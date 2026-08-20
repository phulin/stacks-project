import Mathlib.Algebra.DirectSum.Basic
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.RingTheory.MvPolynomial.Ideal
import Mathlib.RingTheory.FinitePresentation
import Mathlib.RingTheory.FiniteType
import Mathlib.RingTheory.Ideal.Maps
import Mathlib.RingTheory.Ideal.Quotient.Defs
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.RingHom.Etale
import Mathlib.RingTheory.RingHom.Flat

/-!
# Examples, Chapter 37: finite type, not finitely presented, flat at prime

This file records the construction in the section
“Finite type, not finitely presented, flat at prime”.  The algebraic objects
are defined explicitly; the substantive verification lemmas are theorem
interfaces for the proof stage.
-/

noncomputable section

open DirectSum

namespace Formalization.Books.Examples.Unit37

universe u

/-! ## The local base ring and the square-zero extension -/

/-- The two-variable polynomial ring used for the local base. -/
abbrev ftBasePolynomialRing (k : Type u) [Field k] := MvPolynomial (Fin 2) k

/-- The variables `x` and `y` in the base polynomial ring. -/
def ftBaseXVar : Fin 2 := 0

def ftBaseYVar : Fin 2 := 1

def ftBaseX (k : Type u) [Field k] : ftBasePolynomialRing k :=
  MvPolynomial.X ftBaseXVar

def ftBaseY (k : Type u) [Field k] : ftBasePolynomialRing k :=
  MvPolynomial.X ftBaseYVar

/-- The maximal ideal `(x, y)` before localization. -/
def ftBaseMaximalIdeal (k : Type u) [Field k] : Ideal (ftBasePolynomialRing k) :=
  Ideal.span {ftBaseX k, ftBaseY k}

private theorem ftBase_generators_eq_X_image (k : Type u) [Field k] :
    ({ftBaseX k, ftBaseY k} : Set (ftBasePolynomialRing k)) =
      MvPolynomial.X '' ({0, 1} : Set (Fin 2)) := by
  ext p
  constructor
  · intro hp
    have hp' : p = ftBaseX k ∨ p = ftBaseY k := by
      simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hp
    cases hp' with
    | inl h =>
        refine ⟨0, by simp, ?_⟩
        simpa [ftBaseX, ftBaseXVar] using h.symm
    | inr h =>
        refine ⟨1, by simp, ?_⟩
        simpa [ftBaseY, ftBaseYVar] using h.symm
  · intro hp
    cases hp with
    | intro i hi =>
        cases hi with
        | intro hi hpi =>
            have hi' : i = 0 ∨ i = 1 := by
              fin_cases i <;> simp
            have hp' : p = ftBaseX k ∨ p = ftBaseY k := by
              cases hi' with
              | inl hi0 =>
                  left
                  subst i
                  simpa [ftBaseX, ftBaseXVar] using hpi.symm
              | inr hi1 =>
                  right
                  subst i
                  simpa [ftBaseY, ftBaseYVar] using hpi.symm
            simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hp'

private theorem ftBaseMaximalIdeal_eq_constantCoeff_ker (k : Type u) [Field k] :
    ftBaseMaximalIdeal k =
      RingHom.ker (MvPolynomial.constantCoeff : ftBasePolynomialRing k →+* k) := by
  rw [ftBaseMaximalIdeal, ftBase_generators_eq_X_image k]
  apply le_antisymm
  · refine Ideal.span_le.2 ?_
    intro p hp
    cases hp with
    | intro i hi =>
        cases hi with
        | intro hi hpi =>
            rw [← hpi]
            simp
  · intro p hp
    rw [RingHom.mem_ker] at hp
    apply (MvPolynomial.mem_ideal_span_X_image).2
    intro d hd
    have hd0 : d ≠ 0 := by
      intro hzero
      subst d
      have hd' : p.coeff 0 ≠ 0 := by
        simpa [MvPolynomial.mem_support_iff] using hd
      have hp' : p.coeff 0 = 0 := by
        simpa [MvPolynomial.constantCoeff_eq] using hp
      exact hd' hp'
    classical
    by_cases hne : ∃ i, d i ≠ 0
    · cases hne with
      | intro i hi =>
          fin_cases i
          · exact ⟨0, by simp, hi⟩
          · exact ⟨1, by simp, hi⟩
    · exfalso
      apply hd0
      ext i
      exact Classical.not_not.mp (fun hi => hne ⟨i, hi⟩)

/-- The base maximal ideal is prime. -/
instance ftBaseMaximalIdeal_isPrime (k : Type u) [Field k] :
    (ftBaseMaximalIdeal k).IsPrime := by
  rw [ftBaseMaximalIdeal_eq_constantCoeff_ker k]
  exact RingHom.ker_isPrime _

/-- The base maximal ideal is maximal. -/
instance ftBaseMaximalIdeal_isMaximal (k : Type u) [Field k] :
    (ftBaseMaximalIdeal k).IsMaximal := by
  rw [ftBaseMaximalIdeal_eq_constantCoeff_ker k]
  apply RingHom.ker_isMaximal_of_surjective
  intro a
  exact ⟨MvPolynomial.C a, by simp⟩

/-- The local ring `A₀ = k[x, y]_(x,y)`. -/
def ftA0 (k : Type u) [Field k] :=
  Localization.AtPrime (ftBaseMaximalIdeal k)

noncomputable instance ftA0CommRing (k : Type u) [Field k] : CommRing (ftA0 k) := by
  unfold ftA0
  infer_instance

noncomputable instance ftA0Algebra (k : Type u) [Field k] :
    Algebra (ftBasePolynomialRing k) (ftA0 k) := by
  unfold ftA0
  infer_instance

noncomputable instance ftA0IsLocalRing (k : Type u) [Field k] : IsLocalRing (ftA0 k) := by
  unfold ftA0
  infer_instance

abbrev ftAPolynomialRing (k : Type u) [Field k] :=
  MvPolynomial ℕ (ftA0 k)

def ftX (k : Type u) [Field k] : ftA0 k :=
  algebraMap (ftBasePolynomialRing k) (ftA0 k) (ftBaseX k)

def ftY (k : Type u) [Field k] : ftA0 k :=
  algebraMap (ftBasePolynomialRing k) (ftA0 k) (ftBaseY k)

/-- The element `y + x^n + x^(2n+1)` defining the `n`th prime for `n > 0`.

The source construction starts its index at `1`; index `0` would give the
unit `y + 1 + x` in the local ring `A₀`. -/
def ftPrimeEquation (k : Type u) [Field k] (n : ℕ) : ftA0 k :=
  ftY k + (ftX k) ^ n + (ftX k) ^ (2 * n + 1)

/-- The principal ideal `𝔭₀,ₙ = (y + x^n + x^(2n+1))`. -/
def ftP0 (k : Type u) [Field k] (n : ℕ) : Ideal (ftA0 k) :=
  Ideal.span {ftPrimeEquation k n}

theorem ftP0_isPrime (k : Type u) [Field k] (n : ℕ) (hn : 0 < n) :
    (ftP0 k n).IsPrime := by
  sorry

/-- The relations in the square-zero extension before quotienting. -/
def ftARelations (k : Type u) [Field k] : Set (ftAPolynomialRing k) :=
  Set.range (fun p : ℕ × ℕ => MvPolynomial.X p.1 * MvPolynomial.X p.2) ∪
    Set.range (fun n : ℕ =>
      MvPolynomial.X n * MvPolynomial.C (ftPrimeEquation k n))

def ftARelationsIdeal (k : Type u) [Field k] : Ideal (ftAPolynomialRing k) :=
  Ideal.span (ftARelations k)

/-- The ring
`A = A₀[z₁, z₂, …]/(zₙzₘ, zₙ(y+xⁿ+x^(2n+1)))`. -/
def ftA (k : Type u) [Field k] :=
  ftAPolynomialRing k ⧸ ftARelationsIdeal k

noncomputable instance ftACommRing (k : Type u) [Field k] : CommRing (ftA k) := by
  unfold ftA
  infer_instance

noncomputable instance ftAAlgebra (k : Type u) [Field k] : Algebra (ftA0 k) (ftA k) := by
  unfold ftA
  infer_instance

def ftAGenerator (k : Type u) [Field k] (n : ℕ) : ftA k :=
  Ideal.Quotient.mk (ftARelationsIdeal k) (MvPolynomial.X n)

def ftA0ToA (k : Type u) [Field k] : ftA0 k →+* ftA k :=
  algebraMap (ftA0 k) (ftA k)

def ftAX (k : Type u) [Field k] : ftA k :=
  ftA0ToA k (ftX k)

def ftAY (k : Type u) [Field k] : ftA k :=
  ftA0ToA k (ftY k)

def ftAPrimeEquation (k : Type u) [Field k] (n : ℕ) : ftA k :=
  ftA0ToA k (ftPrimeEquation k n)

/-- The augmentation which kills all the `zₙ`. -/
def ftAAugmentation (k : Type u) [Field k] :
    ftAPolynomialRing k →+* ftA0 k :=
  MvPolynomial.eval₂Hom (RingHom.id _) (fun _ => 0)

theorem ftARelations_le_augmentation_ker (k : Type u) [Field k] :
    ftARelationsIdeal k ≤ RingHom.ker (ftAAugmentation k) := by
  simp [ftARelationsIdeal, ftARelations, ftAAugmentation]
  constructor
  · refine Ideal.span_le.2 ?_
    intro p hp
    cases hp with
    | intro q hq =>
        cases q with
        | mk i j =>
            rw [← hq]
            simp
  · refine Ideal.span_le.2 ?_
    intro p hp
    cases hp with
    | intro n hn =>
        rw [← hn]
        simp

/-- The quotient map `A → A₀`. -/
def ftAToA0 (k : Type u) [Field k] : ftA k →+* ftA0 k :=
  Ideal.Quotient.lift (ftARelationsIdeal k) (ftAAugmentation k)
    (fun _ h => ftARelations_le_augmentation_ker k h)

theorem ftAToA0_surjective (k : Type u) [Field k] :
    Function.Surjective (ftAToA0 k) := by
  intro a
  refine ⟨algebraMap (ftA0 k) (ftA k) a, ?_⟩
  have hzero : ∀ x ∈ ftARelationsIdeal k, ftAAugmentation k x = 0 := by
    intro x hx
    exact ftARelations_le_augmentation_ker k hx
  change Ideal.Quotient.lift (ftARelationsIdeal k) (ftAAugmentation k)
      hzero
      (Ideal.Quotient.mk (ftARelationsIdeal k) (MvPolynomial.C a)) = a
  rw [Ideal.Quotient.lift_mk]
  simp [ftAAugmentation]

private theorem ftAAugmentation_eq_zero_mem_idealOfVars (k : Type u) [Field k]
    {p : ftAPolynomialRing k} (hp : ftAAugmentation k p = 0) :
    p ∈ MvPolynomial.idealOfVars ℕ (ftA0 k) := by
  rw [MvPolynomial.idealOfVars, ← Set.image_univ,
    MvPolynomial.mem_ideal_span_X_image]
  intro m hm
  by_cases hm0 : m = 0
  · subst m
    exfalso
    apply (MvPolynomial.mem_support_iff.mp hm)
    have he := MvPolynomial.eval₂Hom_eq_constantCoeff_of_vars
      (RingHom.id (ftA0 k)) (p := p) (fun i hi => rfl)
    have he' : ftAAugmentation k p = MvPolynomial.constantCoeff p := by
      change MvPolynomial.eval₂Hom (RingHom.id _) (fun _ => 0) p = _
      exact he
    have hpc : MvPolynomial.constantCoeff p = 0 := he'.symm.trans hp
    simpa [MvPolynomial.constantCoeff_eq] using hpc
  · have hex : ∃ i, m i ≠ 0 := by
      by_contra h
      push Not at h
      apply hm0
      exact Finsupp.ext fun i => h i
    rcases hex with ⟨i, hi⟩
    exact ⟨i, Set.mem_univ _, hi⟩

private theorem ftARelationsIdeal_contains_idealOfVars_square (k : Type u) [Field k] :
    (MvPolynomial.idealOfVars ℕ (ftA0 k)) ^ 2 ≤ ftARelationsIdeal k := by
  rw [MvPolynomial.idealOfVars, pow_two, Ideal.span_mul_span]
  refine Ideal.span_le.2 ?_
  rintro z ⟨a, ha, b, hb, rfl⟩
  rcases ha with ⟨i, rfl⟩
  rcases hb with ⟨j, rfl⟩
  apply Ideal.subset_span
  exact Set.mem_union_left _ ⟨(i, j), rfl⟩

theorem ftAToA0_kernel_square_zero (k : Type u) [Field k] :
    (RingHom.ker (ftAToA0 k)) ^ 2 = ⊥ := by
  rw [pow_two]
  apply le_antisymm
  · refine Ideal.mul_le.2 ?_
    intro a ha b hb
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective a
    have hp0 : ftAAugmentation k p = 0 := by
      change ftAToA0 k (Ideal.Quotient.mk (ftARelationsIdeal k) p) = 0 at ha
      exact ha
    obtain ⟨q, rfl⟩ := Ideal.Quotient.mk_surjective b
    have hq0 : ftAAugmentation k q = 0 := by
      change ftAToA0 k (Ideal.Quotient.mk (ftARelationsIdeal k) q) = 0 at hb
      exact hb
    have hpI := ftAAugmentation_eq_zero_mem_idealOfVars k hp0
    have hqI := ftAAugmentation_eq_zero_mem_idealOfVars k hq0
    have hpq : p * q ∈ (MvPolynomial.idealOfVars ℕ (ftA0 k)) ^ 2 := by
      rw [pow_two]
      exact Ideal.mul_mem_mul (I := MvPolynomial.idealOfVars ℕ (ftA0 k))
        (J := MvPolynomial.idealOfVars ℕ (ftA0 k)) hpI hqI
    have hpq' := ftARelationsIdeal_contains_idealOfVars_square k hpq
    change Ideal.Quotient.mk (ftARelationsIdeal k) (p * q) = 0
    exact Ideal.Quotient.eq_zero_iff_mem.mpr hpq'
  · exact bot_le

/-- The ideal of `A` corresponding to `𝔭₀,ₙ`, which is prime for `n > 0`. -/
def ftAPrime (k : Type u) [Field k] (n : ℕ) : Ideal (ftA k) :=
  Ideal.comap (ftAToA0 k) (ftP0 k n)

theorem ftAPrime_isPrime (k : Type u) [Field k] (n : ℕ) (hn : 0 < n) :
    (ftAPrime k n).IsPrime := by
  exact (ftP0_isPrime k n hn).comap (ftAToA0 k)

/-- The prime spectra of `A` and `A₀` correspond through the square-zero
extension. -/
theorem ft_primeSpectrum_comap_bijective (k : Type u) [Field k] :
    Function.Bijective (PrimeSpectrum.comap (ftAToA0 k)) := by
  constructor
  · exact PrimeSpectrum.comap_injective_of_surjective (ftAToA0 k)
      (ftAToA0_surjective k)
  · rw [← Set.range_eq_univ,
      range_comap_of_surjective (ftA0 k) (ftAToA0 k) (ftAToA0_surjective k)]
    apply Set.eq_univ_of_forall
    intro p
    change ∀ x, x ∈ RingHom.ker (ftAToA0 k) → x ∈ p.asIdeal
    intro x hx
    have hxx : x * x ∈ RingHom.ker (ftAToA0 k) ^ 2 := by
      rw [pow_two]
      exact Ideal.mul_mem_mul (I := RingHom.ker (ftAToA0 k))
        (J := RingHom.ker (ftAToA0 k)) hx hx
    rw [ftAToA0_kernel_square_zero k] at hxx
    have hzero : x * x = 0 := Ideal.mem_bot.mp hxx
    exact (p.isPrime.mem_or_mem (hzero ▸ p.asIdeal.zero_mem)).elim id id

instance ftA_isLocalRing (k : Type u) [Field k] : IsLocalRing (ftA k) := by
  have hker_le : ∀ (I : Ideal (ftA k)), I.IsMaximal →
      RingHom.ker (ftAToA0 k) ≤ I := by
    intro I hI x hx
    have hxx : x * x ∈ RingHom.ker (ftAToA0 k) ^ 2 := by
      rw [pow_two]
      exact Ideal.mul_mem_mul (I := RingHom.ker (ftAToA0 k))
        (J := RingHom.ker (ftAToA0 k)) hx hx
    rw [ftAToA0_kernel_square_zero k] at hxx
    have hzero : x * x = 0 := Ideal.mem_bot.mp hxx
    exact (hI.isPrime.mem_or_mem (hzero ▸ I.zero_mem)).elim id id
  refine IsLocalRing.of_unique_max_ideal ?_
  refine ⟨(IsLocalRing.maximalIdeal (ftA0 k)).comap (ftAToA0 k),
    Ideal.comap_isMaximal_of_surjective (ftAToA0 k) (ftAToA0_surjective k), ?_⟩
  intro I hI
  have hk := hker_le I hI
  have hmap : (I.map (ftAToA0 k)).IsMaximal :=
    @Ideal.IsMaximal.map_of_surjective_of_ker_le
      (ftA k) (ftA0 k) (ftA k →+* ftA0 k) _ _ _ _
      (ftAToA0 k) (ftAToA0_surjective k) I hI hk
  have hmap_eq : I.map (ftAToA0 k) = IsLocalRing.maximalIdeal (ftA0 k) :=
    IsLocalRing.eq_maximalIdeal hmap
  have hcomp : (I.map (ftAToA0 k)).comap (ftAToA0 k) =
      I ⊔ RingHom.ker (ftAToA0 k) := by
    rw [Ideal.comap_map_of_surjective (ftAToA0 k) (ftAToA0_surjective k) I,
      RingHom.ker_eq_comap_bot]
  calc
    I = I ⊔ RingHom.ker (ftAToA0 k) := (sup_eq_left.mpr hk).symm
    _ = (I.map (ftAToA0 k)).comap (ftAToA0 k) := hcomp.symm
    _ = (IsLocalRing.maximalIdeal (ftA0 k)).comap (ftAToA0 k) := by rw [hmap_eq]

theorem ftAGenerator_annihilator (k : Type u) [Field k] (n : ℕ) :
    (Submodule.span (ftA k) ({ftAGenerator k n} : Set (ftA k))).annihilator =
      ftAPrime k n := by
  sorry

/-! ## The standard-étale algebra `C` -/

/-- The polynomial relation `xz² + z + y`. -/
def ftCRelation (k : Type u) [Field k] : Polynomial (ftA k) :=
  Polynomial.C (ftAX k) * Polynomial.X ^ 2 + Polynomial.X + Polynomial.C (ftAY k)

def ftCRelationsIdeal (k : Type u) [Field k] : Ideal (Polynomial (ftA k)) :=
  Ideal.span {ftCRelation k}

def ftCQuotient (k : Type u) [Field k] :=
  Polynomial (ftA k) ⧸ ftCRelationsIdeal k

noncomputable instance ftCQuotientCommRing (k : Type u) [Field k] :
    CommRing (ftCQuotient k) := by
  unfold ftCQuotient
  infer_instance

noncomputable instance ftCQuotientAlgebra (k : Type u) [Field k] :
    Algebra (ftA k) (ftCQuotient k) := by
  unfold ftCQuotient
  infer_instance

def ftCDerivativePolynomial (k : Type u) [Field k] : Polynomial (ftA k) :=
  Polynomial.C (2 * ftAX k) * Polynomial.X + 1

def ftCDerivative (k : Type u) [Field k] : ftCQuotient k :=
  Ideal.Quotient.mk (ftCRelationsIdeal k) (ftCDerivativePolynomial k)

/-- The ring
`C = A[z]/(xz²+z+y)[1/(2zx+1)]`. -/
def ftC (k : Type u) [Field k] :=
  Localization.Away (ftCDerivative k)

noncomputable instance ftCCommRing (k : Type u) [Field k] : CommRing (ftC k) := by
  unfold ftC
  infer_instance

noncomputable instance ftCQuotientToCAlgebra (k : Type u) [Field k] :
    Algebra (ftCQuotient k) (ftC k) := by
  unfold ftC
  infer_instance

noncomputable instance ftAToCAlgebra (k : Type u) [Field k] : Algebra (ftA k) (ftC k) := by
  unfold ftC
  infer_instance

def ftAToC (k : Type u) [Field k] : ftA k →+* ftC k :=
  algebraMap (ftA k) (ftC k)

def ftCZ (k : Type u) [Field k] : ftC k :=
  algebraMap (ftCQuotient k) (ftC k)
    (Ideal.Quotient.mk (ftCRelationsIdeal k) Polynomial.X)

def ftCX (k : Type u) [Field k] : ftC k :=
  ftAToC k (ftAX k)

def ftCY (k : Type u) [Field k] : ftC k :=
  ftAToC k (ftAY k)

def ftCZn (k : Type u) [Field k] (n : ℕ) : ftC k :=
  ftAToC k (ftAGenerator k n)

theorem ftAToC_etale (k : Type u) [Field k] :
    RingHom.Etale (ftAToC k) := by
  sorry

theorem ftAToC_finiteType (k : Type u) [Field k] :
    RingHom.FiniteType (ftAToC k) := by
  sorry

theorem ftAToC_flat (k : Type u) [Field k] :
    RingHom.Flat (ftAToC k) := by
  sorry

/-- The maximal ideal generated by `x`, `y`, `z`, and all `zₙ`. -/
def ftCQ (k : Type u) [Field k] : Ideal (ftC k) :=
  Ideal.span (({ftCX k, ftCY k, ftCZ k} : Set (ftC k)) ∪ Set.range (ftCZn k))

instance ftCQ_isMaximal (k : Type u) [Field k] :
    (ftCQ k).IsMaximal := by
  sorry

instance ftCQ_isPrime (k : Type u) [Field k] :
    (ftCQ k).IsPrime := by
  sorry

def ftCPrimeIdeal (k : Type u) [Field k] (n : ℕ) : Ideal (ftC k) :=
  Ideal.map (ftAToC k) (ftAPrime k n)

theorem ftCZn_annihilator (k : Type u) [Field k] (n : ℕ) :
    (Submodule.span (ftC k) ({ftCZn k n} : Set (ftC k))).annihilator =
      ftCPrimeIdeal k n := by
  sorry

/-! ## The fibre computation -/

abbrev ftCPrimeFibre (k : Type u) [Field k] (n : ℕ) :=
  ftC k ⧸ ftCPrimeIdeal k n

def ftCRelationOverA0 (k : Type u) [Field k] : Polynomial (ftA0 k) :=
  Polynomial.C (ftX k) * Polynomial.X ^ 2 + Polynomial.X + Polynomial.C (ftY k)

abbrev ftCPrimePresentationBase (k : Type u) [Field k] (n : ℕ) :=
  Polynomial (ftA0 k) ⧸
    (Ideal.span {ftCRelationOverA0 k, Polynomial.C (ftPrimeEquation k n)})

def ftCPrimePresentationDerivative (k : Type u) [Field k] (n : ℕ) :
    ftCPrimePresentationBase k n :=
  Ideal.Quotient.mk _ (Polynomial.C (2 * ftX k) * Polynomial.X + 1)

abbrev ftCPrimePresentation (k : Type u) [Field k] (n : ℕ) :=
  Localization.Away (ftCPrimePresentationDerivative k n)

def ftKXMaximalIdeal (k : Type u) [Field k] : Ideal (Polynomial k) :=
  Ideal.span {(Polynomial.X : Polynomial k)}

instance ftKXMaximalIdeal_isPrime (k : Type u) [Field k] :
    (ftKXMaximalIdeal k).IsPrime := by
  sorry

instance ftKXMaximalIdeal_isMaximal (k : Type u) [Field k] :
    (ftKXMaximalIdeal k).IsMaximal := by
  sorry

abbrev ftKXLocal (k : Type u) [Field k] :=
  Localization.AtPrime (ftKXMaximalIdeal k)

noncomputable instance ftKXLocalCommRing (k : Type u) [Field k] :
    CommRing (ftKXLocal k) := by
  unfold ftKXLocal
  infer_instance

def ftKX (k : Type u) [Field k] : ftKXLocal k :=
  algebraMap (Polynomial k) (ftKXLocal k) Polynomial.X

def ftSecondRelationPolynomial (k : Type u) [Field k] (n : ℕ) :
    Polynomial (ftKXLocal k) :=
  Polynomial.C (ftKX k) * Polynomial.X ^ 2 + Polynomial.X -
    Polynomial.C (ftKX k ^ n + ftKX k ^ (2 * n + 1))

def ftSecondDerivative (k : Type u) [Field k] : Polynomial (ftKXLocal k) :=
  Polynomial.C (2 * ftKX k) * Polynomial.X + 1

abbrev ftSecondBase (k : Type u) [Field k] (n : ℕ) :=
  Polynomial (ftKXLocal k) ⧸
    (Ideal.span {ftSecondRelationPolynomial k n})

def ftSecondDerivativeQuotient (k : Type u) [Field k] (n : ℕ) :
    ftSecondBase k n :=
  Ideal.Quotient.mk _ (ftSecondDerivative k)

abbrev ftSecondPresentation (k : Type u) [Field k] (n : ℕ) :=
  Localization.Away (ftSecondDerivativeQuotient k n)

def ftSecondLeftRelation (k : Type u) [Field k] (n : ℕ) :
    Polynomial (ftKXLocal k) :=
  Polynomial.X - Polynomial.C (ftKX k ^ n)

abbrev ftSecondLeft (k : Type u) [Field k] (n : ℕ) :=
  Polynomial (ftKXLocal k) ⧸ (Ideal.span {ftSecondLeftRelation k n})

def ftSecondRightRelation (k : Type u) [Field k] (n : ℕ) :
    Polynomial (ftKXLocal k) :=
  Polynomial.C (ftKX k) * Polynomial.X +
    Polynomial.C (ftKX k ^ (n + 1) + 1)

abbrev ftSecondRightBase (k : Type u) [Field k] (n : ℕ) :=
  Polynomial (ftKXLocal k) ⧸
    (Ideal.span {ftSecondRightRelation k n})

def ftSecondRightDerivative (k : Type u) [Field k] (n : ℕ) :
    ftSecondRightBase k n :=
  Ideal.Quotient.mk _ (ftSecondDerivative k)

abbrev ftSecondRight (k : Type u) [Field k] (n : ℕ) :=
  Localization.Away (ftSecondRightDerivative k n)

abbrev ftSecondProduct (k : Type u) [Field k] (n : ℕ) :=
  ftSecondLeft k n × ftSecondRight k n

abbrev ftRationalFunctionField (k : Type u) [Field k] :=
  FractionRing (Polynomial k)

abbrev ftFinalProduct (k : Type u) [Field k] :=
  ftKXLocal k × ftRationalFunctionField k

theorem ftCPrimeFibre_equiv_first_presentation (k : Type u) [Field k] (n : ℕ) :
    Nonempty (ftCPrimeFibre k n ≃+* ftCPrimePresentation k n) := by
  sorry

theorem ftCPrimePresentation_equiv_second_presentation (k : Type u) [Field k]
    (n : ℕ) (hn : 0 < n) :
    Nonempty (ftCPrimePresentation k n ≃+* ftSecondPresentation k n) := by
  sorry

theorem ftFibre_factorization (k : Type u) [Field k] (n : ℕ) :
    (Polynomial.X - Polynomial.C (ftKX k ^ n)) *
        (Polynomial.C (ftKX k) * Polynomial.X +
          Polynomial.C (ftKX k ^ (n + 1) + 1)) =
      ftSecondRelationPolynomial k n := by
  sorry

theorem ftSecondPresentation_equiv_product (k : Type u) [Field k] (n : ℕ) :
    Nonempty (ftSecondPresentation k n ≃+* ftSecondProduct k n) := by
  sorry

theorem ftSecondProduct_equiv_final_product (k : Type u) [Field k] (n : ℕ) :
    Nonempty (ftSecondProduct k n ≃+* ftFinalProduct k) := by
  sorry

/-! ## The two ideals over `𝔭ₙ` -/

def ftCRPrimeIdeal (k : Type u) [Field k] (n : ℕ) : Ideal (ftC k) :=
  ftCPrimeIdeal k n ⊔ Ideal.span {ftCZ k - (ftCX k) ^ n}

def ftCQPrimeIdeal (k : Type u) [Field k] (n : ℕ) : Ideal (ftC k) :=
  ftCPrimeIdeal k n ⊔
    Ideal.span {ftCX k * ftCZ k + (ftCX k) ^ (n + 1) + 1}

theorem ftCQPrimeIdeal_isMaximal (k : Type u) [Field k] (n : ℕ) (hn : 0 < n) :
    (ftCQPrimeIdeal k n).IsMaximal := by
  sorry

def ftXi (k : Type u) [Field k] (n : ℕ) : ftC k :=
  (ftCZ k - (ftCX k) ^ n) * ftCZn k n

theorem ftCPrimeIdeal_eq_inf (k : Type u) [Field k] (n : ℕ) :
    ftCPrimeIdeal k n = ftCRPrimeIdeal k n ⊓ ftCQPrimeIdeal k n := by
  sorry

theorem ftCRPrimeIdeal_sup_CQPrimeIdeal (k : Type u) [Field k] (n : ℕ) :
    ftCRPrimeIdeal k n ⊔ ftCQPrimeIdeal k n = ⊤ := by
  sorry

theorem ftCPrimeIdeal_eq_mul (k : Type u) [Field k] (n : ℕ) :
    ftCPrimeIdeal k n = ftCRPrimeIdeal k n * ftCQPrimeIdeal k n := by
  sorry

theorem ftCQPrimeIdeal_annihilator_Xi (k : Type u) [Field k] (n : ℕ) :
    (Submodule.span (ftC k) ({ftXi k n} : Set (ftC k))).annihilator =
      ftCQPrimeIdeal k n := by
  sorry

theorem ftCRPrimeIdeal_le_CQ (k : Type u) [Field k] (n : ℕ) (hn : 0 < n) :
    ftCRPrimeIdeal k n ≤ ftCQ k := by
  sorry

theorem ftCQPrimeIdeal_sup_CQ (k : Type u) [Field k] (n : ℕ) :
    ftCQPrimeIdeal k n ⊔ ftCQ k = ⊤ := by
  sorry

theorem ftCQPrimeIdeal_sup_CQPrimeIdeal (k : Type u) [Field k] {n m : ℕ}
    (hnm : n ≠ m) :
    ftCQPrimeIdeal k n ⊔ ftCQPrimeIdeal k m = ⊤ := by
  sorry

theorem ftCQPrimeIdeal_mul_Xi (k : Type u) [Field k] (n : ℕ) {r : ftC k}
    (hr : r ∈ ftCQPrimeIdeal k n) : r * ftXi k n = 0 := by
  sorry

/-! ## The image algebra `B` -/

def ftCAtQ (k : Type u) [Field k] :=
  Localization.AtPrime (ftCQ k)

noncomputable instance ftCAtQCommRing (k : Type u) [Field k] : CommRing (ftCAtQ k) := by
  unfold ftCAtQ
  infer_instance

noncomputable instance ftCAtQAlgebra (k : Type u) [Field k] : Algebra (ftC k) (ftCAtQ k) := by
  unfold ftCAtQ
  infer_instance

noncomputable instance ftCAtQIsLocalRing (k : Type u) [Field k] : IsLocalRing (ftCAtQ k) := by
  unfold ftCAtQ
  infer_instance

def ftCToCAtQ (k : Type u) [Field k] : ftC k →+* ftCAtQ k :=
  algebraMap (ftC k) (ftCAtQ k)

/-- `B = Im(C → C_𝔮)`, represented by Mathlib's canonical range subring. -/
def ftB (k : Type u) [Field k] :=
  RingHom.range (ftCToCAtQ k)

noncomputable instance ftBCommRing (k : Type u) [Field k] : CommRing (ftB k) := by
  unfold ftB
  infer_instance

def ftCToB (k : Type u) [Field k] : ftC k →+* ftB k :=
  (ftCToCAtQ k).rangeRestrict

theorem ftCToB_Xi (k : Type u) [Field k] (n : ℕ) :
    ftCToB k (ftXi k n) = 0 := by
  sorry

def ftAToB (k : Type u) [Field k] : ftA k →+* ftB k :=
  (ftCToB k).comp (ftAToC k)

instance ftB_algebra (k : Type u) [Field k] : Algebra (ftA k) (ftB k) :=
  (ftAToB k).toAlgebra

def ftBQPrime (k : Type u) [Field k] : Ideal (ftB k) :=
  Ideal.map (ftCToB k) (ftCQ k)

instance ftBQPrime_isPrime (k : Type u) [Field k] :
    (ftBQPrime k).IsPrime := by
  sorry

theorem ftB_finiteType (k : Type u) [Field k] :
    RingHom.FiniteType (ftAToB k) := by
  sorry

theorem ftB_localization_equiv (k : Type u) [Field k] :
    Nonempty (Localization.AtPrime (ftBQPrime k) ≃+* ftCAtQ k) := by
  sorry

def ftAToBLocal (k : Type u) [Field k] (g : ftB k) :
    ftA k →+* Localization.Away g :=
  (algebraMap (ftB k) (Localization.Away g)).comp (ftAToB k)

def ftAToBQ (k : Type u) [Field k] :
    ftA k →+* Localization.AtPrime (ftBQPrime k) :=
  (algebraMap (ftB k) (Localization.AtPrime (ftBQPrime k))).comp (ftAToB k)

theorem ftB_localization_at_prime_flat (k : Type u) [Field k] :
    RingHom.Flat (ftAToBQ k) := by
  sorry

theorem ftBQPrime_lies_over_maximal (k : Type u) [Field k] :
    Ideal.comap (ftAToB k) (ftBQPrime k) = IsLocalRing.maximalIdeal (ftA k) := by
  sorry

def ftBGenerator (k : Type u) [Field k] (n : ℕ) : ftB k :=
  ftCToB k (ftCZn k n)

def ftBX (k : Type u) [Field k] : ftB k :=
  ftCToB k (ftCX k)

def ftBLocalGenerator (k : Type u) [Field k] (g : ftB k) (n : ℕ) :
    Localization.Away g :=
  algebraMap (ftB k) (Localization.Away g) (ftBGenerator k n)

def ftBLocalPrime (k : Type u) [Field k] (g : ftB k) (n : ℕ) :
    Ideal (Localization.Away g) :=
  Ideal.map (ftAToBLocal k g) (ftAPrime k n)

def ftBLocalDifference (k : Type u) [Field k] (g : ftB k) (n : ℕ) :
    Localization.Away g :=
  algebraMap (ftB k) (Localization.Away g)
    (ftCToB k (ftCZ k) - (ftBX k) ^ n)

theorem ftB_local_annihilator_under_flat (k : Type u) [Field k] (g : ftB k)
    (hg : g ∉ ftBQPrime k) (n : ℕ)
    (hflat : RingHom.Flat (ftAToBLocal k g)) :
    (Submodule.span (Localization.Away g) ({ftBLocalGenerator k g n} :
      Set (Localization.Away g))).annihilator = ftBLocalPrime k g n := by
  sorry

theorem ftB_local_difference_not_mem_prime (k : Type u) [Field k] (g : ftC k)
    (hg : g ∉ ftCQ k) (n : ℕ) (hgn : g ∉ ftCQPrimeIdeal k n) :
    ftBLocalDifference k (ftCToB k g) n ∉
      ftBLocalPrime k (ftCToB k g) n := by
  sorry

/-! ## The kernel calculation behind non-finite-presentation -/

abbrev ftKernelIndex (k : Type u) [Field k] (g : ftC k) :=
  {n : ℕ // g ∉ ftCQPrimeIdeal k n}

abbrev ftKernelSummand (k : Type u) [Field k] (g : ftC k)
    (n : ftKernelIndex k g) :=
  ftC k ⧸ ftCQPrimeIdeal k n.1

abbrev ftKernelDirectSum (k : Type u) [Field k] (g : ftC k) :=
  ⨁ n : ftKernelIndex k g, ftKernelSummand k g n

def ftQuotientMulAddHom {R S : Type u} [CommRing R] [CommRing S]
    (I : Ideal R) (f : R →+* S) (s : S)
    (h : ∀ r : R, r ∈ I → f r * s = 0) : (R ⧸ I) →+ S :=
  QuotientAddGroup.lift I.toAddSubgroup
    ((AddMonoidHom.mulRight s).comp f.toAddMonoidHom)
    (fun r hr => h r hr)

def ftCPrimeSummandMap (k : Type u) [Field k] (g : ftC k)
    (n : ftKernelIndex k g) : ftKernelSummand k g n →+
      Localization.Away g :=
  ftQuotientMulAddHom (ftCQPrimeIdeal k n.1)
    (algebraMap (ftC k) (Localization.Away g))
    (algebraMap (ftC k) (Localization.Away g) (ftXi k n.1))
    (by
      intro r hr
      rw [← map_mul, ftCQPrimeIdeal_mul_Xi k n.1 hr, map_zero])

def ftKernelMap (k : Type u) [Field k] (g : ftC k) :
    ftKernelDirectSum k g →+ Localization.Away g :=
  by
    classical
    exact DirectSum.toAddMonoid (fun n => ftCPrimeSummandMap k g n)

def ftCLocalizationMap (k : Type u) [Field k] (g : ftC k) :
    Localization.Away g →+* Localization.Away (ftCToB k g) :=
  Localization.awayMap (ftCToB k) g

theorem ftKernelMap_on_summand (k : Type u) [Field k] (g : ftC k)
    (n : ftKernelIndex k g) (c : ftKernelSummand k g n) :
    ftKernelMap k g (DirectSum.of _ n c) = ftCPrimeSummandMap k g n c := by
  classical
  change DirectSum.toAddMonoid (fun n => ftCPrimeSummandMap k g n)
      (DirectSum.of _ n c) = ftCPrimeSummandMap k g n c
  exact DirectSum.toAddMonoid_of (fun n => ftCPrimeSummandMap k g n) n c

theorem ftCQPrime_contains_only_finitely_many (k : Type u) [Field k] (g : ftC k)
    (hg : g ∉ ftCQ k) :
    {n : ℕ | g ∈ ftCQPrimeIdeal k n}.Finite := by
  sorry

theorem ftKernelMap_injective (k : Type u) [Field k] (g : ftC k)
    (hg : g ∉ ftCQ k) :
    Function.Injective (ftKernelMap k g) := by
  sorry

theorem ftKernelMap_range_eq_kernel (k : Type u) [Field k] (g : ftC k)
    (hg : g ∉ ftCQ k) :
    Set.range (ftKernelMap k g) =
      (RingHom.ker (ftCLocalizationMap k g) : Set (Localization.Away g)) := by
  sorry

theorem ftB_local_finitePresentation_iff_kernel_fg (k : Type u) [Field k]
    (g : ftC k) :
    RingHom.FinitePresentation (ftAToBLocal k (ftCToB k g)) ↔
      (RingHom.ker (ftCLocalizationMap k g)).FG := by
  sorry

theorem ftB_local_not_finitePresentation (k : Type u) [Field k] (g : ftB k)
    (hg : g ∉ ftBQPrime k) :
    ¬ RingHom.FinitePresentation (ftAToBLocal k g) := by
  sorry

theorem ftB_local_not_flat (k : Type u) [Field k] (g : ftB k)
    (hg : g ∉ ftBQPrime k) :
    ¬ RingHom.Flat (ftAToBLocal k g) := by
  sorry

/-! ## The chapter's final existence statement -/

theorem ft_raynaud_gruson_example :
    ∃ (k : Type u) (_ : Field k),
      IsLocalRing (ftA k) ∧
        RingHom.FiniteType (ftAToB k) ∧
        ∃ q : Ideal (ftB k),
          q.IsPrime ∧
            q = ftBQPrime k ∧
            Ideal.comap (ftAToB k) q = IsLocalRing.maximalIdeal (ftA k) ∧
            RingHom.Flat (ftAToBQ k) ∧
            ∀ g : ftB k, g ∉ q →
              ¬ RingHom.FinitePresentation (ftAToBLocal k g) ∧
                ¬ RingHom.Flat (ftAToBLocal k g) := by
  sorry

end Formalization.Books.Examples.Unit37
