import Mathlib.Algebra.DirectSum.Basic
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.Algebra.TrivSqZeroExt.Basic
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
import Mathlib.RingTheory.Smooth.StandardSmoothCotangent

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

private noncomputable def ftAGeneratorTestMap (k : Type u) [Field k] (n : ℕ) :
    ftAPolynomialRing k →+*
      TrivSqZeroExt (ftA0 k ⧸ ftP0 k n) (ftA0 k ⧸ ftP0 k n) :=
  MvPolynomial.eval₂Hom
    ((TrivSqZeroExt.inlHom _ _).comp (Ideal.Quotient.mk (ftP0 k n)))
    (fun i => if i = n then TrivSqZeroExt.inr 1 else 0)

private theorem ftARelations_le_testMap_ker (k : Type u) [Field k] (n : ℕ) :
    ftARelationsIdeal k ≤ RingHom.ker (ftAGeneratorTestMap k n) := by
  refine Ideal.span_le.2 ?_
  intro p hp
  rcases hp with hp | hp
  · rcases hp with ⟨⟨i, j⟩, rfl⟩
    simp [ftAGeneratorTestMap, apply_ite, TrivSqZeroExt.inr_mul_inr]
  · rcases hp with ⟨i, rfl⟩
    change ftAGeneratorTestMap k n
        (MvPolynomial.X i * MvPolynomial.C (ftPrimeEquation k i)) = 0
    calc
      _ = ftAGeneratorTestMap k n (MvPolynomial.X i) *
          ftAGeneratorTestMap k n (MvPolynomial.C (ftPrimeEquation k i)) :=
        (ftAGeneratorTestMap k n).map_mul _ _
      _ = (if i = n then TrivSqZeroExt.inr 1 else 0) *
          TrivSqZeroExt.inl (Ideal.Quotient.mk (ftP0 k n) (ftPrimeEquation k i)) := by
        simp [ftAGeneratorTestMap]
      _ = 0 := by
        by_cases hi : i = n
        · subst i
          have hqzero : Ideal.Quotient.mk (ftP0 k n) (ftPrimeEquation k n) = 0 :=
            Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self _)
          rw [if_pos rfl, hqzero]
          simp
        · simp [hi]

private noncomputable def ftAGeneratorTestMapQuotient (k : Type u) [Field k] (n : ℕ) :
    ftA k →+* TrivSqZeroExt (ftA0 k ⧸ ftP0 k n) (ftA0 k ⧸ ftP0 k n) :=
  Ideal.Quotient.lift (ftARelationsIdeal k) (ftAGeneratorTestMap k n)
    (ftARelations_le_testMap_ker k n)

private theorem ftAGeneratorTestMap_fst (k : Type u) [Field k] (n : ℕ)
    (p : ftAPolynomialRing k) :
    TrivSqZeroExt.fst (ftAGeneratorTestMap k n p) =
      Ideal.Quotient.mk (ftP0 k n) (ftAAugmentation k p) := by
  have hhom :
      (TrivSqZeroExt.fstHom
        (ftA0 k ⧸ ftP0 k n) (ftA0 k ⧸ ftP0 k n) (ftA0 k ⧸ ftP0 k n)).toRingHom.comp
          (ftAGeneratorTestMap k n) =
        (Ideal.Quotient.mk (ftP0 k n)).comp (ftAAugmentation k) := by
    apply MvPolynomial.ringHom_ext'
    · ext a
      change TrivSqZeroExt.fst (ftAGeneratorTestMap k n (MvPolynomial.C a)) =
        Ideal.Quotient.mk (ftP0 k n) (ftAAugmentation k (MvPolynomial.C a))
      rw [show ftAGeneratorTestMap k n (MvPolynomial.C a) =
          (TrivSqZeroExt.inlHom _ _)
            (Ideal.Quotient.mk (ftP0 k n) a) by
          simp [ftAGeneratorTestMap]]
      change Ideal.Quotient.mk (ftP0 k n) a =
        Ideal.Quotient.mk (ftP0 k n) (ftAAugmentation k (MvPolynomial.C a))
      simp only [ftAAugmentation, MvPolynomial.eval₂Hom_C, RingHom.id_apply]
    · intro i
      change TrivSqZeroExt.fst (ftAGeneratorTestMap k n (MvPolynomial.X i)) =
        (Ideal.Quotient.mk (ftP0 k n)) (ftAAugmentation k (MvPolynomial.X i))
      simp only [ftAGeneratorTestMap, ftAAugmentation]
      by_cases hi : i = n
      · simp [hi]
      · simp [hi]
  exact DFunLike.congr_fun hhom p

theorem ftAGenerator_annihilator (k : Type u) [Field k] (n : ℕ) :
    (Submodule.span (ftA k) ({ftAGenerator k n} : Set (ftA k))).annihilator =
      ftAPrime k n := by
  rw [Submodule.annihilator_span_singleton]
  ext x
  simp [LinearMap.toSpanSingleton_apply, ftAPrime]
  constructor
  · intro hx
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
    have hzero := congrArg (ftAGeneratorTestMapQuotient k n) hx
    have hsnd := congrArg TrivSqZeroExt.snd hzero
    have hconst : Ideal.Quotient.mk (ftP0 k n) (ftAAugmentation k p) = 0 := by
      have hsnd' := hsnd
      have hmapprod := (ftAGeneratorTestMapQuotient k n).map_mul
        (Ideal.Quotient.mk (ftARelationsIdeal k) p) (ftAGenerator k n)
      rw [hmapprod] at hsnd'
      simp only [ftAGeneratorTestMapQuotient, ftAGenerator] at hsnd'
      change TrivSqZeroExt.snd
          (ftAGeneratorTestMap k n p * ftAGeneratorTestMap k n (MvPolynomial.X n)) = 0 at hsnd'
      have hXmap : ftAGeneratorTestMap k n (MvPolynomial.X n) =
          TrivSqZeroExt.inr 1 := by
        simp [ftAGeneratorTestMap]
      rw [hXmap, TrivSqZeroExt.snd_mul] at hsnd'
      have hfstzero : TrivSqZeroExt.fst (ftAGeneratorTestMap k n p) = 0 := by
        simpa using hsnd'
      calc
        _ = TrivSqZeroExt.fst (ftAGeneratorTestMap k n p) :=
          (ftAGeneratorTestMap_fst k n p).symm
        _ = 0 := hfstzero
    have hp0 : ftAAugmentation k p ∈ ftP0 k n :=
      Ideal.Quotient.eq_zero_iff_mem.mp hconst
    have hmap : ftAToA0 k (Ideal.Quotient.mk (ftARelationsIdeal k) p) =
        ftAAugmentation k p := by
      change Ideal.Quotient.lift (ftARelationsIdeal k) (ftAAugmentation k) _
          (Ideal.Quotient.mk (ftARelationsIdeal k) p) = _
      rfl
    exact hmap.symm ▸ hp0
  · intro hx
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
    have hmap : ftAToA0 k (Ideal.Quotient.mk (ftARelationsIdeal k) p) =
        ftAAugmentation k p := by
      change Ideal.Quotient.lift (ftARelationsIdeal k) (ftAAugmentation k) _
          (Ideal.Quotient.mk (ftARelationsIdeal k) p) = _
      rfl
    have hp0 : ftAAugmentation k p ∈ ftP0 k n := by
      exact hmap ▸ hx
    have hpv : p - MvPolynomial.C (ftAAugmentation k p) ∈
        MvPolynomial.idealOfVars ℕ (ftA0 k) := by
      apply ftAAugmentation_eq_zero_mem_idealOfVars k
      simp [ftAAugmentation]
    have hX : MvPolynomial.X n ∈ MvPolynomial.idealOfVars ℕ (ftA0 k) := by
      apply Ideal.subset_span
      exact ⟨n, rfl⟩
    have hvar : (p - MvPolynomial.C (ftAAugmentation k p)) * MvPolynomial.X n ∈
        ftARelationsIdeal k :=
      ftARelationsIdeal_contains_idealOfVars_square k
        (by
          simpa only [pow_two] using
            (Ideal.mul_mem_mul
              (I := MvPolynomial.idealOfVars ℕ (ftA0 k))
              (J := MvPolynomial.idealOfVars ℕ (ftA0 k)) hpv hX))
    obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.mp hp0
    have hq : MvPolynomial.C (ftAAugmentation k p) * MvPolynomial.X n ∈
        ftARelationsIdeal k := by
      rw [← ha, MvPolynomial.C_mul]
      simpa [mul_assoc, mul_comm, mul_left_comm] using
        (ftARelationsIdeal k).mul_mem_left (MvPolynomial.C a)
          (Ideal.subset_span (Set.mem_union_right _ ⟨n, rfl⟩))
    change Ideal.Quotient.mk (ftARelationsIdeal k) (p * MvPolynomial.X n) = 0
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    simpa [sub_mul, add_comm, add_left_comm, add_assoc] using
      (ftARelationsIdeal k).add_mem hvar hq

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

private noncomputable instance ftA_self_finiteType (k : Type u) [Field k] :
    Algebra.FiniteType (ftA k) (ftA k) :=
  (RingHom.finiteType_algebraMap (A := ftA k) (B := ftA k)).mp <|
    by simpa using (RingHom.FiniteType.id (ftA k))

private noncomputable instance ftCQuotient_self_finiteType (k : Type u) [Field k] :
    Algebra.FiniteType (ftCQuotient k) (ftCQuotient k) :=
  (RingHom.finiteType_algebraMap (A := ftCQuotient k) (B := ftCQuotient k)).mp <|
    by simpa using (RingHom.FiniteType.id (ftCQuotient k))

private noncomputable instance ftA_ftC_scalarTower (k : Type u) [Field k] :
    IsScalarTower (ftA k) (ftCQuotient k) (ftC k) :=
  IsScalarTower.of_algebraMap_eq fun x => by rfl

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

private def ftCQuotientRelation (k : Type u) [Field k] :
    PUnit.{u + 1} → MvPolynomial PUnit.{u + 1} (ftA k) :=
  fun _ => Polynomial.toMvPolynomial PUnit.unit (ftCRelation k)

private theorem ftCQuotient_map_span (k : Type u) [Field k] :
    ftCRelationsIdeal k =
      Ideal.map
        (MvPolynomial.uniqueAlgEquiv (ftA k) PUnit :
          MvPolynomial PUnit.{u + 1} (ftA k) →+* Polynomial (ftA k))
        (Ideal.span (Set.range (ftCQuotientRelation k))) := by
  rw [Ideal.map_span]
  have hrange : Set.range (ftCQuotientRelation k) =
      {ftCQuotientRelation k (PUnit.unit : PUnit.{u + 1})} := by
    ext p
    simp only [Set.mem_range, Set.mem_singleton_iff]
    constructor
    · rintro ⟨x, hx⟩
      simpa [ftCQuotientRelation] using hx.symm
    · intro hp
      refine ⟨PUnit.unit, ?_⟩
      simpa [ftCQuotientRelation] using hp.symm
  rw [hrange]
  simp only [Set.image_singleton]
  simp [ftCRelationsIdeal, ftCQuotientRelation, ftCRelation]

private noncomputable def ftCQuotientEquiv (k : Type u) [Field k] :
    (MvPolynomial PUnit.{u + 1} (ftA k) ⧸
        Ideal.span (Set.range (ftCQuotientRelation k))) ≃ₐ[ftA k] ftCQuotient k := by
  exact Ideal.quotientEquivAlg _ _ (MvPolynomial.uniqueAlgEquiv (ftA k) PUnit)
    (ftCQuotient_map_span k)

private noncomputable def ftCQuotientPrePresentation (k : Type u) [Field k] :
    Algebra.PreSubmersivePresentation (ftA k) (ftCQuotient k)
      PUnit.{u + 1} PUnit.{u + 1} :=
  (Algebra.PreSubmersivePresentation.naive
      (v := ftCQuotientRelation k) (fun _ : PUnit => PUnit.unit) (fun _ _ h => h)).ofAlgEquiv
    (ftCQuotientEquiv k)

private theorem ftCQuotientPrePresentation_jacobian (k : Type u) [Field k] :
    (ftCQuotientPrePresentation k).jacobian = ftCDerivative k := by
  unfold ftCQuotientPrePresentation
  rw [Algebra.PreSubmersivePresentation.jacobian_eq_jacobiMatrix_det]
  rw [Algebra.PreSubmersivePresentation.jacobiMatrix_ofAlgEquiv]
  simp
  rw [Algebra.PreSubmersivePresentation.jacobiMatrix_apply]
  simp [Algebra.PreSubmersivePresentation.naive, ftCQuotientRelation, ftCRelation,
    ftCDerivative, ftCDerivativePolynomial]
  have hX : ftCQuotientEquiv k
      (Ideal.Quotient.mk (Ideal.span (Set.range (ftCQuotientRelation k)))
        (MvPolynomial.X PUnit.unit)) =
      (Ideal.Quotient.mk (ftCRelationsIdeal k) Polynomial.X :
        Polynomial (ftA k) ⧸ ftCRelationsIdeal k) := by
    unfold ftCQuotient
    unfold ftCQuotientEquiv
    convert
      (Ideal.quotientEquivAlg_mk
        (I := Ideal.span (Set.range (ftCQuotientRelation k)))
        (J := ftCRelationsIdeal k)
        (f := MvPolynomial.uniqueAlgEquiv (ftA k) PUnit)
        (hIJ := ftCQuotient_map_span k) (x := MvPolynomial.X PUnit.unit)) using 1
    simp
  rw [hX]
  have hax : algebraMap (ftA k) (ftCQuotient k) (ftAX k) =
      Ideal.Quotient.mk (ftCRelationsIdeal k) (Polynomial.C (ftAX k)) := by
    rfl
  have htwo : (Ideal.Quotient.mk (ftCRelationsIdeal k)) (Polynomial.C 2) =
      (2 : ftCQuotient k) := by
    change (Ideal.Quotient.mk (ftCRelationsIdeal k)) (Polynomial.C (2 : ftA k)) =
      (Ideal.Quotient.mk (ftCRelationsIdeal k)) (2 : Polynomial (ftA k))
    congr 1
  rw [hax, htwo]
  ring_nf
  ac_rfl

theorem ftAToC_etale (k : Type u) [Field k] :
    RingHom.Etale (ftAToC k) := by
  unfold ftAToC
  rw [RingHom.etale_algebraMap]
  let P₀ : Algebra.PreSubmersivePresentation (ftA k) (ftCQuotient k)
      PUnit.{u + 1} PUnit.{u + 1} := ftCQuotientPrePresentation k
  let P₁ : Algebra.PreSubmersivePresentation (ftCQuotient k) (ftC k) Unit Unit := by
    change Algebra.PreSubmersivePresentation (ftCQuotient k)
      (Localization.Away (ftCDerivative k)) Unit Unit
    exact Algebra.PreSubmersivePresentation.localizationAway
      (S := Localization.Away (ftCDerivative k)) (ftCDerivative k)
  let P := P₁.comp P₀
  have hP : IsUnit P.jacobian := by
    have hP₁ : P₁.jacobian =
        algebraMap (ftCQuotient k) (ftC k) (ftCDerivative k) := by
      change (Algebra.PreSubmersivePresentation.localizationAway
        (S := Localization.Away (ftCDerivative k)) (ftCDerivative k)).jacobian = _
      rw [Algebra.PreSubmersivePresentation.localizationAway_jacobian]
      rfl
    dsimp [P]
    rw [Algebra.PreSubmersivePresentation.comp_jacobian_eq_jacobian_smul_jacobian,
      Algebra.smul_def, ftCQuotientPrePresentation_jacobian, hP₁]
    have hu : IsUnit (algebraMap (ftCQuotient k) (ftC k) (ftCDerivative k)) := by
      change IsUnit (algebraMap (ftCQuotient k)
        (Localization.Away (ftCDerivative k)) (ftCDerivative k))
      exact IsLocalization.Away.algebraMap_isUnit _
    exact hu.mul hu
  let P' : Algebra.SubmersivePresentation (ftA k) (ftC k)
      (Unit ⊕ PUnit.{u + 1}) (Unit ⊕ PUnit.{u + 1}) :=
    { P with jacobian_isUnit := hP }
  have hdim : P'.dimension = 0 := by
    dsimp [P']
    rw [Algebra.PreSubmersivePresentation.dimension_comp_eq_dimension_add_dimension]
    simp [Algebra.Presentation.dimension]
  exact Algebra.Etale.iff_isStandardSmoothOfRelativeDimension_zero.mpr
    (P'.isStandardSmoothOfRelativeDimension hdim)

theorem ftAToC_finiteType (k : Type u) [Field k] :
    RingHom.FiniteType (ftAToC k) := by
  unfold ftAToC
  rw [RingHom.finiteType_algebraMap]
  have hQ : Algebra.FiniteType (ftA k) (ftCQuotient k) := by
    unfold ftCQuotient
    infer_instance
  have hQC : Algebra.FiniteType (ftCQuotient k) (ftC k) := by
    change Algebra.FiniteType (ftCQuotient k) (Localization.Away (ftCDerivative k))
    infer_instance
  exact Algebra.FiniteType.trans hQ hQC

theorem ftAToC_flat (k : Type u) [Field k] :
    RingHom.Flat (ftAToC k) := by
  exact (RingHom.Etale.iff_flat_and_formallyUnramified.mp (ftAToC_etale k)).1

private theorem ftA_maximalIdeal_eq_span_generators (k : Type u) [Field k] :
    IsLocalRing.maximalIdeal (ftA k) =
      Ideal.span (({ftAX k, ftAY k} : Set (ftA k)) ∪ Set.range (ftAGenerator k)) := by
  let I : Ideal (ftA k) :=
    Ideal.span (({ftAX k, ftAY k} : Set (ftA k)) ∪ Set.range (ftAGenerator k))
  have hmax0 : Ideal.map (algebraMap (ftBasePolynomialRing k) (ftA0 k))
      (ftBaseMaximalIdeal k) = IsLocalRing.maximalIdeal (ftA0 k) := by
    unfold ftA0
    exact IsLocalization.AtPrime.map_eq_maximalIdeal
      (Rₚ := Localization.AtPrime (ftBaseMaximalIdeal k)) (ftBaseMaximalIdeal k)
  have hbase : Ideal.map (algebraMap (ftBasePolynomialRing k) (ftA0 k))
      (ftBaseMaximalIdeal k) = Ideal.span ({ftX k, ftY k} : Set (ftA0 k)) := by
    rw [ftBaseMaximalIdeal, Ideal.map_span]
    apply le_antisymm
    · refine Ideal.span_le.2 ?_
      rintro _ ⟨b, hb, rfl⟩
      rcases (show b = ftBaseX k ∨ b = ftBaseY k by simpa using hb) with rfl | rfl
      · exact Ideal.subset_span (by simp [ftX])
      · exact Ideal.subset_span (by simp [ftY])
    · refine Ideal.span_le.2 ?_
      rintro _ (rfl | rfl)
      · exact Ideal.subset_span ⟨ftBaseX k, by simp, rfl⟩
      · exact Ideal.subset_span ⟨ftBaseY k, by simp, rfl⟩
  have hgen_le : I ≤ (IsLocalRing.maximalIdeal (ftA0 k)).comap (ftAToA0 k) := by
    have hA0 : ∀ a : ftA0 k, ftAToA0 k (ftA0ToA k a) = a := by
      intro a
      have hzero : ∀ x ∈ ftARelationsIdeal k, ftAAugmentation k x = 0 := by
        intro x hx
        exact ftARelations_le_augmentation_ker k hx
      change Ideal.Quotient.lift (ftARelationsIdeal k) (ftAAugmentation k) hzero
          (Ideal.Quotient.mk (ftARelationsIdeal k) (MvPolynomial.C a)) = a
      rw [Ideal.Quotient.lift_mk]
      simp [ftAAugmentation]
    refine Ideal.span_le.2 ?_
    rintro a (ha | ha)
    · rcases (show a = ftAX k ∨ a = ftAY k by simpa using ha) with rfl | rfl
      · have hx0 : ftX k ∈ IsLocalRing.maximalIdeal (ftA0 k) := by
          rw [← hmax0, hbase]
          exact Ideal.subset_span (by simp)
        change ftAToA0 k (ftAX k) ∈ IsLocalRing.maximalIdeal (ftA0 k)
        rw [show ftAToA0 k (ftAX k) = ftX k by
          simpa [ftAX, ftA0ToA] using hA0 (ftX k)]
        exact hx0
      · have hy0 : ftY k ∈ IsLocalRing.maximalIdeal (ftA0 k) := by
          rw [← hmax0, hbase]
          exact Ideal.subset_span (by simp)
        change ftAToA0 k (ftAY k) ∈ IsLocalRing.maximalIdeal (ftA0 k)
        rw [show ftAToA0 k (ftAY k) = ftY k by
          simpa [ftAY, ftA0ToA] using hA0 (ftY k)]
        exact hy0
    · rcases ha with ⟨n, rfl⟩
      change ftAToA0 k (ftAGenerator k n) ∈ IsLocalRing.maximalIdeal (ftA0 k)
      change ftAAugmentation k (MvPolynomial.X n) ∈ IsLocalRing.maximalIdeal (ftA0 k)
      simp [ftAAugmentation]
  have hcomp : IsLocalRing.maximalIdeal (ftA k) =
      (IsLocalRing.maximalIdeal (ftA0 k)).comap (ftAToA0 k) :=
    (IsLocalRing.eq_maximalIdeal
      (Ideal.comap_isMaximal_of_surjective (ftAToA0 k) (ftAToA0_surjective k))).symm
  rw [hcomp]
  apply le_antisymm ?_ hgen_le
  intro a ha
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective a
  change ftAAugmentation k p ∈ IsLocalRing.maximalIdeal (ftA0 k) at ha
  have hconst : ftAAugmentation k p ∈ Ideal.span ({ftX k, ftY k} : Set (ftA0 k)) := by
    rw [← hbase, hmax0]
    exact ha
  have hvar_le : Ideal.map (Ideal.Quotient.mk (ftARelationsIdeal k))
      (MvPolynomial.idealOfVars ℕ (ftA0 k)) ≤ I := by
    rw [MvPolynomial.idealOfVars, Ideal.map_span]
    refine Ideal.span_le.2 ?_
    rintro _ ⟨p, ⟨n, rfl⟩, rfl⟩
    exact Ideal.subset_span (Set.mem_union_right _ ⟨n, rfl⟩)
  have hvar : Ideal.Quotient.mk (ftARelationsIdeal k)
      (p - MvPolynomial.C (ftAAugmentation k p)) ∈ I :=
    hvar_le (Ideal.mem_map_of_mem _ (ftAAugmentation_eq_zero_mem_idealOfVars k
      (by simp [ftAAugmentation])))
  have hconst_le : Ideal.map (algebraMap (ftA0 k) (ftA k))
      (Ideal.span ({ftX k, ftY k} : Set (ftA0 k))) ≤ I := by
    rw [Ideal.map_span]
    refine Ideal.span_le.2 ?_
    rintro _ ⟨a, ha, rfl⟩
    rcases (show a = ftX k ∨ a = ftY k by simpa using ha) with rfl | rfl
    · change ftAX k ∈ I
      exact Ideal.subset_span (Set.mem_union_left _ (Set.mem_insert_iff.mpr (Or.inl rfl)))
    · change ftAY k ∈ I
      exact Ideal.subset_span (Set.mem_union_left _ (Set.mem_insert_iff.mpr (Or.inr rfl)))
  have hconst' : Ideal.Quotient.mk (ftARelationsIdeal k)
      (MvPolynomial.C (ftAAugmentation k p)) ∈ I := by
    change algebraMap (ftA0 k) (ftA k) (ftAAugmentation k p) ∈ I
    exact hconst_le (Ideal.mem_map_of_mem _ hconst)
  change Ideal.Quotient.mk (ftARelationsIdeal k) p ∈ I
  have heq : Ideal.Quotient.mk (ftARelationsIdeal k) p =
      Ideal.Quotient.mk (ftARelationsIdeal k)
          (p - MvPolynomial.C (ftAAugmentation k p)) +
        Ideal.Quotient.mk (ftARelationsIdeal k) (MvPolynomial.C (ftAAugmentation k p)) := by
    rw [← map_add]
    simp
  rw [heq]
  exact I.add_mem hvar hconst'

/-- The maximal ideal generated by `x`, `y`, `z`, and all `zₙ`. -/
def ftCQ (k : Type u) [Field k] : Ideal (ftC k) :=
  Ideal.span (({ftCX k, ftCY k, ftCZ k} : Set (ftC k)) ∪ Set.range (ftCZn k))

instance ftCQ_isMaximal (k : Type u) [Field k] :
    (ftCQ k).IsMaximal := by
  let m : Ideal (ftA k) := IsLocalRing.maximalIdeal (ftA k)
  let K := ftA k ⧸ m
  letI : Field K := Ideal.Quotient.field m
  let ρ : ftA k →+* K := Ideal.Quotient.mk m
  let e : Polynomial (ftA k) →+* K := Polynomial.eval₂RingHom ρ 0
  have hmX : ftAX k ∈ m := by
    rw [show m = IsLocalRing.maximalIdeal (ftA k) by rfl,
      ftA_maximalIdeal_eq_span_generators]
    exact Ideal.subset_span (Set.mem_union_left _ (by simp))
  have hmY : ftAY k ∈ m := by
    rw [show m = IsLocalRing.maximalIdeal (ftA k) by rfl,
      ftA_maximalIdeal_eq_span_generators]
    exact Ideal.subset_span (Set.mem_union_left _ (by simp))
  have hmG : ∀ n : ℕ, ftAGenerator k n ∈ m := by
    intro n
    rw [show m = IsLocalRing.maximalIdeal (ftA k) by rfl,
      ftA_maximalIdeal_eq_span_generators]
    exact Ideal.subset_span (Set.mem_union_right _ ⟨n, rfl⟩)
  have hρX : ρ (ftAX k) = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hmX
  have hρY : ρ (ftAY k) = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hmY
  have hρG : ∀ n : ℕ, ρ (ftAGenerator k n) = 0 :=
    fun n => Ideal.Quotient.eq_zero_iff_mem.mpr (hmG n)
  have hrel : ftCRelationsIdeal k ≤ RingHom.ker e := by
    refine Ideal.span_le.2 ?_
    intro p hp
    rcases hp with rfl
    change e (Polynomial.C (ftAX k) * Polynomial.X ^ 2 + Polynomial.X +
      Polynomial.C (ftAY k)) = 0
    simp [e, hρX, hρY]
  let f0 : ftCQuotient k →+* K :=
    Ideal.Quotient.lift (ftCRelationsIdeal k) e hrel
  let q0 : Ideal (ftCQuotient k) :=
    Ideal.span ((({algebraMap (ftA k) (ftCQuotient k) (ftAX k),
      algebraMap (ftA k) (ftCQuotient k) (ftAY k)} : Set (ftCQuotient k)) ∪
      {Ideal.Quotient.mk (ftCRelationsIdeal k) Polynomial.X}) ∪
      Set.range (fun n : ℕ => algebraMap (ftA k) (ftCQuotient k)
        (ftAGenerator k n)))
  have hq0ker : q0 ≤ RingHom.ker f0 := by
    refine Ideal.span_le.2 ?_
    rintro z (hz | hz)
    · rcases hz with hz | hz
      · rcases (show z = algebraMap (ftA k) (ftCQuotient k) (ftAX k) ∨
          z = algebraMap (ftA k) (ftCQuotient k) (ftAY k) by
          simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hz) with rfl | rfl
        · change e (Polynomial.C (ftAX k)) = 0
          simp [e, hρX]
        · change e (Polynomial.C (ftAY k)) = 0
          simp [e, hρY]
      · have hz' := Set.mem_singleton_iff.mp hz
        rw [hz']
        change e Polynomial.X = 0
        simp [e]
    · rcases hz with ⟨n, rfl⟩
      change e (Polynomial.C (ftAGenerator k n)) = 0
      simp [e, hρG n]
  let qmap : Polynomial (ftA k) →+* ftCQuotient k := by
    change Polynomial (ftA k) →+* (Polynomial (ftA k) ⧸ ftCRelationsIdeal k)
    exact Ideal.Quotient.mk (ftCRelationsIdeal k)
  let P : Ideal (Polynomial (ftA k)) :=
    Ideal.span (({Polynomial.C a | a ∈ m} : Set (Polynomial (ftA k))) ∪
      {Polynomial.X})
  have hmap_m : Ideal.map (algebraMap (ftA k) (ftCQuotient k)) m ≤ q0 := by
    rw [show m = IsLocalRing.maximalIdeal (ftA k) by rfl,
      ftA_maximalIdeal_eq_span_generators, Ideal.map_span]
    refine Ideal.span_le.2 ?_
    rintro z ⟨a, ha, rfl⟩
    rcases ha with ha | ha
    · rcases (show a = ftAX k ∨ a = ftAY k by simpa using ha) with rfl | rfl
      · exact Ideal.subset_span (Set.mem_union_left _ (by simp))
      · exact Ideal.subset_span (Set.mem_union_left _ (by simp))
    · rcases ha with ⟨n, rfl⟩
      exact Ideal.subset_span (Set.mem_union_right _ ⟨n, rfl⟩)
  have hPmap : Ideal.map qmap P ≤ q0 := by
    change Ideal.map qmap
      (Ideal.span (({Polynomial.C a | a ∈ m} : Set (Polynomial (ftA k))) ∪
        {Polynomial.X})) ≤ q0
    rw [Ideal.map_span]
    refine Ideal.span_le.2 ?_
    rintro z ⟨p, hp, rfl⟩
    rcases hp with ⟨a, ha, rfl⟩ | rfl
    · change algebraMap (ftA k) (ftCQuotient k) a ∈ q0
      exact hmap_m (Ideal.mem_map_of_mem _ ha)
    · change Ideal.Quotient.mk (ftCRelationsIdeal k) Polynomial.X ∈ q0
      change Ideal.Quotient.mk (ftCRelationsIdeal k) Polynomial.X ∈
        Ideal.span ((({algebraMap (ftA k) (ftCQuotient k) (ftAX k),
          algebraMap (ftA k) (ftCQuotient k) (ftAY k)} : Set (ftCQuotient k)) ∪
          {Ideal.Quotient.mk (ftCRelationsIdeal k) Polynomial.X}) ∪
          Set.range (fun n : ℕ => algebraMap (ftA k) (ftCQuotient k)
            (ftAGenerator k n)))
      exact Ideal.subset_span (Set.mem_union_left _
        (Set.mem_union_right _ (Set.mem_singleton_iff.mpr rfl)))
  have hpoly : ∀ t : Polynomial (ftA k), e t = 0 → t ∈ P := by
    intro t ht
    have htconst : ρ (t.constantCoeff) = 0 := by
      simpa [e] using ht
    have hconst : t.constantCoeff ∈ m :=
      Ideal.Quotient.eq_zero_iff_mem.mp htconst
    have hrest0 : (t - Polynomial.C (t.constantCoeff)).constantCoeff = 0 := by
      simp
    have hrest : t - Polynomial.C (t.constantCoeff) ∈
        Ideal.span ({Polynomial.X} : Set (Polynomial (ftA k))) := by
      rw [← Polynomial.ker_constantCoeff]
      exact hrest0
    have hrestle : Ideal.span ({Polynomial.X} : Set (Polynomial (ftA k))) ≤ P := by
      refine Ideal.span_le.2 ?_
      intro z hz
      exact Ideal.subset_span (Set.mem_union_right _ hz)
    have hconstmem : Polynomial.C (t.constantCoeff) ∈ P := by
      exact Ideal.subset_span
        (Set.mem_union_left _ ⟨t.constantCoeff, hconst, rfl⟩)
    have hadd := P.add_mem (hrestle hrest) hconstmem
    rw [← sub_add_cancel t (Polynomial.C (t.constantCoeff))]
    exact hadd
  have hker0 : RingHom.ker f0 ≤ q0 := by
    intro b hb
    obtain ⟨t, rfl⟩ := Ideal.Quotient.mk_surjective b
    change e t = 0 at hb
    exact hPmap (Ideal.mem_map_of_mem _ (hpoly t hb))
  have hqmap : Ideal.map (algebraMap (ftCQuotient k) (ftC k)) q0 ≤ ftCQ k := by
    change Ideal.map (algebraMap (ftCQuotient k) (ftC k))
        (Ideal.span ((({algebraMap (ftA k) (ftCQuotient k) (ftAX k),
          algebraMap (ftA k) (ftCQuotient k) (ftAY k)} : Set (ftCQuotient k)) ∪
          {Ideal.Quotient.mk (ftCRelationsIdeal k) Polynomial.X}) ∪
          Set.range (fun n : ℕ => algebraMap (ftA k) (ftCQuotient k)
            (ftAGenerator k n)))) ≤
      Ideal.span (({ftCX k, ftCY k, ftCZ k} : Set (ftC k)) ∪
        Set.range (ftCZn k))
    rw [Ideal.map_span]
    have hscalar (a : ftA k) :
        algebraMap (ftCQuotient k) (ftC k)
            (algebraMap (ftA k) (ftCQuotient k) a) = ftAToC k a := by
      change algebraMap (ftA k) (ftC k) a = ftAToC k a
      rfl
    refine Ideal.span_le.2 ?_
    rintro z ⟨b, hb, rfl⟩
    rcases hb with hb | hb
    · rcases hb with hb | hb
      · rcases (show b = algebraMap (ftA k) (ftCQuotient k) (ftAX k) ∨
          b = algebraMap (ftA k) (ftCQuotient k) (ftAY k) by
          simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hb) with rfl | rfl
        · change ftAToC k (ftAX k) ∈ _
          rw [← hscalar (ftAX k)]
          exact Ideal.subset_span (Set.mem_union_left _
            (Set.mem_insert_iff.mpr (Or.inl rfl)))
        · change ftAToC k (ftAY k) ∈ _
          rw [← hscalar (ftAY k)]
          exact Ideal.subset_span (Set.mem_union_left _
            (Set.mem_insert_iff.mpr (Or.inr (Or.inl rfl))))
      · have hb' := Set.mem_singleton_iff.mp hb
        rw [hb']
        exact Ideal.subset_span (Set.mem_union_left _
          (Set.mem_insert_iff.mpr (Or.inr (Or.inr rfl))))
    · rcases hb with ⟨n, rfl⟩
      exact Ideal.subset_span (Set.mem_union_right _ ⟨n, rfl⟩)
  have hder : IsUnit (f0 (ftCDerivative k)) := by
    change IsUnit (e (ftCDerivativePolynomial k))
    simp [ftCDerivativePolynomial, e, hρX]
  let f : ftC k →+* K := by
    change Localization.Away (ftCDerivative k) →+* K
    exact IsLocalization.Away.lift (S := Localization.Away (ftCDerivative k))
      (x := ftCDerivative k) (g := f0) hder
  have hfB : f.comp (algebraMap (ftCQuotient k) (ftC k)) = f0 := by
    change (IsLocalization.Away.lift (S := Localization.Away (ftCDerivative k))
      (x := ftCDerivative k) (g := f0) hder).comp
        (algebraMap (ftCQuotient k) (Localization.Away (ftCDerivative k))) = f0
    exact IsLocalization.Away.lift_comp (x := ftCDerivative k) (g := f0) hder
  have hfB_apply : ∀ b : ftCQuotient k,
      f (algebraMap (ftCQuotient k) (ftC k) b) = f0 b := by
    intro b
    have h := congrArg (fun g : ftCQuotient k →+* K => g b) hfB
    change f (algebraMap (ftCQuotient k) (ftC k) b) = f0 b at h
    exact h
  have hfA : ∀ a : ftA k, f (ftAToC k a) = ρ a := by
    intro a
    change f (algebraMap (ftCQuotient k) (ftC k)
      (algebraMap (ftA k) (ftCQuotient k) a)) = ρ a
    calc
      f (algebraMap (ftCQuotient k) (ftC k)
          (algebraMap (ftA k) (ftCQuotient k) a)) =
          f0 (algebraMap (ftA k) (ftCQuotient k) a) := hfB_apply _
      _ = ρ a := by
        change e (Polynomial.C a) = ρ a
        simp [e]
  have hsurj : Function.Surjective f := by
    intro z
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective z
    exact ⟨ftAToC k a, hfA a⟩
  let x0 : ftCQuotient k := by
    change Polynomial (ftA k) ⧸ ftCRelationsIdeal k
    exact Ideal.Quotient.mk (ftCRelationsIdeal k) Polynomial.X
  have hx0 : algebraMap (ftCQuotient k) (ftC k) x0 = ftCZ k := by
    rfl
  have hfCZ : f (ftCZ k) = 0 := by
    rw [← hx0, hfB_apply]
    change e Polynomial.X = 0
    simp [e]
  have hCQker : ftCQ k ≤ RingHom.ker f := by
    rw [ftCQ]
    refine Ideal.span_le.2 ?_
    rintro z (hz | hz)
    · rcases (show z = ftCX k ∨ z = ftCY k ∨ z = ftCZ k by
        simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hz) with rfl | rfl | rfl
      · change f (ftAToC k (ftAX k)) = 0
        rw [hfA, hρX]
      · change f (ftAToC k (ftAY k)) = 0
        rw [hfA, hρY]
      · exact hfCZ
    · rcases hz with ⟨n, rfl⟩
      change f (ftAToC k (ftAGenerator k n)) = 0
      rw [hfA, hρG n]
  have hkerf : RingHom.ker f ≤ ftCQ k := by
    intro c hc
    letI : IsLocalization (Submonoid.powers (ftCDerivative k)) (ftC k) := by
      change IsLocalization (Submonoid.powers (ftCDerivative k))
        (Localization.Away (ftCDerivative k))
      infer_instance
    change Localization.Away (ftCDerivative k) at c
    obtain ⟨p, s, rfl⟩ := IsLocalization.exists_mk'_eq
      (S := ftC k) (Submonoid.powers (ftCDerivative k)) c
    have hprod := congrArg f (IsLocalization.mk'_spec
      (S := ftC k) p s)
    have hc0 : f (IsLocalization.mk' (ftC k) p s) = 0 := hc
    have hprod' : f (IsLocalization.mk' (ftC k) p s) *
        f (algebraMap (ftCQuotient k) (ftC k) (s : ftCQuotient k)) =
        f (algebraMap (ftCQuotient k) (ftC k) p) := by
      rw [← map_mul]
      exact hprod
    rw [hc0, zero_mul] at hprod'
    have hnumf : f (algebraMap (ftCQuotient k) (ftC k) p) = 0 := hprod'.symm
    have hnumf0 : f0 p = 0 := by
      have h := hfB_apply p
      exact (h.symm ▸ hnumf)
    have hpq : p ∈ q0 := hker0 hnumf0
    have hnum : algebraMap (ftCQuotient k) (ftC k) p ∈ ftCQ k := by
      exact hqmap (Ideal.mem_map_of_mem _ hpq)
    apply (Ideal.unit_mul_mem_iff_mem _
      (IsLocalization.map_units (ftC k) s)).mp
    change algebraMap (ftCQuotient k) (ftC k) (s : ftCQuotient k) *
      IsLocalization.mk' (ftC k) p s ∈ ftCQ k
    have heq : algebraMap (ftCQuotient k) (ftC k) (s : ftCQuotient k) *
        IsLocalization.mk' (ftC k) p s =
        algebraMap (ftCQuotient k) (ftC k) p := by
      rw [mul_comm]
      exact IsLocalization.mk'_spec (S := ftC k) p s
    rw [heq]
    exact hnum
  have hker : RingHom.ker f = ftCQ k := le_antisymm hkerf hCQker
  exact hker ▸ RingHom.ker_isMaximal_of_surjective f hsurj

instance ftCQ_isPrime (k : Type u) [Field k] :
    (ftCQ k).IsPrime := by
  exact (ftCQ_isMaximal k).isPrime

def ftCPrimeIdeal (k : Type u) [Field k] (n : ℕ) : Ideal (ftC k) :=
  Ideal.map (ftAToC k) (ftAPrime k n)

private theorem ft_annihilator_element_flat_base_change
    {R S M : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup M] [Module R M] [Module.Flat R S] (m : M) :
    (Submodule.span R ({m} : Set M)).annihilator.map (algebraMap R S) =
      (Submodule.span S ({(1 : S) ⊗ₜ[R] m} : Set (TensorProduct R S M))).annihilator := by
  rw [Submodule.annihilator_span_singleton, Submodule.annihilator_span_singleton]
  let f : R →ₗ[R] M := LinearMap.toSpanSingleton R M m
  have h_exact : Function.Exact (LinearMap.ker f).subtype f :=
    f.exact_subtype_ker_map
  have h_exact' := Module.Flat.lTensor_exact S h_exact
  have hker : LinearMap.ker (f.lTensor S) =
      LinearMap.range ((LinearMap.ker f).subtype.lTensor S) :=
    h_exact'.linearMap_ker_eq
  apply le_antisymm
  · rw [Ideal.map_le_iff_le_comap]
    intro r hr
    change (LinearMap.toSpanSingleton S (TensorProduct R S M)
      (1 ⊗ₜ[R] m)) (algebraMap R S r) = 0
    rw [LinearMap.toSpanSingleton_apply]
    simpa [f] using congrArg (fun x => (1 : S) ⊗ₜ[R] x)
      (show f r = 0 from hr)
  · intro s hs
    have hs' : (s ⊗ₜ[R] (1 : R)) ∈ LinearMap.ker (f.lTensor S) := by
      change (f.lTensor S) (s ⊗ₜ[R] (1 : R)) = 0
      have hcalc : (f.lTensor S) (s ⊗ₜ[R] (1 : R)) =
          s ⊗ₜ[R] f 1 := by rfl
      rw [hcalc]
      rw [show f 1 = m by simp [f]]
      rw [TensorProduct.tmul_eq_smul_one_tmul]
      exact (LinearMap.toSpanSingleton_apply S (TensorProduct R S M)
        (1 ⊗ₜ[R] m) s).symm ▸ hs
    obtain ⟨y, hy⟩ := LinearMap.mem_range.mp (hker ▸ hs')
    have hmem : ∀ (y : TensorProduct R S (LinearMap.ker f)) (s : S),
        (LinearMap.lTensor S (LinearMap.ker f).subtype) y =
            s ⊗ₜ[R] (1 : R) →
          s ∈ Ideal.map (algebraMap R S)
            (LinearMap.ker (LinearMap.toSpanSingleton R M m)) := by
      intro y
      induction y using TensorProduct.induction_on with
      | zero =>
          intro s hs
          have hs0 := congrArg (TensorProduct.rid R S) hs
          simp at hs0
          simpa [hs0] using (Ideal.map (algebraMap R S)
            (LinearMap.ker (LinearMap.toSpanSingleton R M m))).zero_mem
      | add x y hx hy =>
          intro s hs
          have hs' := congrArg (TensorProduct.rid R S) hs
          have hxy : s = (TensorProduct.rid R S)
              ((LinearMap.lTensor S (LinearMap.ker f).subtype) x) +
              (TensorProduct.rid R S)
                ((LinearMap.lTensor S (LinearMap.ker f).subtype) y) := by
            simpa using hs'.symm
          subst s
          exact (Ideal.map (algebraMap R S)
            (LinearMap.ker (LinearMap.toSpanSingleton R M m))).add_mem
            (hx _ (by
              rw [← TensorProduct.rid_symm_apply]
              exact ((TensorProduct.rid R S).symm_apply_apply _).symm))
            (hy _ (by
              rw [← TensorProduct.rid_symm_apply]
              exact ((TensorProduct.rid R S).symm_apply_apply _).symm))
      | tmul s' i =>
          intro s hs
          have hs' := congrArg (TensorProduct.rid R S) hs
          have hi : algebraMap R S (i : R) ∈
              Ideal.map (algebraMap R S)
                (LinearMap.ker (LinearMap.toSpanSingleton R M m)) :=
            Ideal.mem_map_of_mem (algebraMap R S) i.property
          have hsi := (Ideal.map (algebraMap R S)
            (LinearMap.ker (LinearMap.toSpanSingleton R M m))).mul_mem_left s' hi
          have hs'' : (i : R) • s' = s := by simpa using hs'
          rw [← hs'']
          simpa [Algebra.smul_def, mul_comm] using hsi
    exact hmem y s hy

theorem ftCZn_annihilator (k : Type u) [Field k] (n : ℕ) :
    (Submodule.span (ftC k) ({ftCZn k n} : Set (ftC k))).annihilator =
      ftCPrimeIdeal k n := by
  have hflat : Module.Flat (ftA k) (ftC k) :=
    RingHom.flat_algebraMap_iff.mp (ftAToC_flat k)
  have hbase := @ft_annihilator_element_flat_base_change (ftA k) (ftC k) (ftA k)
    _ _ _ _ (inferInstance : Module (ftA k) (ftA k)) hflat (ftAGenerator k n)
  let g := ftAGenerator k n
  let rid := TensorProduct.rid (ftA k) (ftC k)
  have hrid (s : ftC k) : rid (s • ((1 : ftC k) ⊗ₜ[ftA k] g)) =
      s * ftAToC k g := by
    rw [← TensorProduct.tmul_eq_smul_one_tmul]
    simp [rid, g, ftAToC, Algebra.smul_def, mul_comm]
  have hmem (s : ftC k) :
      s ∈ (Submodule.span (ftC k) ({ftCZn k n} : Set (ftC k))).annihilator ↔
        s ∈ (Submodule.span (ftC k)
          ({(1 : ftC k) ⊗ₜ[ftA k] g} :
            Set (TensorProduct (ftA k) (ftC k) (ftA k)))).annihilator := by
    rw [Submodule.mem_annihilator_span_singleton,
      Submodule.mem_annihilator_span_singleton]
    change s • ftAToC k g = 0 ↔
      s • ((1 : ftC k) ⊗ₜ[ftA k] g) = 0
    constructor
    · intro hs
      apply rid.injective
      rw [map_zero, hrid]
      simpa [Algebra.smul_def, mul_comm] using hs
    · intro hs
      have h := congrArg rid hs
      rw [hrid] at h
      simpa [Algebra.smul_def, mul_comm] using h
  apply le_antisymm
  · intro s hs
    have hs' := (hmem s).mp hs
    have hs'' : s ∈ (Submodule.span (ftC k)
        ({(1 : ftC k) ⊗ₜ[ftA k] (ftAGenerator k n)} :
          Set (TensorProduct (ftA k) (ftC k) (ftA k)))).annihilator := by
      simpa [g] using hs'
    have hsmap : s ∈ Ideal.map (algebraMap (ftA k) (ftC k))
        (Submodule.span (ftA k) ({ftAGenerator k n} : Set (ftA k))).annihilator := by
      exact hbase.symm ▸ hs''
    change s ∈ Ideal.map (ftAToC k) (ftAPrime k n)
    simpa only [ftAGenerator_annihilator k n, ftAToC] using hsmap
  · intro s hs
    change s ∈ Ideal.map (ftAToC k) (ftAPrime k n) at hs
    have hsmap : s ∈ Ideal.map (algebraMap (ftA k) (ftC k))
        (Submodule.span (ftA k) ({ftAGenerator k n} : Set (ftA k))).annihilator := by
      exact (ftAGenerator_annihilator k n).symm ▸ hs
    have hs'' : s ∈ (Submodule.span (ftC k)
        ({(1 : ftC k) ⊗ₜ[ftA k] (ftAGenerator k n)} :
          Set (TensorProduct (ftA k) (ftC k) (ftA k)))).annihilator := by
      exact hbase ▸ hsmap
    have hs' : s ∈ (Submodule.span (ftC k)
        ({(1 : ftC k) ⊗ₜ[ftA k] g} :
          Set (TensorProduct (ftA k) (ftC k) (ftA k)))).annihilator := by
      simpa [g] using hs''
    exact (hmem s).mpr hs'

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
  simpa [ftKXMaximalIdeal] using
    (RingHom.ker_isPrime (Polynomial.constantCoeff : Polynomial k →+* k))

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
