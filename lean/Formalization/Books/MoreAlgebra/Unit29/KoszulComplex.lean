import Formalization.Books.Algebra.Unit09.Localization
import Formalization.Books.Algebra.Unit13.TensorAlgebra
import Formalization.Books.Algebra.Unit78.FiniteProjectiveModules
import Formalization.Books.Homology.Unit14.HomotopyAndShift
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Symmetric
import Mathlib.Algebra.Homology.HomotopyCofiber
import Mathlib.Algebra.Homology.Monoidal
import Mathlib.Algebra.Homology.TotalComplex
import Mathlib.LinearAlgebra.Alternating.Uncurry.Fin

/-!
# More on Algebra, Chapter 29: The Koszul complex

The chapter's Koszul complexes are expressed using Mathlib's exterior powers and
homological-complex interfaces.  The propositions below record the textbook's
construction and theorem interfaces; the proposition proofs belong to the later
proof stage.
-/

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open HomologicalComplex
open ComplexShape

universe u

namespace Formalization.Books.MoreAlgebra.Unit29

/-! ## The exterior differential -/

/-- The homogeneous module used in degree `n` of a Koszul complex. -/
abbrev koszulTerm (R E : Type u) (n : ℕ) [CommRing R] [AddCommGroup E]
    [Module R E] := ⋀[R]^n E

/-- The alternating map which contracts one exterior generator with `φ`. -/
def koszulContractionPre (R E : Type u) [CommRing R] [AddCommGroup E] [Module R E]
    (φ : E →ₗ[R] R) (n : ℕ) :
    E →ₗ[R] E [⋀^Fin n]→ₗ[R] (⋀[R]^n E) :=
  { toFun := fun e => (φ e) • exteriorPower.ιMulti R n
    map_add' := by
      intro e e'
      simp [map_add, add_smul]
    map_smul' := by
      intro a e
      simp [map_smul, smul_smul] }

/-- The corresponding contraction with values in the full exterior algebra. -/
def koszulContractionPreAlgebra (R E : Type u) [CommRing R] [AddCommGroup E]
    [Module R E] (φ : E →ₗ[R] R) (n : ℕ) :
    E →ₗ[R] E [⋀^Fin n]→ₗ[R] ExteriorAlgebra R E :=
  { toFun := fun e => (φ e) • ExteriorAlgebra.ιMulti R n
    map_add' := by
      intro e e'
      simp [map_add, add_smul]
    map_smul' := by
      intro a e
      simp [map_smul, smul_smul] }

/-- Uncurrying the contraction gives the Koszul differential on generators. -/
def koszulContraction (R E : Type u) [CommRing R] [AddCommGroup E] [Module R E]
    (φ : E →ₗ[R] R) (n : ℕ) :
    E [⋀^Fin (n + 1)]→ₗ[R] (⋀[R]^n E) :=
  AlternatingMap.alternatizeUncurryFin (koszulContractionPre R E φ n)

/-- The same uncurried map, now regarded as taking values in the exterior algebra. -/
def koszulContractionAlgebra (R E : Type u) [CommRing R] [AddCommGroup E]
    [Module R E] (φ : E →ₗ[R] R) (n : ℕ) :
    E [⋀^Fin (n + 1)]→ₗ[R] ExteriorAlgebra R E :=
  AlternatingMap.alternatizeUncurryFin (koszulContractionPreAlgebra R E φ n)

/-- The differential on the `n+1`st exterior power. -/
noncomputable def koszulDifferential (R E : Type u) [CommRing R] [AddCommGroup E]
    [Module R E] (φ : E →ₗ[R] R) (n : ℕ) :
    (⋀[R]^(n + 1) E) →ₗ[R] (⋀[R]^n E) :=
  exteriorPower.alternatingMapLinearEquiv (koszulContraction R E φ n)

/-- The explicit alternating-sum formula for the Koszul differential.

Lean numbers the entries of a `Fin` tuple from zero, so the exponent `i` here
is the source's exponent `i+1` after reindexing. -/
theorem koszulDifferential_apply_ιMulti (R E : Type u) [CommRing R]
    [AddCommGroup E] [Module R E] (φ : E →ₗ[R] R) (n : ℕ)
    (v : Fin (n + 1) → E) :
    koszulDifferential R E φ n (exteriorPower.ιMulti R (n + 1) v) =
    ∑ i : Fin (n + 1), (-1 : R) ^ (i : ℕ) •
        ((φ (v i)) • exteriorPower.ιMulti R n (i.removeNth v)) := by
  rw [koszulDifferential, exteriorPower.alternatingMapLinearEquiv_apply_ιMulti]
  simp only [koszulContraction, AlternatingMap.alternatizeUncurryFin_apply,
    koszulContractionPre, LinearMap.coe_mk, AddHom.coe_mk]
  simp_rw [← Int.cast_smul_eq_zsmul R]
  simp

/-- The differential on the full exterior algebra, obtained from the alternating
maps on each homogeneous component. -/
noncomputable def koszulAlgebraDifferential (R E : Type u) [CommRing R]
    [AddCommGroup E] [Module R E] (φ : E →ₗ[R] R) :
    ExteriorAlgebra R E →ₗ[R] ExteriorAlgebra R E :=
  ExteriorAlgebra.liftAlternating (fun n =>
    match n with
    | 0 => 0
    | n + 1 => koszulContractionAlgebra R E φ n)

/-- The full-algebra version of the explicit differential formula. -/
theorem koszulAlgebraDifferential_apply_ιMulti (R E : Type u) [CommRing R]
    [AddCommGroup E] [Module R E] (φ : E →ₗ[R] R) (n : ℕ)
    (v : Fin (n + 1) → E) :
    koszulAlgebraDifferential R E φ (ExteriorAlgebra.ιMulti R (n + 1) v) =
    ∑ i : Fin (n + 1), (-1 : R) ^ (i : ℕ) •
        ((φ (v i)) • ExteriorAlgebra.ιMulti R n (i.removeNth v)) := by
  rw [koszulAlgebraDifferential, ExteriorAlgebra.liftAlternating_apply_ιMulti]
  simp only [koszulContractionAlgebra, AlternatingMap.alternatizeUncurryFin_apply,
    koszulContractionPreAlgebra, LinearMap.coe_mk, AddHom.coe_mk]
  simp_rw [← Int.cast_smul_eq_zsmul R]
  simp

/-- The graded Leibniz identity required of a differential on the exterior algebra. -/
def IsKoszulDerivation (R E : Type u) [CommRing R] [AddCommGroup E] [Module R E]
    (φ : E →ₗ[R] R)
    (d : ExteriorAlgebra R E →ₗ[R] ExteriorAlgebra R E) : Prop :=
  (∀ (n m : ℕ) (x : ⋀[R]^n E) (y : ⋀[R]^m E),
      d ((x : ExteriorAlgebra R E) * (y : ExteriorAlgebra R E)) =
        d (x : ExteriorAlgebra R E) * (y : ExteriorAlgebra R E) +
          (-1 : R) ^ n •
            ((x : ExteriorAlgebra R E) * d (y : ExteriorAlgebra R E))) ∧
    (∀ e, d (ExteriorAlgebra.ι R e) = algebraMap R (ExteriorAlgebra R E) (φ e))

/-- The algebra differential is a graded derivation and squares to zero. -/
def IsKoszulDGA (R E : Type u) [CommRing R] [AddCommGroup E] [Module R E]
    (φ : E →ₗ[R] R) (D : ExteriorAlgebra R E →ₗ[R] ExteriorAlgebra R E) : Prop :=
  IsKoszulDerivation R E φ D ∧ D.comp D = 0

/-- The commutative DGA underlying the Koszul complex. -/
structure KoszulDGA (R E : Type u) [CommRing R] [AddCommGroup E] [Module R E]
    (φ : E →ₗ[R] R) where
  differential : ExteriorAlgebra R E →ₗ[R] ExteriorAlgebra R E
  isDGA : IsKoszulDGA R E φ differential

private theorem koszulAlgebraDifferential_on_generator_aux (R E : Type u) [CommRing R]
    [AddCommGroup E] [Module R E] (φ : E →ₗ[R] R) (e : E) :
    koszulAlgebraDifferential R E φ (ExteriorAlgebra.ι R e) =
      algebraMap R (ExteriorAlgebra R E) (φ e) := by
  rw [show ExteriorAlgebra.ι R e = ExteriorAlgebra.ιMulti R 1 (fun _ => e) by
    simp only [ExteriorAlgebra.ιMulti_succ_apply, Matrix.vecTail,
      ExteriorAlgebra.ιMulti_zero_apply, mul_one],
    koszulAlgebraDifferential_apply_ιMulti]
  simp [Algebra.algebraMap_eq_smul_one]

private theorem koszulAlgebraDifferential_mul_generator_aux (R E : Type u) [CommRing R]
    [AddCommGroup E] [Module R E] (φ : E →ₗ[R] R) (e : E)
    (x : ExteriorAlgebra R E) :
    koszulAlgebraDifferential R E φ (ExteriorAlgebra.ι R e * x) =
      koszulAlgebraDifferential R E φ (ExteriorAlgebra.ι R e) * x +
        (-1 : R) • (ExteriorAlgebra.ι R e * koszulAlgebraDifferential R E φ x) := by
  have hmap :
      (koszulAlgebraDifferential R E φ).comp
          (LinearMap.mulLeft R (ExteriorAlgebra.ι R e)) =
        LinearMap.mulLeft R (koszulAlgebraDifferential R E φ (ExteriorAlgebra.ι R e)) +
          (-1 : R) •
            (LinearMap.mulLeft R (ExteriorAlgebra.ι R e)).comp
              (koszulAlgebraDifferential R E φ) := by
    apply ExteriorAlgebra.lhom_ext
    intro n
    ext v
    simp only [LinearMap.compAlternatingMap_apply, LinearMap.add_apply, LinearMap.smul_apply,
      LinearMap.comp_apply, LinearMap.mulLeft_apply]
    rw [koszulAlgebraDifferential, ExteriorAlgebra.liftAlternating_ι_mul,
      ExteriorAlgebra.liftAlternating_apply_ιMulti]
    simp only [koszulContractionAlgebra]
    change AlternatingMap.alternatizeUncurryFin
        (koszulContractionPreAlgebra R E φ n) (Matrix.vecCons e v) = _
    rw [AlternatingMap.alternatizeUncurryFin_apply, Fin.sum_univ_succ]
    cases n with
    | zero =>
        simp [koszulAlgebraDifferential_on_generator_aux,
          koszulContractionPreAlgebra, Int.cast_smul_eq_zsmul,
          AlternatingMap.alternatizeUncurryFin_apply]
    | succ n =>
        have hremove (i : Fin (n + 1)) :
            i.succ.removeNth (Matrix.vecCons e v) =
              Matrix.vecCons e (i.removeNth v) := by
          ext j
          simpa [Matrix.vecCons, Fin.removeNth, Function.comp_apply] using
            congrFun (Fin.cons_comp_succ_succAbove e v i) j
        rw [ExteriorAlgebra.liftAlternating_apply_ιMulti]
        simp [koszulAlgebraDifferential_on_generator_aux,
          koszulAlgebraDifferential_apply_ιMulti, koszulContractionPreAlgebra,
          Int.cast_smul_eq_zsmul, AlternatingMap.alternatizeUncurryFin_apply,
          hremove, Finset.mul_sum, pow_succ, smul_eq_mul, mul_assoc, mul_comm,
          mul_left_comm]
        apply Finset.sum_congr rfl
        intro i hi
        congr 1
        have hsign :
            ((-1 : ExteriorAlgebra R E) ^ (i : ℕ)) =
              algebraMap R (ExteriorAlgebra R E) ((-1 : R) ^ (i : ℕ)) := by
          rw [map_pow, map_neg, map_one]
        rw [hsign, ← Algebra.left_comm (R := R)]
  exact LinearMap.congr_fun hmap x

private theorem koszulAlgebraDifferential_mul_homogeneous_aux (R E : Type u)
    [CommRing R] [AddCommGroup E] [Module R E] (φ : E →ₗ[R] R) (n : ℕ)
    (x : ⋀[R]^n E) (y : ExteriorAlgebra R E) :
    koszulAlgebraDifferential R E φ ((x : ExteriorAlgebra R E) * y) =
      koszulAlgebraDifferential R E φ (x : ExteriorAlgebra R E) * y +
        (-1 : R) ^ n •
          ((x : ExteriorAlgebra R E) * koszulAlgebraDifferential R E φ y) := by
  have hι : ∀ (n : ℕ) (v : Fin n → E) (y : ExteriorAlgebra R E),
      koszulAlgebraDifferential R E φ
          (ExteriorAlgebra.ιMulti R n v * y) =
        koszulAlgebraDifferential R E φ (ExteriorAlgebra.ιMulti R n v) * y +
          (-1 : R) ^ n •
            (ExteriorAlgebra.ιMulti R n v * koszulAlgebraDifferential R E φ y) := by
    intro n
    induction n with
    | zero =>
        intro v y
        simp [koszulAlgebraDifferential]
    | succ n ih =>
        intro v y
        rw [ExteriorAlgebra.ιMulti_succ_apply, mul_assoc,
          koszulAlgebraDifferential_mul_generator_aux,
          koszulAlgebraDifferential_mul_generator_aux, ih]
        rw [pow_succ]
        simp only [smul_add, smul_smul, mul_add, add_mul, neg_add, neg_mul,
          mul_neg, neg_smul, one_smul, Algebra.mul_smul_comm, mul_one, one_mul]
        simp only [mul_assoc]
        abel
  have hx : x ∈ Submodule.span R (Set.range (exteriorPower.ιMulti R n)) := by
    rw [exteriorPower.ιMulti_span R n E]
    trivial
  induction hx using Submodule.span_induction with
  | mem z hz =>
      obtain ⟨v, rfl⟩ := hz
      exact hι n v y
  | zero =>
      simp
  | add z₁ z₂ hz₁ hz₂ ih₁ ih₂ =>
      change koszulAlgebraDifferential R E φ
          (((z₁ : ExteriorAlgebra R E) + (z₂ : ExteriorAlgebra R E)) * y) =
        koszulAlgebraDifferential R E φ ((z₁ : ExteriorAlgebra R E) +
            (z₂ : ExteriorAlgebra R E)) * y +
          (-1 : R) ^ n •
            (((z₁ : ExteriorAlgebra R E) + (z₂ : ExteriorAlgebra R E)) *
              koszulAlgebraDifferential R E φ y)
      simp only [map_add, add_mul, mul_add, add_smul, smul_add]
      rw [ih₁, ih₂]
      abel
  | smul r z hz ih =>
      change koszulAlgebraDifferential R E φ
          (((r : R) • (z : ExteriorAlgebra R E)) * y) =
        koszulAlgebraDifferential R E φ ((r : R) • (z : ExteriorAlgebra R E)) * y +
          (-1 : R) ^ n •
            (((r : R) • (z : ExteriorAlgebra R E)) * koszulAlgebraDifferential R E φ y)
      rw [smul_mul_assoc, map_smul, smul_mul_assoc, map_smul]
      rw [ih]
      simp only [smul_mul_assoc, smul_smul, mul_assoc, smul_add]
      rw [mul_comm]

private theorem koszulAlgebraDifferential_comp_self_aux (R E : Type u) [CommRing R]
    [AddCommGroup E] [Module R E] (φ : E →ₗ[R] R) :
    (koszulAlgebraDifferential R E φ).comp (koszulAlgebraDifferential R E φ) = 0 := by
  apply LinearMap.ext
  intro x
  induction x using CliffordAlgebra.left_induction with
  | algebraMap =>
      simp [koszulAlgebraDifferential, Algebra.algebraMap_eq_smul_one]
  | add x y hx hy =>
      simp only [LinearMap.comp_apply] at hx hy ⊢
      simpa using congrArg₂ (· + ·) hx hy
  | ι_mul e x hx =>
      simp only [LinearMap.comp_apply]
      simp only [LinearMap.comp_apply] at hx
      rw [koszulAlgebraDifferential_mul_generator_aux,
        map_add, map_smul, koszulAlgebraDifferential_mul_generator_aux,
        koszulAlgebraDifferential_on_generator_aux]
      rw [← Algebra.smul_def, map_smul, hx]
      simp [smul_mul_assoc, smul_smul, mul_assoc, Algebra.mul_smul_comm]
      rw [Algebra.smul_def]
      exact add_neg_cancel _

/-! The canonical Koszul DGA structure. -/
def koszulDGA (R E : Type u) [CommRing R] [AddCommGroup E] [Module R E]
    (φ : E →ₗ[R] R) : KoszulDGA R E φ :=
  { differential := koszulAlgebraDifferential R E φ
    isDGA := by
      refine ⟨?_, ?_⟩
      · constructor
        · intro n m x y
          exact koszulAlgebraDifferential_mul_homogeneous_aux R E φ n x y
        · intro e
          exact koszulAlgebraDifferential_on_generator_aux R E φ e
      · exact koszulAlgebraDifferential_comp_self_aux R E φ }

theorem koszulDGA_isDGA (R E : Type u) [CommRing R] [AddCommGroup E]
    [Module R E] (φ : E →ₗ[R] R) :
    IsKoszulDGA R E φ (koszulDGA R E φ).differential := by
  exact (koszulDGA R E φ).isDGA

theorem koszulAlgebraDifferential_on_generator (R E : Type u) [CommRing R]
    [AddCommGroup E] [Module R E] (φ : E →ₗ[R] R) (e : E) :
    koszulAlgebraDifferential R E φ (ExteriorAlgebra.ι R e) =
      algebraMap R (ExteriorAlgebra R E) (φ e) := by
  exact koszulAlgebraDifferential_on_generator_aux R E φ e

theorem koszulAlgebraDifferential_unique (R E : Type u) [CommRing R]
    [AddCommGroup E] [Module R E] (φ : E →ₗ[R] R)
    (d : ExteriorAlgebra R E →ₗ[R] ExteriorAlgebra R E)
    (hd : IsKoszulDerivation R E φ d) :
    d = koszulAlgebraDifferential R E φ := by
  apply ExteriorAlgebra.lhom_ext
  intro n
  ext v
  induction n with
  | zero =>
      change d (ExteriorAlgebra.ιMulti R 0 v) =
        koszulAlgebraDifferential R E φ (ExteriorAlgebra.ιMulti R 0 v)
      simp only [ExteriorAlgebra.ιMulti_zero_apply]
      have h := hd.1 0 0 (exteriorPower.ιMulti R 0 (0 : Fin 0 → E))
        (exteriorPower.ιMulti R 0 (0 : Fin 0 → E))
      simp only [exteriorPower.ιMulti_apply_coe, pow_zero, one_smul] at h
      have hd0 : d 1 = 0 := by
        apply_fun (fun z => z - d 1) at h
        simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using h.symm
      rw [hd0]
      simp [koszulAlgebraDifferential]
  | succ n ih =>
      change d (ExteriorAlgebra.ιMulti R (n + 1) v) =
        koszulAlgebraDifferential R E φ (ExteriorAlgebra.ιMulti R (n + 1) v)
      rw [ExteriorAlgebra.ιMulti_succ_apply]
      have hd' := hd.1 1 n (exteriorPower.ιMulti R 1 (fun _ => v 0))
        (exteriorPower.ιMulti R n (Matrix.vecTail v))
      have hι1 :
          (exteriorPower.ιMulti R 1 (fun _ => v 0) :
            ExteriorAlgebra R E) = ExteriorAlgebra.ι R (v 0) := by
        simp [exteriorPower.ιMulti_apply_coe, ExteriorAlgebra.ιMulti_succ_apply]
      rw [hι1] at hd'
      have hD := koszulAlgebraDifferential_mul_generator_aux R E φ (v 0)
        (ExteriorAlgebra.ιMulti R n (Matrix.vecTail v))
      have ih' := ih (Matrix.vecTail v)
      change d (ExteriorAlgebra.ιMulti R n (Matrix.vecTail v)) =
        koszulAlgebraDifferential R E φ (ExteriorAlgebra.ιMulti R n
          (Matrix.vecTail v)) at ih'
      calc
        d (ExteriorAlgebra.ι R (v 0) * ExteriorAlgebra.ιMulti R n
            (Matrix.vecTail v)) =
            d (ExteriorAlgebra.ι R (v 0)) *
                ExteriorAlgebra.ιMulti R n (Matrix.vecTail v) +
              (-1 : R) • (ExteriorAlgebra.ι R (v 0) *
                d (ExteriorAlgebra.ιMulti R n (Matrix.vecTail v))) := by
                  simpa using hd'
        _ = koszulAlgebraDifferential R E φ (ExteriorAlgebra.ι R (v 0)) *
              ExteriorAlgebra.ιMulti R n (Matrix.vecTail v) +
            (-1 : R) • (ExteriorAlgebra.ι R (v 0) *
              koszulAlgebraDifferential R E φ
                (ExteriorAlgebra.ιMulti R n (Matrix.vecTail v))) := by
                  rw [hd.2 (v 0), koszulAlgebraDifferential_on_generator_aux, ih']
        _ = koszulAlgebraDifferential R E φ
              (ExteriorAlgebra.ι R (v 0) *
                ExteriorAlgebra.ιMulti R n (Matrix.vecTail v)) := by
                  symm
                  exact hD

/-! ## The complex and sequences -/

/-- The Koszul term in an arbitrary integer degree; negative degrees are zero. -/
noncomputable def koszulTermZ (R E : Type u) [CommRing R] [AddCommGroup E]
    [Module R E] (n : ℤ) : ModuleCat.{u} R :=
  if 0 ≤ n then ModuleCat.of R (⋀[R]^(Int.toNat n) E)
  else ModuleCat.of R (Fin 0 → R)

/-- The differential of the integer-indexed Koszul complex. -/
noncomputable def koszulDifferentialZ (R E : Type u) [CommRing R] [AddCommGroup E]
    [Module R E] (φ : E →ₗ[R] R) (n : ℤ) :
    koszulTermZ R E (n + 1) ⟶ koszulTermZ R E n := by
  by_cases hn : 0 ≤ n
  · have hn1 : 0 ≤ n + 1 := by omega
    have hnat : Int.toNat (n + 1) = Int.toNat n + 1 := by
      exact Int.toNat_add hn (by omega)
    simp only [koszulTermZ, if_pos hn1, if_pos hn]
    rw [hnat]
    exact ModuleCat.ofHom (koszulDifferential R E φ (Int.toNat n))
  · by_cases hn1 : 0 ≤ n + 1
    · simp only [koszulTermZ, if_pos hn1, if_neg hn]
      exact 0
    · simp only [koszulTermZ, if_neg hn1, if_neg hn]
      exact 0

private theorem koszulDifferential_comp_aux (R E : Type u) [CommRing R]
    [AddCommGroup E] [Module R E] (φ : E →ₗ[R] R) (n : ℕ) :
    ModuleCat.ofHom (koszulDifferential R E φ (n + 1)) ≫
        ModuleCat.ofHom (koszulDifferential R E φ n) = 0 := by
  have h_restrict (m : ℕ) :
      (Submodule.subtype (⋀[R]^m E)).comp
          (koszulDifferential R E φ m) =
        (koszulAlgebraDifferential R E φ).comp
          (Submodule.subtype (⋀[R]^(m + 1) E)) := by
    apply exteriorPower.linearMap_ext
    ext w
    simp only [LinearMap.compAlternatingMap_apply, LinearMap.comp_apply]
    rw [koszulDifferential_apply_ιMulti]
    change _ = koszulAlgebraDifferential R E φ
      (ExteriorAlgebra.ιMulti R (m + 1) w)
    rw [koszulAlgebraDifferential_apply_ιMulti]
    simp only [map_sum, map_smul]
    rfl
  rw [← ModuleCat.ofHom_comp]
  apply ModuleCat.hom_ext
  ext v
  change ((Submodule.subtype (⋀[R]^n E)).comp
      (koszulDifferential R E φ n))
        (koszulDifferential R E φ (n + 1)
          (exteriorPower.ιMulti R (n + 1 + 1) v)) = 0
  rw [h_restrict n]
  change (koszulAlgebraDifferential R E φ)
      ((Submodule.subtype (⋀[R]^(n + 1) E)).comp
        (koszulDifferential R E φ (n + 1))
          (exteriorPower.ιMulti R (n + 1 + 1) v)) = 0
  rw [h_restrict (n + 1)]
  change ((koszulAlgebraDifferential R E φ).comp
      (koszulAlgebraDifferential R E φ))
        ((Submodule.subtype (⋀[R]^(n + 1 + 1) E))
          (exteriorPower.ιMulti R (n + 1 + 1) v)) = 0
  rw [koszulAlgebraDifferential_comp_self_aux]
  simp

theorem koszulDifferentialZ_comp (R E : Type u) [CommRing R] [AddCommGroup E]
    [Module R E] (φ : E →ₗ[R] R) (n : ℤ) :
    koszulDifferentialZ R E φ (n + 1) ≫ koszulDifferentialZ R E φ n = 0 := by
  cases n with
  | ofNat k =>
      have hk0 : 0 ≤ Int.ofNat k := by simp
      have hk1 : 0 ≤ Int.ofNat k + 1 := by omega
      simp only [koszulDifferentialZ, koszulTermZ, hk0, hk1]
      exact koszulDifferential_comp_aux R E φ k
  | negSucc k =>
      cases k with
      | zero =>
          have hzero : koszulDifferentialZ R E φ (Int.negSucc 0) = 0 := by
            simp only [koszulDifferentialZ, koszulTermZ]
            apply ModuleCat.hom_ext
            ext x
            rfl
          rw [hzero]
          simp
      | succ k =>
          have hk1 : ¬ 0 ≤ Int.negSucc (k + 1) + 1 := by omega
          simp only [koszulDifferentialZ, koszulTermZ, hk1]
          apply ModuleCat.hom_ext
          ext x
          rfl

theorem koszulDifferential_comp (R E : Type u) [CommRing R] [AddCommGroup E]
    [Module R E] (φ : E →ₗ[R] R) (n : ℕ) :
    ModuleCat.ofHom (koszulDifferential R E φ (n + 1)) ≫
        ModuleCat.ofHom (koszulDifferential R E φ n) = 0 := by
  exact koszulDifferential_comp_aux R E φ n

/-- The homological Koszul complex, indexed over `ℤ` and zero in negative degrees. -/
noncomputable def koszulComplex (R E : Type u) [CommRing R] [AddCommGroup E]
    [Module R E] (φ : E →ₗ[R] R) : ChainComplex (ModuleCat.{u} R) ℤ :=
  ChainComplex.of (fun n => koszulTermZ R E n) (fun n => koszulDifferentialZ R E φ n)
    (koszulDifferentialZ_comp R E φ)

/-- The nonnegative indexing of the same construction, used by the canonical
`down ℕ` total tensor complex. -/
noncomputable def koszulComplexNat (R E : Type u) [CommRing R] [AddCommGroup E]
    [Module R E] (φ : E →ₗ[R] R) : ChainComplex (ModuleCat.{u} R) ℕ :=
  ChainComplex.of (fun n => ModuleCat.of R (⋀[R]^n E))
    (fun n => ModuleCat.ofHom (koszulDifferential R E φ n))
    (koszulDifferential_comp R E φ)

theorem koszulComplex_X_nonnegative (R E : Type u) [CommRing R] [AddCommGroup E]
    [Module R E] (φ : E →ₗ[R] R) (n : ℕ) :
    (koszulComplex R E φ).X (n : ℤ) = ModuleCat.of R (⋀[R]^n E) := by
  simp [koszulComplex, koszulTermZ]

theorem koszulComplex_X_negative (R E : Type u) [CommRing R] [AddCommGroup E]
    [Module R E] (φ : E →ₗ[R] R) (n : ℤ) (hn : n < 0) :
    IsZero ((koszulComplex R E φ).X n) := by
  simp [koszulComplex, koszulTermZ, not_le_of_gt hn]
  infer_instance

theorem koszulComplex_d_nonnegative (R E : Type u) [CommRing R] [AddCommGroup E]
    [Module R E] (φ : E →ₗ[R] R) (n : ℕ) :
    (koszulComplex R E φ).d (n + 1 : ℤ) n =
      ModuleCat.ofHom (koszulDifferential R E φ n) := by
  simp [koszulComplex, ChainComplex.of_d, koszulDifferentialZ]
  apply ModuleCat.hom_ext
  ext x
  rfl

/-- The map associated with a finite sequence, using the standard free module. -/
def sequenceLinearMap (R : Type u) [CommRing R] (r : ℕ) (f : Fin r → R) :
    (Fin r → R) →ₗ[R] R :=
  { toFun := fun x => ∑ i, x i * f i
    map_add' := by
      intro x y
      simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]
    map_smul' := by
      intro a x
      simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum, RingHom.id_apply]
      apply Finset.sum_congr rfl
      intro i hi
      rw [mul_assoc] }

@[simp]
theorem sequenceLinearMap_apply (R : Type u) [CommRing R] (r : ℕ) (f : Fin r → R)
    (x : Fin r → R) : sequenceLinearMap R r f x = ∑ i, x i * f i := rfl

/-- The Koszul complex of a sequence. -/
noncomputable def koszulComplexOn (R : Type u) [CommRing R] (r : ℕ) (f : Fin r → R) :
    ChainComplex (ModuleCat.{u} R) ℤ :=
  koszulComplex R (Fin r → R) (sequenceLinearMap R r f)

noncomputable def koszulComplexOnNat (R : Type u) [CommRing R] (r : ℕ) (f : Fin r → R) :
    ChainComplex (ModuleCat.{u} R) ℕ :=
  koszulComplexNat R (Fin r → R) (sequenceLinearMap R r f)

/-- The standard insertion of a final element into a finite sequence. -/
def sequenceAppendLast (r : ℕ) (f : Fin r → R) (g : R) : Fin (r + 1) → R :=
  Fin.lastCases g f

/-! ## Local finite-free presentations and functoriality -/

/-- The canonical localization of a Koszul map at a basic open. -/
noncomputable def localizedKoszulMap
    (R E : Type u) [CommRing R] [AddCommGroup E] [Module R E]
    (φ : E →ₗ[R] R) (a : R) :
    LocalizedModule.Away a E →ₗ[Localization.Away a]
      LocalizedModule.Away a R :=
  LocalizedModule.map (Submonoid.powers a) φ

/-- Data for a local finite-free presentation of a Koszul map.  The target is
the localized copy of `R`; it is the module-theoretic form of the localized
ring target. -/
structure KoszulLocalSequencePresentation (R E : Type u) [CommRing R]
    [AddCommGroup E] [Module R E] (φ : E →ₗ[R] R) (a : R) where
  rank : ℕ
  basis : LocalizedModule.Away a E ≃ₗ[Localization.Away a]
    (Fin rank →₀ Localization.Away a)
  sequence : Fin rank → LocalizedModule.Away a R
  map_on_basis : ∀ i,
    localizedKoszulMap R E φ a (basis.symm (Finsupp.single i 1)) = sequence i

theorem koszul_finiteLocallyFree_local
    (R E : Type u) [CommRing R] [AddCommGroup E] [Module R E]
    (φ : E →ₗ[R] R)
    (hE : Formalization.Books.Algebra.Unit78.FiniteLocallyFree R E) :
    ∃ s : Set R, Ideal.span s = ⊤ ∧
      ∀ a ∈ s, Nonempty (KoszulLocalSequencePresentation R E φ a) := by
  rcases hE with ⟨s, hs, h⟩
  refine ⟨s, hs, ?_⟩
  intro a ha
  have hfree : Module.Free (Localization.Away a) (LocalizedModule.Away a E) :=
    h a ha |>.2
  have hfinite : Module.Finite (Localization.Away a) (LocalizedModule.Away a E) :=
    h a ha |>.1
  let ι := @Module.Free.ChooseBasisIndex (Localization.Away a)
    (LocalizedModule.Away a E) _ _ _ hfree
  let b : Module.Basis ι (Localization.Away a) (LocalizedModule.Away a E) :=
    @Module.Free.chooseBasis (Localization.Away a) (LocalizedModule.Away a E) _ _ _ hfree
  let fintype : Fintype ι :=
    @Module.Free.ChooseBasisIndex.fintype (Localization.Away a)
      (LocalizedModule.Away a E) _ _ _ hfree hfinite
  let e : ι ≃ Fin (@Fintype.card ι fintype) := @Fintype.equivFin ι fintype
  let b' := b.reindex e
  let basis : LocalizedModule.Away a E ≃ₗ[Localization.Away a]
      (Fin (@Fintype.card ι fintype) →₀ Localization.Away a) := b'.repr
  let sequence : Fin (@Fintype.card ι fintype) → LocalizedModule.Away a R :=
    fun i => localizedKoszulMap R E φ a (basis.symm (Finsupp.single i 1))
  exact ⟨{
    rank := @Fintype.card ι fintype
    basis := basis
    sequence := sequence
    map_on_basis := by intro i; rfl
  }⟩

/-- The exterior-algebra map induced by a linear map of generators. -/
def koszulAlgebraMap (R E E' : Type u) [CommRing R] [AddCommGroup E]
    [AddCommGroup E'] [Module R E] [Module R E'] (ψ : E →ₗ[R] E') :
    ExteriorAlgebra R E →ₐ[R] ExteriorAlgebra R E' :=
  ExteriorAlgebra.map ψ

/-- Data of the DGA map induced by a map of Koszul generators. -/
structure KoszulDGAHom (R E E' : Type u) [CommRing R] [AddCommGroup E]
    [AddCommGroup E'] [Module R E] [Module R E']
    (φ : E →ₗ[R] R) (φ' : E' →ₗ[R] R) (ψ : E →ₗ[R] E') where
  algebraMap : ExteriorAlgebra R E →ₐ[R] ExteriorAlgebra R E'
  algebraMap_eq_induced : algebraMap = koszulAlgebraMap R E E' ψ
  differential_commutes :
    algebraMap.toLinearMap.comp (koszulAlgebraDifferential R E φ) =
      (koszulAlgebraDifferential R E' φ').comp algebraMap.toLinearMap

theorem koszul_functorial
    (R E E' : Type u) [CommRing R] [AddCommGroup E] [AddCommGroup E']
    [Module R E] [Module R E'] (φ : E →ₗ[R] R) (φ' : E' →ₗ[R] R)
    (ψ : E →ₗ[R] E') (h : φ'.comp ψ = φ) :
    Nonempty (KoszulDGAHom R E E' φ φ' ψ) := by
  refine ⟨{
    algebraMap := koszulAlgebraMap R E E' ψ
    algebraMap_eq_induced := rfl
    differential_commutes := ?_
  }⟩
  apply LinearMap.ext
  intro x
  induction x using CliffordAlgebra.left_induction with
  | algebraMap =>
      simp [koszulAlgebraMap, koszulAlgebraDifferential]
  | add x y hx hy =>
      simp only [LinearMap.comp_apply, map_add] at hx hy ⊢
      simpa using congrArg₂ (· + ·) hx hy
  | ι_mul e x hx =>
      simp only [LinearMap.comp_apply]
      change (koszulAlgebraMap R E E' ψ)
          (koszulAlgebraDifferential R E φ (ExteriorAlgebra.ι R x * e)) =
        koszulAlgebraDifferential R E' φ'
          ((koszulAlgebraMap R E E' ψ) (ExteriorAlgebra.ι R x * e))
      rw [koszulAlgebraDifferential_mul_generator_aux]
      rw [map_add, map_smul, map_mul, map_mul, map_mul]
      simp only [koszulAlgebraMap, ExteriorAlgebra.map_apply_ι]
      rw [koszulAlgebraDifferential_mul_generator_aux]
      rw [koszulAlgebraDifferential_on_generator_aux,
        koszulAlgebraDifferential_on_generator_aux]
      have hx' :
          (koszulAlgebraMap R E E' ψ) (koszulAlgebraDifferential R E φ e) =
            koszulAlgebraDifferential R E' φ'
              ((koszulAlgebraMap R E E' ψ) e) := by
        simpa [koszulAlgebraMap] using hx
      have hx'' :
          (ExteriorAlgebra.map ψ) (koszulAlgebraDifferential R E φ e) =
            koszulAlgebraDifferential R E' φ' ((ExteriorAlgebra.map ψ) e) := by
        simpa [koszulAlgebraMap] using hx'
      rw [hx'']
      have hxe : φ' (ψ x) = φ x := LinearMap.congr_fun h x
      simp [hxe, Algebra.smul_def]

/-- Data of an isomorphism between two Koszul DGAs. -/
structure KoszulDGAIso (R E E' : Type u) [CommRing R] [AddCommGroup E]
    [AddCommGroup E'] [Module R E] [Module R E']
    (φ : E →ₗ[R] R) (φ' : E' →ₗ[R] R) (ψ : E ≃ₗ[R] E') where
  algebraEquiv : ExteriorAlgebra R E ≃ₐ[R] ExteriorAlgebra R E'
  algebraEquiv_eq_induced :
    algebraEquiv.toAlgHom = koszulAlgebraMap R E E' ψ.toLinearMap
  differential_commutes :
    algebraEquiv.toLinearMap.comp (koszulAlgebraDifferential R E φ) =
      (koszulAlgebraDifferential R E' φ').comp algebraEquiv.toLinearMap

/-! The change-of-basis sequence associated with an invertible matrix.  The
source uses the rows of the matrix: `g i = ∑ j, X i j * f j`. -/
noncomputable def matrixChangeSequence (R : Type u) [CommRing R] (r : ℕ)
    (X : Matrix (Fin r) (Fin r) R) (f : Fin r → R) : Fin r → R :=
  fun i => ∑ j, X i j * f j

private theorem koszulDifferential_map_change_basis
    (R : Type u) [CommRing R] (r : ℕ) (f g : Fin r → R)
    (e : (Fin r → R) ≃ₗ[R] (Fin r → R))
    (h : (sequenceLinearMap R r g) =
      (sequenceLinearMap R r f).comp e.toLinearMap) (n : ℕ) :
    (koszulDifferential R (Fin r → R) (sequenceLinearMap R r g) n).comp
        (exteriorPower.map (n + 1) e.symm.toLinearMap) =
      (exteriorPower.map n e.symm.toLinearMap).comp
        (koszulDifferential R (Fin r → R) (sequenceLinearMap R r f) n) := by
  apply exteriorPower.linearMap_ext
  apply AlternatingMap.ext
  intro v
  have hfun (x : Fin r → R) :
      sequenceLinearMap R r g (e.symm.toLinearMap x) = sequenceLinearMap R r f x := by
    simpa using LinearMap.congr_fun h (e.symm x)
  have hremove (i : Fin (n + 1)) :
      i.removeNth (fun j => e.symm.toLinearMap (v j)) =
        (fun j => e.symm.toLinearMap (i.removeNth v j)) := by
    ext j
    rfl
  simp only [LinearMap.compAlternatingMap_apply, LinearMap.comp_apply]
  change koszulDifferential R (Fin r → R) (sequenceLinearMap R r g) n
      (exteriorPower.map (n + 1) e.symm.toLinearMap
        (exteriorPower.ιMulti R (n + 1) v)) =
    exteriorPower.map n e.symm.toLinearMap
      (koszulDifferential R (Fin r → R) (sequenceLinearMap R r f) n
        (exteriorPower.ιMulti R (n + 1) v))
  rw [exteriorPower.map_apply_ιMulti,
    koszulDifferential_apply_ιMulti, koszulDifferential_apply_ιMulti]
  simp only [map_sum, map_smul, exteriorPower.map_apply_ιMulti]
  simp only [Function.comp_apply]
  apply Finset.sum_congr rfl
  intro i hi
  have hcoef :
      sequenceLinearMap R r g (e.symm.toLinearMap (v i)) =
        sequenceLinearMap R r f (v i) :=
    hfun (v i)
  rw [hcoef]
  congr 2

private noncomputable def exteriorPowerLinearEquiv
    (R : Type u) [CommRing R] (M : Type u) [AddCommGroup M] [Module R M]
    (n : ℕ) (e : M ≃ₗ[R] M) :
    (⋀[R]^n M) ≃ₗ[R] (⋀[R]^n M) :=
  LinearEquiv.ofLinear (exteriorPower.map n e.symm.toLinearMap)
    (exteriorPower.map n e.toLinearMap) (by
      rw [← exteriorPower.map_comp, e.symm_comp, exteriorPower.map_id]) (by
      rw [← exteriorPower.map_comp, e.comp_symm, exteriorPower.map_id])

theorem koszul_change_basis
    (R : Type u) [CommRing R] (r : ℕ) (f : Fin r → R)
    (e : (Fin r → R) ≃ₗ[R] (Fin r → R))
    (g : Fin r → R)
    (h : (sequenceLinearMap R r g) =
      (sequenceLinearMap R r f).comp e.toLinearMap) :
    Nonempty (koszulComplexOn R r f ≅ koszulComplexOn R r g) := by
  let component : ∀ n : ℤ,
      (koszulComplexOn R r f).X n ≅ (koszulComplexOn R r g).X n := fun n => by
    by_cases hn : 0 ≤ n
    · simp only [koszulComplexOn, koszulComplex, koszulTermZ, if_pos hn]
      exact (exteriorPowerLinearEquiv R (Fin r → R) (Int.toNat n) e).toModuleIso
    · simp only [koszulComplexOn, koszulComplex, koszulTermZ, if_neg hn]
      exact Iso.refl _
  refine ⟨HomologicalComplex.Hom.isoOfComponents component ?_⟩
  intro i j hij
  simp only [ComplexShape.down_Rel] at hij
  subst i
  by_cases hj : 0 ≤ j
  · have hnext : 0 ≤ j + 1 := by omega
    have hj' : j = (Int.toNat j : ℤ) := by omega
    rw [hj']
    simp only [koszulComplexOn]
    rw [koszulComplex_d_nonnegative R (Fin r → R) (sequenceLinearMap R r g)
      (Int.toNat j), koszulComplex_d_nonnegative R (Fin r → R)
      (sequenceLinearMap R r f) (Int.toNat j)]
    have hd := koszulDifferential_map_change_basis R r f g e h (Int.toNat j)
    simp [component, koszulComplexOn, koszulComplex, koszulTermZ,
      koszulDifferentialZ, hj, hnext]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    let x' : ⋀[R]^(Int.toNat j + 1) (Fin r → R) := x
    change koszulDifferential R (Fin r → R) (sequenceLinearMap R r g)
        (Int.toNat j)
        ((exteriorPower.map (Int.toNat j + 1) e.symm.toLinearMap) x') =
      (exteriorPower.map (Int.toNat j) e.symm.toLinearMap)
        (koszulDifferential R (Fin r → R) (sequenceLinearMap R r f)
          (Int.toNat j) x')
    exact LinearMap.congr_fun hd x'
  · by_cases hnext : 0 ≤ j + 1
    · have hj' : j = -1 := by omega
      subst j
      have hdg : (koszulComplexOn R r g).d (0 : ℤ) (-1 : ℤ) = 0 := by
        change koszulDifferentialZ R (Fin r → R)
            (sequenceLinearMap R r g) (-1 : ℤ) = 0
        simp only [koszulDifferentialZ, koszulTermZ]
        apply ModuleCat.hom_ext
        ext x
        rfl
      have hdf : (koszulComplexOn R r f).d (0 : ℤ) (-1 : ℤ) = 0 := by
        change koszulDifferentialZ R (Fin r → R)
            (sequenceLinearMap R r f) (-1 : ℤ) = 0
        simp only [koszulDifferentialZ, koszulTermZ]
        apply ModuleCat.hom_ext
        ext x
        rfl
      rw [show (-1 : ℤ) + 1 = 0 by norm_num]
      rw [hdg, hdf]
      simp [component]
    · have hdg : (koszulComplexOn R r g).d (j + 1) j = 0 := by
        simp [koszulComplexOn, koszulComplex, ChainComplex.of_d,
          koszulDifferentialZ, koszulTermZ, hj, hnext]
        apply ModuleCat.hom_ext
        ext x
        have hsub : Subsingleton
            (↥(if 0 ≤ j then ModuleCat.of R (⋀[R]^(Int.toNat j) (Fin r → R))
              else ModuleCat.of R (Fin 0 → R))) := by
          split
          · rename_i hj'
            exact (hj hj').elim
          · infer_instance
        exact @Subsingleton.elim _ hsub _ _
      have hdf : (koszulComplexOn R r f).d (j + 1) j = 0 := by
        simp [koszulComplexOn, koszulComplex, ChainComplex.of_d,
          koszulDifferentialZ, koszulTermZ, hj, hnext]
        apply ModuleCat.hom_ext
        ext x
        have hsub : Subsingleton
            (↥(if 0 ≤ j then ModuleCat.of R (⋀[R]^(Int.toNat j) (Fin r → R))
              else ModuleCat.of R (Fin 0 → R))) := by
          split
          · rename_i hj'
            exact (hj hj').elim
          · infer_instance
        exact @Subsingleton.elim _ hsub _ _
      rw [hdg, hdf]
      simp [component]

theorem koszul_change_basis_matrix
    (R : Type u) [CommRing R] (r : ℕ) (X : Matrix (Fin r) (Fin r) R)
    [Invertible X] (f : Fin r → R) :
    Nonempty (koszulComplexOn R r f ≅
      koszulComplexOn R r (matrixChangeSequence R r X f)) := by
  let e : (Fin r → R) ≃ₗ[R] (Fin r → R) :=
    Matrix.toLin'OfInv
      (M := Matrix.transpose (⅟ X)) (M' := Matrix.transpose X) (by
        rw [← Matrix.transpose_mul, mul_invOf_self, Matrix.transpose_one]) (by
        rw [← Matrix.transpose_mul, invOf_mul_self, Matrix.transpose_one])
  have hseq : sequenceLinearMap R r (matrixChangeSequence R r X f) =
      (sequenceLinearMap R r f).comp e.toLinearMap := by
    apply LinearMap.ext
    intro x
    simp [sequenceLinearMap, matrixChangeSequence, e, Matrix.toLin'OfInv,
      Matrix.toLin'_apply, Matrix.mulVec, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i hi
    change (∑ j, x j * (X j i * f i)) =
      (∑ j, X j i * x j) * f i
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  exact koszul_change_basis R r f e (matrixChangeSequence R r X f) hseq

/-! ## Homotopies and annihilation -/

/-- Multiplication by a scalar on every term of a complex. -/
noncomputable def scalarChainMap {α : Type*} [AddRightCancelSemigroup α] [One α]
    [DecidableEq α] (R : Type u) [CommRing R]
    (A : ChainComplex (ModuleCat.{u} R) α) (a : R) : A ⟶ A :=
  ChainComplex.ofHom (fun n => a • 𝟙 (A.X n)) (by
    intro n
    simp)

/-- The abstract Koszul contracting homotopy. -/
private noncomputable def koszulWedge
    (R E : Type u) [CommRing R] [AddCommGroup E] [Module R E]
    (e : E) (n : ℕ) : (⋀[R]^n E) →ₗ[R] (⋀[R]^(n + 1) E) :=
  exteriorPower.alternatingMapLinearEquiv
    ((exteriorPower.ιMulti R (n + 1)).curryLeft e)

private theorem koszulWedge_apply_ιMulti
    (R E : Type u) [CommRing R] [AddCommGroup E] [Module R E]
    (e : E) (n : ℕ) (v : Fin n → E) :
    koszulWedge R E e n (exteriorPower.ιMulti R n v) =
      exteriorPower.ιMulti R (n + 1) (Matrix.vecCons e v) := by
  rw [koszulWedge, exteriorPower.alternatingMapLinearEquiv_apply_ιMulti]
  rfl

private noncomputable def koszulHomotopyPrev
    (R E : Type u) [CommRing R] [AddCommGroup E] [Module R E]
    (φ : E →ₗ[R] R) (e : E) (n : ℕ) :
    (⋀[R]^n E) →ₗ[R] (⋀[R]^n E) :=
  match n with
  | 0 => 0
  | n + 1 => (koszulWedge R E e n).comp (koszulDifferential R E φ n)

private theorem koszulHomotopy_identity
    (R E : Type u) [CommRing R] [AddCommGroup E] [Module R E]
    (φ : E →ₗ[R] R) (e : E) (n : ℕ) :
    (koszulDifferential R E φ n).comp (koszulWedge R E e n) +
        koszulHomotopyPrev R E φ e n =
      (φ e) • LinearMap.id := by
  apply exteriorPower.linearMap_ext
  apply AlternatingMap.ext
  intro v
  cases n with
  | zero =>
      simp only [koszulHomotopyPrev, LinearMap.compAlternatingMap_apply,
        LinearMap.add_apply, LinearMap.comp_apply, LinearMap.smul_apply,
        LinearMap.id_apply]
      rw [koszulWedge_apply_ιMulti, koszulDifferential_apply_ιMulti]
      simp
  | succ n =>
      simp only [koszulHomotopyPrev, LinearMap.compAlternatingMap_apply,
        LinearMap.add_apply, LinearMap.comp_apply, LinearMap.smul_apply,
        LinearMap.id_apply]
      rw [koszulWedge_apply_ιMulti, koszulDifferential_apply_ιMulti,
        koszulDifferential_apply_ιMulti]
      simp only [map_sum, map_smul]
      simp_rw [koszulWedge_apply_ιMulti]
      have hremove (i : Fin (n + 1)) :
          i.succ.removeNth (Matrix.vecCons e v) =
            Matrix.vecCons e (i.removeNth v) := by
        ext j
        simpa [Matrix.vecCons, Fin.removeNth, Function.comp_apply] using
          congrFun (Fin.cons_comp_succ_succAbove e v i) j
      rw [Fin.sum_univ_succ]
      simp_rw [hremove]
      simp [Matrix.vecCons, pow_succ]
      rw [add_assoc, ← Finset.sum_add_distrib]
      simp only [smul_smul, neg_mul, neg_smul, neg_add_cancel, add_zero,
        Finset.sum_const_zero]

theorem koszul_homotopy_abstract
    (R E : Type u) [CommRing R] [AddCommGroup E] [Module R E]
    (φ : E →ₗ[R] R) (e : E) :
    Nonempty (Homotopy
      (scalarChainMap R (koszulComplex R E φ) (φ e)) 0) := by
  let h : ∀ i j, (ComplexShape.down ℤ).Rel j i →
      ModuleCat.Hom ((koszulComplex R E φ).X i) ((koszulComplex R E φ).X j) := by
    intro i j hij
    change i + 1 = j at hij
    subst j
    by_cases hi : 0 ≤ i
    · have hi1 : 0 ≤ i + 1 := by omega
      have hnat : Int.toNat (i + 1) = Int.toNat i + 1 := by
        exact Int.toNat_add hi (by omega)
      simp only [koszulComplex, koszulTermZ, if_pos hi, if_pos hi1]
      rw [hnat]
      exact ModuleCat.ofHom (koszulWedge R E e (Int.toNat i))
    · by_cases hi1 : 0 ≤ i + 1
      · simp only [koszulComplex, koszulTermZ, if_neg hi, if_pos hi1]
        exact ModuleCat.ofHom 0
      · simp only [koszulComplex, koszulTermZ, if_neg hi, if_neg hi1]
        exact ModuleCat.ofHom 0
  have hcat (n : ℕ) :
      (φ e) • 𝟙 (ModuleCat.of R (⋀[R]^n E)) =
        ModuleCat.ofHom
          ((koszulDifferential R E φ n).comp (koszulWedge R E e n) +
            koszulHomotopyPrev R E φ e n) := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    have hid := koszulHomotopy_identity R E φ e n
    simpa [add_comm] using (LinearMap.congr_fun hid x).symm
  have hmap : scalarChainMap R (koszulComplex R E φ) (φ e) =
      Homotopy.nullHomotopicMap' (C := koszulComplex R E φ)
      (D := koszulComplex R E φ) (c := ComplexShape.down ℤ) h := by
    apply HomologicalComplex.Hom.ext
    funext n
    cases n with
    | ofNat n =>
        cases n with
        | zero =>
            have h21 : (ComplexShape.down ℤ).Rel (1 : ℤ) 0 := by
              change (0 : ℤ) + 1 = 1
              rfl
            have h10 : (ComplexShape.down ℤ).Rel (0 : ℤ) (-1 : ℤ) := by
              change (-1 : ℤ) + 1 = 0
              norm_num
            change (scalarChainMap R (koszulComplex R E φ) (φ e)).f (0 : ℤ) =
              (Homotopy.nullHomotopicMap' (C := koszulComplex R E φ)
                (D := koszulComplex R E φ) (c := ComplexShape.down ℤ) h).f 0
            rw [Homotopy.nullHomotopicMap'_f (c := ComplexShape.down ℤ)
              h21 h10]
            have hdneg : (koszulComplex R E φ).d (0 : ℤ) (-1 : ℤ) = 0 := by
              change koszulDifferentialZ R E φ (-1 : ℤ) = 0
              simp only [koszulDifferentialZ, koszulTermZ]
              apply ModuleCat.hom_ext
              ext x
              rfl
            rw [hdneg]
            have h01 : h (0 : ℤ) 1 h21 =
                ModuleCat.ofHom (koszulWedge R E e 0) := by
              apply ModuleCat.hom_ext
              ext x
              rfl
            have hd01 : (koszulComplex R E φ).d (1 : ℤ) 0 =
                ModuleCat.ofHom (koszulDifferential R E φ 0) := by
              simpa using koszulComplex_d_nonnegative R E φ 0
            have hscalar0 :
                (scalarChainMap R (koszulComplex R E φ) (φ e)).f (0 : ℤ) =
                  (φ e) • 𝟙 (ModuleCat.of R (⋀[R]^0 E)) := by
              simp [scalarChainMap, koszulComplex, koszulTermZ]
              rfl
            rw [hscalar0]
            apply ModuleCat.hom_ext
            apply LinearMap.ext
            intro x
            have hc := congrArg ModuleCat.Hom.hom (hcat 0)
            have hs : ModuleCat.Hom.hom
                ((φ e) • 𝟙 (ModuleCat.of R (⋀[R]^0 E))) =
                (φ e) • LinearMap.id := by
              ext y
              rfl
            rw [hs]
            have hx := LinearMap.congr_fun hc x
            rw [hs] at hx
            have hzero :
                (0 : (koszulComplex R E φ).X (0 : ℤ) ⟶
                  (koszulComplex R E φ).X (-1 : ℤ)) ≫ h (-1) 0 h10 = 0 := by
              simp
            have hcomp0 :
                0 ≫ h (-1) 0 h10 +
                    h 0 1 h21 ≫ (koszulComplex R E φ).d (1 : ℤ) 0 =
                  h 0 1 h21 ≫ (koszulComplex R E φ).d (1 : ℤ) 0 := by
              rw [hzero, zero_add]
            have hcomp1 :
                h 0 1 h21 ≫ (koszulComplex R E φ).d (1 : ℤ) 0 =
                  ModuleCat.ofHom (koszulWedge R E e 0) ≫
                    ModuleCat.ofHom (koszulDifferential R E φ 0) := by
              rw [h01, hd01]
              rfl
            rw [hcomp0, hcomp1]
            have hcomp :
                (ModuleCat.Hom.hom
                    (ModuleCat.ofHom
                      (koszulDifferential R E φ 0 ∘ₗ
                      koszulWedge R E e 0 +
                        koszulHomotopyPrev R E φ e 0))) x =
                (ModuleCat.Hom.hom
                    (ModuleCat.ofHom (koszulWedge R E e 0) ≫
                      ModuleCat.ofHom (koszulDifferential R E φ 0))) x := by
              simp only [koszulHomotopyPrev, add_zero]
              change koszulDifferential R E φ 0
                  (koszulWedge R E e 0 x) =
                koszulDifferential R E φ 0
                  (koszulWedge R E e 0 x)
              rfl
            exact hx.trans hcomp
        | succ n =>
            have h21 : (ComplexShape.down ℤ).Rel (((n + 1) + 1 : ℕ) : ℤ)
                ((n + 1 : ℕ) : ℤ) := by
              simp [ComplexShape.down_Rel]
            have h10 : (ComplexShape.down ℤ).Rel ((n + 1 : ℕ) : ℤ) (n : ℤ) := by
              simp [ComplexShape.down_Rel]
            have h10' : h (n : ℤ) ((n + 1 : ℕ) : ℤ) h10 =
                ModuleCat.ofHom (koszulWedge R E e n) := by
              apply ModuleCat.hom_ext
              ext x
              rfl
            have h21' : h ((n + 1 : ℕ) : ℤ) (((n + 1) + 1 : ℕ) : ℤ) h21 =
                ModuleCat.ofHom (koszulWedge R E e (n + 1)) := by
              apply ModuleCat.hom_ext
              ext x
              rfl
            change (scalarChainMap R (koszulComplex R E φ) (φ e)).f
                ((n + 1 : ℕ) : ℤ) =
              (Homotopy.nullHomotopicMap' (C := koszulComplex R E φ)
                (D := koszulComplex R E φ) (c := ComplexShape.down ℤ) h).f
                ((n + 1 : ℕ) : ℤ)
            rw [Homotopy.nullHomotopicMap'_f (c := ComplexShape.down ℤ)
              h21 h10]
            have hn1 : (0 : ℤ) ≤ (n : ℤ) + 1 := by omega
            have hd10''' :
                (koszulComplex R E φ).d ((n + 1 : ℕ) : ℤ) (n : ℤ) =
                  ModuleCat.ofHom (koszulDifferential R E φ n) := by
              simpa using koszulComplex_d_nonnegative R E φ n
            have hd21''' :
                (koszulComplex R E φ).d (((n + 1) + 1 : ℕ) : ℤ)
                    ((n + 1 : ℕ) : ℤ) =
                  ModuleCat.ofHom (koszulDifferential R E φ (n + 1)) := by
              simpa only [Int.natCast_add, Int.natCast_one] using
                koszulComplex_d_nonnegative R E φ (n + 1)
            rw [hd10''', hd21''', h10', h21']
            have hscalar :
                (scalarChainMap R (koszulComplex R E φ) (φ e)).f
                    ((n + 1 : ℕ) : ℤ) =
                  (φ e) • 𝟙 (ModuleCat.of R (⋀[R]^(n + 1) E)) := by
              simp [scalarChainMap, koszulComplex, koszulTermZ, hn1]
              rfl
            rw [hscalar]
            apply ModuleCat.hom_ext
            apply LinearMap.ext
            intro x
            have hc := congrArg ModuleCat.Hom.hom (hcat (n + 1))
            have hs : ModuleCat.Hom.hom
                ((φ e) • 𝟙 (ModuleCat.of R (⋀[R]^(n + 1) E))) =
                (φ e) • LinearMap.id := by
              ext y
              rfl
            rw [hs]
            have hx := LinearMap.congr_fun hc x
            have hcomp :
                (ModuleCat.Hom.hom
                    (ModuleCat.ofHom
                      (koszulDifferential R E φ (n + 1) ∘ₗ
                        koszulWedge R E e (n + 1) +
                        koszulHomotopyPrev R E φ e (n + 1)))) x =
                  (ModuleCat.Hom.hom
                    (ModuleCat.ofHom (koszulDifferential R E φ n) ≫
                        ModuleCat.ofHom (koszulWedge R E e n) +
                      ModuleCat.ofHom (koszulWedge R E e (n + 1)) ≫
                        ModuleCat.ofHom (koszulDifferential R E φ (n + 1)))) x := by
              change
                koszulDifferential R E φ (n + 1)
                    (koszulWedge R E e (n + 1) x) +
                    koszulWedge R E e n
                      (koszulDifferential R E φ n x) =
                  koszulWedge R E e n
                      (koszulDifferential R E φ n x) +
                    koszulDifferential R E φ (n + 1)
                      (koszulWedge R E e (n + 1) x)
              exact add_comm _ _
            exact hx.trans hcomp
    | negSucc n =>
        exact (koszulComplex_X_negative R E φ (Int.negSucc n) (by omega)).eq_of_src _ _
  rw [hmap]
  exact ⟨Homotopy.nullHomotopy' (C := koszulComplex R E φ)
    (D := koszulComplex R E φ) (c := ComplexShape.down ℤ) h⟩

theorem koszul_homotopy_sequence
    (R : Type u) [CommRing R] (r : ℕ) (f : Fin r → R) (i : Fin r) :
    Nonempty (Homotopy
      (scalarChainMap R (koszulComplexOn R r f) (f i)) 0) := by
  classical
  have hsingle :
      sequenceLinearMap R r f (Pi.single i 1) = f i := by
    simp [sequenceLinearMap, Pi.single_apply]
  change Nonempty (Homotopy
    (scalarChainMap R
      (koszulComplex R (Fin r → R) (sequenceLinearMap R r f)) (f i)) 0)
  rw [← hsingle]
  exact koszul_homotopy_abstract R (Fin r → R)
    (sequenceLinearMap R r f) (Pi.single i 1)

/-- An ideal acts by zero on a module. -/
def IdealActsByZero (R : Type u) [CommRing R] (I : Ideal R) (M : Type u)
    [AddCommGroup M] [Module R M] : Prop :=
  ∀ a ∈ I, ∀ x : M, a • x = 0

theorem koszul_homology_annihilated
    (R : Type u) [CommRing R] (r : ℕ) (f : Fin r → R) (n : ℤ) :
    IdealActsByZero R (Ideal.span (Set.range f))
      ((koszulComplexOn R r f).homology n) := by
  sorry

/-! ## Mapping cones -/

/-- Mathlib's homotopy cofiber is the mapping cone of a chain map. -/
noncomputable abbrev homotopyCone {R : Type u} [CommRing R]
    {A B : ChainComplex (ModuleCat.{u} R) ℤ} (f : A ⟶ B) :=
  HomologicalComplex.homotopyCofiber f

/-- The canonical inclusion of the target into a homotopy cone. -/
noncomputable abbrev coneInclusion {R : Type u} [CommRing R]
    {A B : ChainComplex (ModuleCat.{u} R) ℤ} (f : A ⟶ B) :
    B ⟶ homotopyCone f :=
  HomologicalComplex.homotopyCofiber.inr f

/-- A component of the canonical projection from a cone to its shifted source. -/
noncomputable abbrev coneProjectionComponent {R : Type u} [CommRing R]
    {A B : ChainComplex (ModuleCat.{u} R) ℤ} (f : A ⟶ B)
    (i j : ℤ) (hij : (ComplexShape.down ℤ).Rel i j) :
    (homotopyCone f).X i ⟶ A.X j :=
  HomologicalComplex.homotopyCofiber.fstX f i j hij

/-- The canonical projection from a cone to the shifted source. -/
noncomputable def coneProjection {R : Type u} [CommRing R]
    {A B : ChainComplex (ModuleCat.{u} R) ℤ} (f : A ⟶ B) :
    homotopyCone f ⟶
      (Formalization.Books.Homology.Unit14.ChainComplex.shiftFunctor
        (ModuleCat.{u} R) (-1 : ℤ)).obj A :=
  { f := fun i =>
      HomologicalComplex.homotopyCofiber.fstX f i (i - 1) (by
        simp [ComplexShape.down, ComplexShape.down'])
    comm' := by
      intro i j hij
      sorry }

theorem homotopyCone_d_fst
    {R : Type u} [CommRing R] {A B : ChainComplex (ModuleCat.{u} R) ℤ}
    (f : A ⟶ B) (i j k : ℤ)
    (hij : (ComplexShape.down ℤ).Rel i j) (hjk : (ComplexShape.down ℤ).Rel j k) :
    (homotopyCone f).d i j ≫
        HomologicalComplex.homotopyCofiber.fstX f j k hjk =
      -HomologicalComplex.homotopyCofiber.fstX f i j hij ≫ A.d j k := by
  exact HomologicalComplex.homotopyCofiber.d_fstX f i j k hij hjk

theorem homotopyCone_d_snd
    {R : Type u} [CommRing R] {A B : ChainComplex (ModuleCat.{u} R) ℤ}
    (f : A ⟶ B) (i j : ℤ) (hij : (ComplexShape.down ℤ).Rel i j) :
    (homotopyCone f).d i j ≫
        HomologicalComplex.homotopyCofiber.sndX f j =
      HomologicalComplex.homotopyCofiber.fstX f i j hij ≫ f.f j +
        HomologicalComplex.homotopyCofiber.sndX f i ≫ B.d i j := by
  exact HomologicalComplex.homotopyCofiber.d_sndX f i j hij

/-- The map whose cone is the Koszul complex after adjoining one generator. -/
def koszulExtendedMap (R E : Type u) [CommRing R] [AddCommGroup E]
    [Module R E] (φ : E →ₗ[R] R) (f : R) : (E × R) →ₗ[R] R :=
  { toFun := fun x => φ x.1 + f * x.2
    map_add' := by
      intro x y
      simp [map_add]
      rw [mul_add]
      ac_rfl
    map_smul' := by
      intro a x
      simp [smul_eq_mul, mul_add, mul_left_comm] }

theorem koszul_cone_abstract
    (R E : Type u) [CommRing R] [AddCommGroup E] [Module R E]
    (φ : E →ₗ[R] R) (f : R) :
    Nonempty (koszulComplex R (E × R) (koszulExtendedMap R E φ f) ≅
      homotopyCone (scalarChainMap R (koszulComplex R E φ) f)) := by
  sorry

theorem koszul_cone_sequence
    (R : Type u) [CommRing R] (r : ℕ) (f : Fin (r + 1) → R) :
    Nonempty (koszulComplexOn R (r + 1) f ≅
      homotopyCone
        (scalarChainMap R
          (koszulComplexOn R r (fun i => f i.castSucc)) (f (Fin.last r)))) := by
  sorry

/-! ## Squared cones and multiplication -/

abbrev IntegerChainComplex (R : Type u) [CommRing R] :=
  ChainComplex (ModuleCat.{u} R) ℤ

noncomputable abbrev chainShiftOne {R : Type u} [CommRing R]
    (A : IntegerChainComplex R) : IntegerChainComplex R :=
  (Formalization.Books.Homology.Unit14.ChainComplex.shiftFunctor
    (ModuleCat.{u} R) (1 : ℤ)).obj A

noncomputable abbrev integerHomotopyCone {R : Type u} [CommRing R]
    {A B : IntegerChainComplex R} (f : A ⟶ B) :=
  HomologicalComplex.homotopyCofiber f

theorem homotopyCone_squared
    (R : Type u) [CommRing R] (A : IntegerChainComplex R) (f g : R) :
    ∃ q : chainShiftOne (integerHomotopyCone (scalarChainMap R A f)) ⟶
        integerHomotopyCone (scalarChainMap R A g),
      Nonempty (HomotopyEquiv
        (integerHomotopyCone (scalarChainMap R A (f * g)))
        (integerHomotopyCone q)) := by
  sorry

theorem koszul_multiplicative_abstract
    (R E : Type u) [CommRing R] [AddCommGroup E] [Module R E]
    (φ : E →ₗ[R] R) (f g : R) :
    ∃ q : chainShiftOne
          (koszulComplex R (E × R) (koszulExtendedMap R E φ f)) ⟶
        koszulComplex R (E × R) (koszulExtendedMap R E φ g),
      Nonempty (HomotopyEquiv
        (koszulComplex R (E × R) (koszulExtendedMap R E φ (f * g)))
        (integerHomotopyCone q)) := by
  sorry

theorem koszul_multiplicative_sequence
    (R : Type u) [CommRing R] (r : ℕ) (f : Fin r → R) (a b : R) :
    ∃ q : chainShiftOne
          (koszulComplexOn R (r + 1) (sequenceAppendLast r f a)) ⟶
        koszulComplexOn R (r + 1) (sequenceAppendLast r f b),
      Nonempty (HomotopyEquiv
        (koszulComplexOn R (r + 1) (sequenceAppendLast r f (a * b)))
        (integerHomotopyCone q)) := by
  sorry

/-! ## Joins of sequences -/

/-- Concatenation of two finite sequences. -/
def joinSequences {r s : ℕ} (f : Fin r → R) (g : Fin s → R) : Fin (r + s) → R :=
  Fin.append f g

/-- The canonical total tensor complex of two nonnegative chain complexes. -/
abbrev NatChainComplex (R : Type u) [CommRing R] :=
  ChainComplex (ModuleCat.{u} R) ℕ

noncomputable abbrev tensorChainComplex (R : Type u) [CommRing R]
    (K L : NatChainComplex R) : NatChainComplex R :=
  HomologicalComplex.tensorObj K L

theorem koszul_join_sequences
    (R : Type u) [CommRing R] {r s : ℕ} (f : Fin r → R) (g : Fin s → R) :
    Nonempty (koszulComplexOnNat R (r + s) (joinSequences f g) ≅
      tensorChainComplex R (koszulComplexOnNat R r f) (koszulComplexOnNat R s g)) := by
  sorry

end Formalization.Books.MoreAlgebra.Unit29
