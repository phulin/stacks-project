import Mathlib.RingTheory.AlgebraicIndependent.Basic
import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
import Mathlib.RingTheory.DiscreteValuationRing.TFAE
import Mathlib.RingTheory.FiniteType
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Jacobson.Radical
import Mathlib.RingTheory.KrullDimension.Polynomial
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.Localization.Integral
import Mathlib.RingTheory.Localization.Ideal
import Mathlib.RingTheory.PowerSeries.NoZeroDivisors
import Mathlib.RingTheory.RegularLocalRing.Defs

/-!
# Examples, Chapter 19: A non catenary Noetherian local ring

This file formalizes the precise constructions and assertions in the source
section.  The source's ring-theoretic verifications are theorem interfaces at
this stage; the power-series, generated-subalgebra, ideal, localization, and
scalar-plus-Jacobson-radical constructions themselves use Mathlib's canonical
objects.
-/

noncomputable section

namespace Formalization.Books.Examples.Unit19

open scoped BigOperators Polynomial

universe u v

section PowerSeriesConstruction

variable (k : Type u) [Field k]

/-- The formal series `z = ∑ i ≥ 1, a i X^i` from the source. -/
noncomputable def zPowerSeries (a : ℕ → k) : PowerSeries k :=
  PowerSeries.mk a

/-- The tail `z_j = ∑ i ≥ j, a i X^(i-j)`. -/
noncomputable def zTail (a : ℕ → k) (j : ℕ) : PowerSeries k :=
  PowerSeries.mk (fun n ↦ a (n + j))

/- The finite initial part subtracted in the source's Laurent-series formula
   for `z_j`.  The range `j - 1` indexes `a₁, ..., a_{j-1}`. -/
def zPrefix (a : ℕ → k) (j : ℕ) : PowerSeries k :=
  Finset.sum (Finset.range (j - 1))
    (fun i ↦ PowerSeries.C (a (i + 1)) * PowerSeries.X ^ (i + 1))

/-- The fraction field of `k⟦X⟧`, used for the source's Laurent series field
`k((x)) = k⟦x⟧[1/x]`. -/
abbrev LaurentSeriesField := FractionRing (PowerSeries k)

/-- The canonical map from the rational function field `k(x)` into the
fraction field of `k⟦x⟧`. -/
noncomputable def rationalFunctionToLaurentSeries :
    FractionRing (Polynomial k) →+* LaurentSeriesField k :=
  IsFractionRing.map
    (j := (Polynomial.coeToPowerSeries.ringHom : Polynomial k →+* PowerSeries k))
    (Polynomial.coe_injective k)

/-- The rational-function-field algebra structure on the Laurent series field. -/
@[instance_reducible] noncomputable def rationalFunctionAlgebra :
    Algebra (FractionRing (Polynomial k)) (LaurentSeriesField k) :=
  RingHom.toAlgebra (rationalFunctionToLaurentSeries k)

/-- A coefficient sequence satisfying the source's zero constant coefficient
and transcendence hypotheses. -/
structure PowerSeriesData where
  coefficients : ℕ → k
  constantCoeff_zero : coefficients 0 = 0
  transcendental :
    letI := rationalFunctionAlgebra k
    Transcendental (FractionRing (Polynomial k))
      (algebraMap (PowerSeries k) (LaurentSeriesField k)
        (zPowerSeries (k := k) coefficients))

variable {k}

/- The displayed definition of `z_j` as a Laurent-series quotient. -/
theorem zTail_eq_inv_X_pow_mul_sub_prefix
    (d : PowerSeriesData k) {j : ℕ} (hj : 1 ≤ j) :
    algebraMap (PowerSeries k) (LaurentSeriesField k)
        (zTail (k := k) d.coefficients j) =
      (algebraMap (PowerSeries k) (LaurentSeriesField k) PowerSeries.X)⁻¹ ^ j *
        (algebraMap (PowerSeries k) (LaurentSeriesField k)
            (zPowerSeries (k := k) d.coefficients) -
          algebraMap (PowerSeries k) (LaurentSeriesField k)
            (zPrefix (k := k) d.coefficients j)) := by
  have hrec : ∀ n : ℕ,
      PowerSeries.X * zTail (k := k) d.coefficients (n + 1) +
          PowerSeries.C (d.coefficients n) =
        zTail (k := k) d.coefficients n := by
    intro n
    rw [PowerSeries.eq_X_mul_shift_add_const
      (zTail (k := k) d.coefficients n)]
    congr 1
    · ext m
      simp [zTail, PowerSeries.coeff_mk, Nat.add_assoc, Nat.add_comm,
        Nat.add_left_comm]
    · simp [zTail, PowerSeries.constantCoeff_mk]
  have hprefix : ∀ n : ℕ,
      zPrefix (k := k) d.coefficients (n + 1) =
        zPrefix (k := k) d.coefficients n +
          PowerSeries.C (d.coefficients n) * PowerSeries.X ^ n := by
    intro n
    cases n with
    | zero =>
        simp [zPrefix, d.constantCoeff_zero]
    | succ n =>
        simp [zPrefix, Finset.sum_range_succ]
  have hpow : ∀ n : ℕ,
      (PowerSeries.X ^ n) * zTail (k := k) d.coefficients n +
          zPrefix (k := k) d.coefficients n =
        zPowerSeries (k := k) d.coefficients := by
    intro n
    induction n with
    | zero =>
        simp [zPowerSeries, zTail, zPrefix]
    | succ n ih =>
        calc
          (PowerSeries.X ^ (n + 1)) *
                zTail (k := k) d.coefficients (n + 1) +
              zPrefix (k := k) d.coefficients (n + 1) =
              (PowerSeries.X ^ n) *
                  (PowerSeries.X * zTail (k := k) d.coefficients (n + 1) +
                    PowerSeries.C (d.coefficients n)) +
                zPrefix (k := k) d.coefficients n := by
            rw [pow_succ, hprefix n]
            ring
          _ = (PowerSeries.X ^ n) * zTail (k := k) d.coefficients n +
                zPrefix (k := k) d.coefficients n := by
            rw [hrec n]
          _ = zPowerSeries (k := k) d.coefficients := ih
  have hsub :
      (PowerSeries.X ^ j) * zTail (k := k) d.coefficients j =
        zPowerSeries (k := k) d.coefficients -
          zPrefix (k := k) d.coefficients j :=
    (eq_sub_iff_add_eq).2 (hpow j)
  let f := algebraMap (PowerSeries k) (LaurentSeriesField k)
  have hmap := congrArg f hsub
  have hx : f PowerSeries.X ≠ 0 := by
    intro h
    have h' :
        (algebraMap (PowerSeries k) (LaurentSeriesField k)) PowerSeries.X =
          (algebraMap (PowerSeries k) (LaurentSeriesField k)) 0 := by
      simpa [f] using h
    have hX : (PowerSeries.X : PowerSeries k) = 0 :=
      (IsFractionRing.injective (PowerSeries k) (LaurentSeriesField k)) h'
    have hcoeff := congrArg (PowerSeries.coeff 1) hX
    simpa using hcoeff
  change f (zTail (k := k) d.coefficients j) =
    (f PowerSeries.X)⁻¹ ^ j *
      (f (zPowerSeries (k := k) d.coefficients) -
        f (zPrefix (k := k) d.coefficients j))
  rw [← map_sub, ← hmap]
  simp only [map_mul, map_pow]
  rw [← mul_assoc, ← mul_pow, inv_mul_cancel₀ hx, one_pow, one_mul]

/-- The source identity `z = x z₁`. -/
theorem z_eq_X_mul_zTail_one (d : PowerSeriesData k) :
    zPowerSeries (k := k) d.coefficients = PowerSeries.X *
      zTail (k := k) d.coefficients 1 := by
  rw [PowerSeries.eq_X_mul_shift_add_const
    (zPowerSeries (k := k) d.coefficients)]
  simp only [zPowerSeries, PowerSeries.constantCoeff_mk]
  rw [d.constantCoeff_zero]
  simp [zTail]

/-- The source recursion `x z_(j+1) + a_j = z_j` for `j ≥ 1`. -/
theorem X_mul_zTail_succ_add_coeff_eq_zTail
    (d : PowerSeriesData k) {j : ℕ} (hj : 1 ≤ j) :
    PowerSeries.X * zTail (k := k) d.coefficients (j + 1) +
        PowerSeries.C (d.coefficients j) =
      zTail (k := k) d.coefficients j := by
  rw [PowerSeries.eq_X_mul_shift_add_const
    (zTail (k := k) d.coefficients j)]
  congr 1
  · ext n
    simp [zTail, PowerSeries.coeff_mk, Nat.add_assoc, Nat.add_comm,
      Nat.add_left_comm]
  · simp [zTail, PowerSeries.constantCoeff_mk]

/-- The `k`-subalgebra generated by `x`, `z`, and all the `z_j` (`j ≥ 1`). -/
noncomputable def generatedRing (d : PowerSeriesData k) : Subalgebra k (PowerSeries k) :=
  Algebra.adjoin k
    (insert PowerSeries.X
      (insert (zPowerSeries (k := k) d.coefficients)
        (Set.range (fun j : ℕ ↦ zTail (k := k) d.coefficients (j + 1)))))

/-- The distinguished element `x` in the generated ring. -/
noncomputable def xInGeneratedRing (d : PowerSeriesData k) : generatedRing d :=
  ⟨PowerSeries.X, Algebra.subset_adjoin (by simp)⟩

/-- The distinguished element `z` in the generated ring. -/
noncomputable def zInGeneratedRing (d : PowerSeriesData k) : generatedRing d :=
  ⟨zPowerSeries (k := k) d.coefficients, Algebra.subset_adjoin (by simp)⟩

/-- The element `z_(j+1)` in the generated ring. -/
noncomputable def zSuccInGeneratedRing (d : PowerSeriesData k) (j : ℕ) : generatedRing d :=
  ⟨zTail (k := k) d.coefficients (j + 1),
    Algebra.subset_adjoin (by
      exact Or.inr (Or.inr (Set.mem_range.2 ⟨j, rfl⟩)))⟩

end PowerSeriesConstruction

section TheTwoLocalizations

variable {k : Type u} [Field k]

/-- The ring `R = k[x, z₁, z₂, ...] ⊂ k⟦x⟧`. -/
noncomputable abbrev R (d : PowerSeriesData k) := generatedRing d

/-- The canonical inclusion of the generated ring into the power-series ring. -/
noncomputable def generatedRingInclusion (d : PowerSeriesData k) : R d →+* PowerSeries k :=
  (generatedRing d).val.toRingHom

/- The generated ring is a domain because it is a subalgebra of the domain
   `k⟦X⟧`.  This instance records the ambient-domain fact used by the
   localization and fraction-field interfaces below. -/
instance r_isDomain (d : PowerSeriesData k) : IsDomain (R d) := by
  dsimp [R]
  infer_instance

/- The scalar structure used to state the transcendence degree of the
   fraction field of `R`.  Mathlib deliberately does not make this tower
   algebra an unconditional instance because of possible instance diamonds. -/
@[instance_reducible] noncomputable def fractionFieldRAlgebra (d : PowerSeriesData k) :
    Algebra k (FractionRing (R d)) :=
  RingHom.toAlgebra
    ((algebraMap (R d) (FractionRing (R d))).comp (algebraMap k (R d)))

private noncomputable abbrev fractionFieldRAlgebraInst (d : PowerSeriesData k) :
    Algebra k (FractionRing (R d)) :=
  fractionFieldRAlgebra d


/- The source's assertion that the fraction field of `R` has transcendence
   degree two over `k`. -/
attribute [local instance] fractionFieldRAlgebraInst in
theorem fractionField_R_transcendence_degree_two (d : PowerSeriesData k) :
    @Algebra.trdeg k (FractionRing (R d)) _ _ (fractionFieldRAlgebra d) = 2 := by
  let gL : R d →+* LaurentSeriesField k :=
    (algebraMap (PowerSeries k) (LaurentSeriesField k)).comp (generatedRingInclusion d)
  have hgL : Function.Injective gL := by
    intro a b h
    apply Subtype.ext
    apply (IsFractionRing.injective (PowerSeries k) (LaurentSeriesField k))
    exact h
  let γ : FractionRing (R d) →+* LaurentSeriesField k :=
    IsFractionRing.lift (A := R d) (K := FractionRing (R d)) (L := LaurentSeriesField k) hgL
  have hscalar (a : k) :
      algebraMap k (FractionRing (R d)) a =
        algebraMap (R d) (FractionRing (R d)) (algebraMap k (R d) a) := by
    rfl
  have hγk : γ.comp (algebraMap k (FractionRing (R d))) =
      algebraMap k (LaurentSeriesField k) := by
    ext c
    change γ (algebraMap k (FractionRing (R d)) c) =
      algebraMap k (LaurentSeriesField k) c
    rw [hscalar c]
    rw [IsFractionRing.lift_algebraMap]
    rfl
  let xK : FractionRing (R d) :=
    algebraMap (R d) (FractionRing (R d)) (xInGeneratedRing d)
  let zK : FractionRing (R d) :=
    algebraMap (R d) (FractionRing (R d)) (zInGeneratedRing d)
  let xL : LaurentSeriesField k :=
    algebraMap (PowerSeries k) (LaurentSeriesField k) PowerSeries.X
  let zL : LaurentSeriesField k :=
    algebraMap (PowerSeries k) (LaurentSeriesField k)
      (zPowerSeries (k := k) d.coefficients)
  have hγx : γ xK = xL := by
    change γ (algebraMap (R d) (FractionRing (R d)) (xInGeneratedRing d)) = xL
    rw [IsFractionRing.lift_algebraMap]
    rfl
  have hγz : γ zK = zL := by
    change γ (algebraMap (R d) (FractionRing (R d)) (zInGeneratedRing d)) = zL
    rw [IsFractionRing.lift_algebraMap]
    rfl
  let cK : Polynomial k →+* FractionRing (R d) :=
    Polynomial.eval₂RingHom (algebraMap k (FractionRing (R d))) xK
  let cL : Polynomial k →+* LaurentSeriesField k :=
    Polynomial.eval₂RingHom (algebraMap k (LaurentSeriesField k)) xL
  have hγc : γ.comp cK = cL := by
    apply RingHom.ext
    intro p
    change γ (Polynomial.eval₂ (algebraMap k (FractionRing (R d))) xK p) =
      Polynomial.eval₂ (algebraMap k (LaurentSeriesField k)) xL p
    rw [Polynomial.hom_eval₂]
    rw [hγk, hγx]
  let eK : Polynomial (Polynomial k) →+* FractionRing (R d) :=
    Polynomial.eval₂RingHom cK zK
  let eL : Polynomial (Polynomial k) →+* LaurentSeriesField k :=
    Polynomial.eval₂RingHom cL zL
  have hγe : γ.comp eK = eL := by
    apply RingHom.ext
    intro p
    change γ (Polynomial.eval₂ cK zK p) = Polynomial.eval₂ cL zL p
    rw [Polynomial.hom_eval₂]
    rw [hγc, hγz]
  letI : Algebra (FractionRing (Polynomial k)) (LaurentSeriesField k) :=
    rationalFunctionAlgebra k
  have hztrans :
      Transcendental (FractionRing (Polynomial k)) zL := by
    simpa [zL] using d.transcendental
  let cF : Polynomial k →+* FractionRing (Polynomial k) :=
    algebraMap (Polynomial k) (FractionRing (Polynomial k))
  have hcL :
      (algebraMap (PowerSeries k) (LaurentSeriesField k)).comp
          (Polynomial.coeToPowerSeries.ringHom : Polynomial k →+* PowerSeries k) = cL := by
    have hC :
        (algebraMap (PowerSeries k) (LaurentSeriesField k)).comp
            PowerSeries.C = algebraMap k (LaurentSeriesField k) := by
      ext c
      rfl
    apply RingHom.ext
    intro p
    induction p using Polynomial.induction_on' with
    | add p q hp hq =>
        simp [cL, xL] at hp hq ⊢
        rw [hp, hq]
    | monomial n a =>
        have hm : PowerSeries.monomial n a =
            PowerSeries.C a * PowerSeries.X ^ n := by
          ext m
          simp [PowerSeries.coeff_C_mul_X_pow, PowerSeries.coeff_monomial]
        change (algebraMap (PowerSeries k) (LaurentSeriesField k))
            ((Polynomial.monomial n a : Polynomial k) : PowerSeries k) = cL _
        rw [Polynomial.coe_monomial, hm]
        calc
          (algebraMap (PowerSeries k) (LaurentSeriesField k))
                (PowerSeries.C a * PowerSeries.X ^ n) =
              (algebraMap k (LaurentSeriesField k)) a * xL ^ n := by
            rw [map_mul, map_pow]
            have hCa :
                (algebraMap (PowerSeries k) (LaurentSeriesField k))
                    (PowerSeries.C a) = (algebraMap k (LaurentSeriesField k)) a := by
              change ((algebraMap (PowerSeries k) (LaurentSeriesField k)).comp
                PowerSeries.C) a = _
              exact RingHom.congr_fun hC a
            rw [hCa]
          _ = cL (Polynomial.monomial n a) := by
            simp [cL, xL]
  have hcoeff :
      (algebraMap (FractionRing (Polynomial k)) (LaurentSeriesField k)).comp cF = cL := by
    let j : Polynomial k →+* PowerSeries k :=
      Polynomial.coeToPowerSeries.ringHom
    let hj : nonZeroDivisors (Polynomial k) ≤
        (nonZeroDivisors (PowerSeries k)).comap j :=
      nonZeroDivisors_le_comap_nonZeroDivisors_of_injective j
        (Polynomial.coe_injective k)
    have hmapcomp :
        (IsLocalization.map (LaurentSeriesField k) j hj).comp
            (algebraMap (Polynomial k) (FractionRing (Polynomial k))) =
          (algebraMap (PowerSeries k) (LaurentSeriesField k)).comp j := by
      exact IsLocalization.map_comp hj
    apply RingHom.ext
    intro p
    change rationalFunctionToLaurentSeries k (algebraMap (Polynomial k)
      (FractionRing (Polynomial k)) p) = cL p
    rw [show rationalFunctionToLaurentSeries k =
      IsLocalization.map (LaurentSeriesField k) j hj from rfl]
    calc
      (IsLocalization.map (LaurentSeriesField k) j hj)
          ((algebraMap (Polynomial k) (FractionRing (Polynomial k))) p) =
          ((algebraMap (PowerSeries k) (LaurentSeriesField k)).comp j) p :=
        RingHom.congr_fun hmapcomp p
      _ = cL p := by
        exact RingHom.congr_fun hcL p
  have heL : Function.Injective eL := by
    intro p q hpq
    have hroot :
        Polynomial.aeval zL ((p - q).map cF) = 0 := by
      change Polynomial.eval₂
          (algebraMap (FractionRing (Polynomial k)) (LaurentSeriesField k)) zL
          ((p - q).map cF) = 0
      rw [Polynomial.eval₂_map, hcoeff]
      change eL (p - q) = 0
      rw [map_sub, hpq, sub_self]
    have hmapzero : (p - q).map cF = 0 :=
      (transcendental_iff_injective.mp hztrans) (by simpa using hroot)
    have hdiff : p - q = 0 := by
      apply Polynomial.map_injective cF
        (IsFractionRing.injective (Polynomial k) (FractionRing (Polynomial k)))
      simpa using hmapzero
    exact sub_eq_zero.mp hdiff
  have heK : Function.Injective eK := by
    intro p q hpq
    apply heL
    have h' : eL p = eL q := by
      rw [← RingHom.congr_fun hγe p, ← RingHom.congr_fun hγe q]
      exact congrArg γ hpq
    exact h'
  let eKAlg : Polynomial (Polynomial k) →ₐ[k] FractionRing (R d) :=
    { eK with
      commutes' := by
        intro c
        simp [eK, cK] }
  have heKAlg : Function.Injective eKAlg := heK
  let φ : FractionRing (Polynomial (Polynomial k)) →ₐ[k] FractionRing (R d) :=
    IsFractionRing.liftAlgHom heKAlg
  have hq :
      Algebra.trdeg k (Polynomial (Polynomial k)) = 2 := by
    rw [← trdeg_add_eq k (Polynomial k) (A := Polynomial (Polynomial k))]
    norm_num
  have hlow :
      2 ≤ Algebra.trdeg k (FractionRing (R d)) := by
    calc
      2 = Algebra.trdeg k (Polynomial (Polynomial k)) := hq.symm
      _ ≤ Algebra.trdeg k (FractionRing (R d)) :=
        trdeg_le_of_injective eKAlg heKAlg
  let qX : Polynomial (Polynomial k) := Polynomial.C Polynomial.X
  let qZ : Polynomial (Polynomial k) := Polynomial.X
  let qXK : FractionRing (Polynomial (Polynomial k)) :=
    algebraMap (Polynomial (Polynomial k))
      (FractionRing (Polynomial (Polynomial k))) qX
  let qZK : FractionRing (Polynomial (Polynomial k)) :=
    algebraMap (Polynomial (Polynomial k))
      (FractionRing (Polynomial (Polynomial k))) qZ
  have hφx : φ qXK = xK := by
    change IsFractionRing.lift heKAlg qXK = xK
    rw [IsFractionRing.lift_algebraMap]
    change eK (Polynomial.C Polynomial.X) = xK
    simp [eK, cK, xK]
  have hφz : φ qZK = zK := by
    change IsFractionRing.lift heKAlg qZK = zK
    rw [IsFractionRing.lift_algebraMap]
    change eK Polynomial.X = zK
    simp [eK, zK]
  have hxK : xK ≠ 0 := by
    intro h
    have h' : algebraMap (R d) (FractionRing (R d))
        (xInGeneratedRing d) = algebraMap (R d) (FractionRing (R d)) 0 := by
      simpa [xK] using h
    have hR : xInGeneratedRing d = 0 :=
      (IsFractionRing.injective (R d) (FractionRing (R d))) h'
    have hX : (PowerSeries.X : PowerSeries k) = 0 := by
      exact congrArg Subtype.val hR
    have hcoeff := congrArg (PowerSeries.coeff 1) hX
    simpa using hcoeff
  have htail : ∀ n : ℕ, ∃ q : FractionRing (Polynomial (Polynomial k)),
      φ q = algebraMap (R d) (FractionRing (R d))
        (zSuccInGeneratedRing d n) := by
    intro n
    induction n with
    | zero =>
        refine ⟨qXK⁻¹ * qZK, ?_⟩
        have hzR : xInGeneratedRing d * zSuccInGeneratedRing d 0 =
            zInGeneratedRing d := by
          apply Subtype.ext
          exact (z_eq_X_mul_zTail_one d).symm
        have hzK := congrArg (algebraMap (R d) (FractionRing (R d))) hzR
        rw [map_mul] at hzK
        rw [map_mul, map_inv₀, hφx, hφz]
        change xK⁻¹ * zK = _
        calc
          xK⁻¹ * zK = xK⁻¹ * (xK *
              algebraMap (R d) (FractionRing (R d))
                (zSuccInGeneratedRing d 0)) := by rw [hzK]
          _ = algebraMap (R d) (FractionRing (R d))
                (zSuccInGeneratedRing d 0) := by
            rw [← mul_assoc, inv_mul_cancel₀ hxK, one_mul]
    | succ n ih =>
        obtain ⟨q, hq⟩ := ih
        refine ⟨qXK⁻¹ *
          (q - algebraMap k (FractionRing (Polynomial (Polynomial k)))
            (d.coefficients (n + 1))), ?_⟩
        have hrecR : xInGeneratedRing d * zSuccInGeneratedRing d (n + 1) +
            algebraMap k (R d) (d.coefficients (n + 1)) =
              zSuccInGeneratedRing d n := by
          apply Subtype.ext
          change PowerSeries.X * zTail (k := k) d.coefficients (n + 2) +
              PowerSeries.C (d.coefficients (n + 1)) =
                zTail (k := k) d.coefficients (n + 1)
          exact X_mul_zTail_succ_add_coeff_eq_zTail d (by omega)
        have hrecK := congrArg (algebraMap (R d) (FractionRing (R d))) hrecR
        rw [map_add, map_mul] at hrecK
        have hrecK' : xK * algebraMap (R d) (FractionRing (R d))
              (zSuccInGeneratedRing d (n + 1)) +
              algebraMap k (FractionRing (R d)) (d.coefficients (n + 1)) =
            algebraMap (R d) (FractionRing (R d))
              (zSuccInGeneratedRing d n) := by
          rw [hscalar]
          simpa [xK] using hrecK
        rw [map_mul, map_inv₀, map_sub, hφx, hq, φ.commutes]
        calc
          xK⁻¹ *
              (algebraMap (R d) (FractionRing (R d))
                (zSuccInGeneratedRing d n) -
                algebraMap k (FractionRing (R d))
                  (d.coefficients (n + 1))) =
              xK⁻¹ *
              (xK * algebraMap (R d) (FractionRing (R d))
                  (zSuccInGeneratedRing d (n + 1)) +
                  algebraMap k (FractionRing (R d))
                    (d.coefficients (n + 1)) -
                  algebraMap k (FractionRing (R d))
              (d.coefficients (n + 1))) := by rw [hrecK']
          _ = algebraMap (R d) (FractionRing (R d))
              (zSuccInGeneratedRing d (n + 1)) := by
            rw [add_sub_cancel_right, ← mul_assoc, inv_mul_cancel₀ hxK, one_mul]
  have hrange : ∀ (y : PowerSeries k) (hy : y ∈ generatedRing d),
      ∃ q : FractionRing (Polynomial (Polynomial k)),
        φ q = algebraMap (R d) (FractionRing (R d)) ⟨y, hy⟩ := by
    intro y hy
    refine Algebra.adjoin_induction
      (p := fun y hy => ∃ q : FractionRing (Polynomial (Polynomial k)),
        φ q = algebraMap (R d) (FractionRing (R d)) ⟨y, hy⟩)
      ?_ ?_ ?_ ?_ hy
    · intro y hy
      rcases hy with (rfl | hy)
      · refine ⟨qXK, hφx.trans ?_⟩
        congr 1
      · rcases hy with (rfl | hy)
        · refine ⟨qZK, hφz.trans ?_⟩
          congr 1
        · rcases Set.mem_range.mp hy with ⟨n, rfl⟩
          obtain ⟨q, hq⟩ := htail n
          refine ⟨q, hq.trans ?_⟩
          congr 1
    · intro c
      refine ⟨algebraMap k (FractionRing (Polynomial (Polynomial k))) c, ?_⟩
      rw [φ.commutes, hscalar c]
      congr 1
    · intro y z _ _ hy hz
      rcases hy with ⟨qy, hy⟩
      rcases hz with ⟨qz, hz⟩
      refine ⟨qy + qz, ?_⟩
      rw [map_add, hy, hz, ← map_add]
      congr 1
    · intro y z _ _ hy hz
      rcases hy with ⟨qy, hy⟩
      rcases hz with ⟨qz, hz⟩
      refine ⟨qy * qz, ?_⟩
      rw [map_mul, hy, hz, ← map_mul]
      congr 1
  have hsurj : Function.Surjective φ := by
    intro y
    obtain ⟨a, b, hb, hy⟩ := IsFractionRing.div_surjective (R d) y
    obtain ⟨qa, hqa⟩ := hrange a a.property
    obtain ⟨qb, hqb⟩ := hrange b b.property
    refine ⟨qa / qb, ?_⟩
    calc
      φ (qa / qb) = φ qa / φ qb := by rw [map_div₀]
      _ = algebraMap (R d) (FractionRing (R d)) a /
          algebraMap (R d) (FractionRing (R d)) b := by rw [hqa, hqb]
      _ = y := hy
  haveI : Algebra.IsAlgebraic (FractionRing (Polynomial (Polynomial k)))
      (FractionRing (Polynomial (Polynomial k))) :=
    Algebra.IsAlgebraic.of_finite _ _
  haveI : Algebra.IsAlgebraic (Polynomial (Polynomial k))
      (FractionRing (Polynomial (Polynomial k))) :=
    (IsFractionRing.comap_isAlgebraic_iff
      (A := Polynomial (Polynomial k))
      (K := FractionRing (Polynomial (Polynomial k)))
      (C := FractionRing (Polynomial (Polynomial k)))).2 inferInstance
  have hqF :
      Algebra.trdeg k (FractionRing (Polynomial (Polynomial k))) = 2 := by
    rw [← trdeg_add_eq k (Polynomial (Polynomial k))
      (A := FractionRing (Polynomial (Polynomial k)))]
    have hzero :
        Algebra.trdeg (Polynomial (Polynomial k))
          (FractionRing (Polynomial (Polynomial k))) = 0 :=
      trdeg_eq_zero
    rw [hzero, add_zero]
    exact hq
  have hupp :
      Algebra.trdeg k (FractionRing (R d)) ≤
        Algebra.trdeg k (FractionRing (Polynomial (Polynomial k))) :=
    trdeg_le_of_surjective φ hsurj
  have hupp' : Algebra.trdeg k (FractionRing (R d)) ≤ 2 := by
    rw [hqF] at hupp
    exact hupp
  exact le_antisymm hupp' hlow

/-- The coefficient sum `a₁ + ⋯ + a_j` occurring in the generators of `𝔫`. -/
def initialCoefficientSum (d : PowerSeriesData k) (j : ℕ) : k :=
  Finset.sum (Finset.range j) (fun i ↦ d.coefficients (i + 1))

/-- The `j`th generator `z_(j+1) + a₁ + ⋯ + a_j` of `𝔫`. -/
noncomputable def nGenerator (d : PowerSeriesData k) (j : ℕ) : R d :=
  zSuccInGeneratedRing d j +
    algebraMap k (R d) (initialCoefficientSum d j)

/-- The maximal ideal `𝔪 = (x)`. -/
noncomputable def mIdeal (d : PowerSeriesData k) : Ideal (R d) :=
  Ideal.span {xInGeneratedRing d}

/-- The ideal `𝔫 = (x - 1, z₁, z₂ + a₁, z₃ + a₁ + a₂, ...)`. -/
noncomputable def nIdeal (d : PowerSeriesData k) : Ideal (R d) :=
  Ideal.span (insert (xInGeneratedRing d - 1) (Set.range (nGenerator d)))

/-- The principal ideal `(x - 1)` used in the intermediate quotient. -/
noncomputable def xSubOneIdeal (d : PowerSeriesData k) : Ideal (R d) :=
  Ideal.span {xInGeneratedRing d - 1}

/-- The quotient by `𝔪` is the coefficient field. -/
theorem quotient_mIdeal_equiv (d : PowerSeriesData k) :
    Nonempty (R d ⧸ mIdeal d ≃+* k) := by
  sorry

/-- The ideal `𝔪` is maximal. -/
theorem mIdeal_isMaximal (d : PowerSeriesData k) :
    (mIdeal d).IsMaximal := by
  sorry

/-- The quotient by `(x - 1)` is the polynomial ring `k[z]`. -/
theorem quotient_xSubOneIdeal_equiv (d : PowerSeriesData k) :
    Nonempty (R d ⧸ xSubOneIdeal d ≃+* Polynomial k) := by
  sorry

theorem nIdeal_eq_span_xSubOne_z (d : PowerSeriesData k) :
    nIdeal d = Ideal.span {xInGeneratedRing d - 1, zInGeneratedRing d} := by
  sorry

/-- The ideal `𝔫` is maximal. -/
theorem nIdeal_isMaximal (d : PowerSeriesData k) :
    (nIdeal d).IsMaximal := by
  sorry

theorem mIdeal_isPrime (d : PowerSeriesData k) :
    (mIdeal d).IsPrime :=
  (mIdeal_isMaximal d).isPrime

theorem nIdeal_isPrime (d : PowerSeriesData k) :
    (nIdeal d).IsPrime :=
  (nIdeal_isMaximal d).isPrime

instance mIdeal_isPrime_instance (d : PowerSeriesData k) :
    (mIdeal d).IsPrime := mIdeal_isPrime d

instance nIdeal_isPrime_instance (d : PowerSeriesData k) :
    (nIdeal d).IsPrime := nIdeal_isPrime d

theorem non_m_maps_to_powerSeries_unit (d : PowerSeriesData k) :
    ∀ r : R d, r ∉ mIdeal d → IsUnit (generatedRingInclusion d r) := by
  sorry

/-- The localization `R_𝔪` embeds in `k⟦x⟧`. -/
theorem localization_m_embeds_in_powerSeries (d : PowerSeriesData k) :
    ∃ f : Localization.AtPrime (mIdeal d) →+* PowerSeries k,
      Function.Injective f ∧
        f.comp (algebraMap (R d) (Localization.AtPrime (mIdeal d))) =
          generatedRingInclusion d := by
  sorry

/-- `R_𝔪` is a discrete valuation ring with residue field `k`. -/
theorem localization_m_is_dvr (d : PowerSeriesData k) :
    IsDiscreteValuationRing (Localization.AtPrime (mIdeal d)) := by
  sorry

theorem localization_m_is_noetherian_regular (d : PowerSeriesData k) :
    IsNoetherianRing (Localization.AtPrime (mIdeal d)) ∧
      IsRegularLocalRing (Localization.AtPrime (mIdeal d)) := by
  sorry

theorem localization_m_has_dimension_one (d : PowerSeriesData k) :
    ringKrullDim (Localization.AtPrime (mIdeal d)) = 1 := by
  sorry

theorem localization_m_has_residue_field_k (d : PowerSeriesData k) :
    Nonempty (IsLocalRing.ResidueField (Localization.AtPrime (mIdeal d)) ≃+* k) := by
  sorry

/-- The residue field at `𝔫` is also `k`. -/
theorem quotient_nIdeal_equiv (d : PowerSeriesData k) :
    Nonempty (R d ⧸ nIdeal d ≃+* k) := by
  sorry

/-- The Laurent polynomial ring `k[x, x⁻¹]`. -/
abbrev LaurentPolynomialRing (k : Type u) [Field k] :=
  Localization.Away (Polynomial.X : Polynomial k)

/-- The polynomial ring `k[x, x⁻¹, z]` used in the presentation of `R_𝔫`. -/
abbrev nPresentationRing (k : Type u) [Field k] := Polynomial (LaurentPolynomialRing k)

/-- The image of `x` in `k[x, x⁻¹]`. -/
noncomputable def xInLaurentPolynomialRing (k : Type u) [Field k] : LaurentPolynomialRing k :=
  algebraMap (Polynomial k) (LaurentPolynomialRing k) Polynomial.X

/-- The maximal ideal `(x - 1, z)` in `k[x, x⁻¹, z]`. -/
noncomputable def nPresentationIdeal (k : Type u) [Field k] : Ideal (nPresentationRing k) :=
  Ideal.span {algebraMap (LaurentPolynomialRing k) (nPresentationRing k)
      (xInLaurentPolynomialRing k) - 1, Polynomial.X}

/-- The presentation ideal is maximal. -/
theorem nPresentationIdeal_isMaximal (k : Type u) [Field k] :
    (nPresentationIdeal k).IsMaximal := by
  sorry

instance nPresentationIdeal_isPrime_instance :
    (nPresentationIdeal k).IsPrime :=
  (nPresentationIdeal_isMaximal k).isPrime

/-- The source's presentation of `R_𝔫` by the localization of
`k[x, x⁻¹, z]` at `(x - 1, z)`. -/
theorem localization_n_presentation (d : PowerSeriesData k) :
    Nonempty (Localization.AtPrime (nPresentationIdeal k) ≃+*
      Localization.AtPrime (nIdeal d)) := by
  sorry

/-- `R_𝔫` is a regular local ring of dimension `2` and residue field `k`. -/
theorem localization_n_is_regular_local_dim_two (d : PowerSeriesData k) :
    IsNoetherianRing (Localization.AtPrime (nIdeal d)) ∧
      IsRegularLocalRing (Localization.AtPrime (nIdeal d)) ∧
      ringKrullDim (Localization.AtPrime (nIdeal d)) = 2 ∧
      Nonempty (IsLocalRing.ResidueField (Localization.AtPrime (nIdeal d)) ≃+* k) := by
  sorry

/-- The source's multiplicative subset `S = (R - 𝔪) ∩ (R - 𝔫)`. -/
def multiplicativeSet (d : PowerSeriesData k) : Set (R d) :=
  ((Set.univ : Set (R d)) \ (mIdeal d : Set (R d))) ∩
    ((Set.univ : Set (R d)) \ (nIdeal d : Set (R d)))

theorem multiplicativeSet_eq_complement_union (d : PowerSeriesData k) :
    multiplicativeSet d =
      (Set.univ : Set (R d)) \ ((mIdeal d : Set (R d)) ∪ (nIdeal d : Set (R d))) := by
  ext r
  simp [multiplicativeSet]

theorem multiplicativeSet_isMultiplicative (d : PowerSeriesData k) :
    1 ∈ multiplicativeSet d ∧
      ∀ {r s : R d}, r ∈ multiplicativeSet d → s ∈ multiplicativeSet d →
        r * s ∈ multiplicativeSet d := by
  sorry

/- The displayed multiplicative subset, bundled as Mathlib's canonical
submonoid structure. -/
noncomputable def multiplicativeSubmonoid (d : PowerSeriesData k) : Submonoid (R d) :=
  { carrier := multiplicativeSet d
    one_mem' := (multiplicativeSet_isMultiplicative d).1
    mul_mem' := by
      intro r s hr hs
      exact (multiplicativeSet_isMultiplicative d).2 hr hs }

/-- The ring `B = S⁻¹R`. -/
noncomputable def B (d : PowerSeriesData k) := Localization (multiplicativeSubmonoid d)

instance b_commRing_instance (d : PowerSeriesData k) : CommRing (B d) := by
  unfold B
  infer_instance

noncomputable instance b_algebra_R_instance (d : PowerSeriesData k) : Algebra (R d) (B d) :=
  by
    unfold B
    infer_instance

noncomputable instance b_algebra_k_instance (d : PowerSeriesData k) : Algebra k (B d) := by
  unfold B R
  infer_instance

theorem b_isDomain (d : PowerSeriesData k) :
    IsDomain (B d) := by
  sorry

instance b_isDomain_instance (d : PowerSeriesData k) : IsDomain (B d) := b_isDomain d

/-- Extension of `𝔪` to `B`. -/
noncomputable def mBIdeal (d : PowerSeriesData k) : Ideal (B d) :=
  Ideal.map (algebraMap (R d) (B d)) (mIdeal d)

/-- Extension of `𝔫` to `B`. -/
noncomputable def nBIdeal (d : PowerSeriesData k) : Ideal (B d) :=
  Ideal.map (algebraMap (R d) (B d)) (nIdeal d)

theorem b_is_k_algebra (d : PowerSeriesData k) :
    Nonempty (Algebra k (B d)) := by
  exact ⟨inferInstance⟩

/-- The two displayed ideals remain maximal after passing from `R` to `B`. -/
theorem mBIdeal_isMaximal (d : PowerSeriesData k) :
    (mBIdeal d).IsMaximal := by
  sorry

theorem nBIdeal_isMaximal (d : PowerSeriesData k) :
    (nBIdeal d).IsMaximal := by
  sorry

theorem mBIdeal_isPrime (d : PowerSeriesData k) :
    (mBIdeal d).IsPrime :=
  (mBIdeal_isMaximal d).isPrime

theorem nBIdeal_isPrime (d : PowerSeriesData k) :
    (nBIdeal d).IsPrime :=
  (nBIdeal_isMaximal d).isPrime

instance mBIdeal_isPrime_instance (d : PowerSeriesData k) :
    (mBIdeal d).IsPrime := mBIdeal_isPrime d

instance nBIdeal_isPrime_instance (d : PowerSeriesData k) :
    (nBIdeal d).IsPrime := nBIdeal_isPrime d

theorem b_maximal_ideals (d : PowerSeriesData k) :
    mBIdeal d ≠ nBIdeal d ∧
      ∀ I : Ideal (B d), I.IsMaximal ↔ I = mBIdeal d ∨ I = nBIdeal d := by
  sorry

theorem b_residue_fields (d : PowerSeriesData k) :
    Nonempty (B d ⧸ mBIdeal d ≃+* k) ∧
      Nonempty (B d ⧸ nBIdeal d ≃+* k) := by
  sorry

theorem b_localization_m_equiv (d : PowerSeriesData k) :
    Nonempty (Localization.AtPrime (mBIdeal d) ≃+*
      Localization.AtPrime (mIdeal d)) := by
  sorry

theorem b_localization_n_equiv (d : PowerSeriesData k) :
    Nonempty (Localization.AtPrime (nBIdeal d) ≃+*
      Localization.AtPrime (nIdeal d)) := by
  sorry

theorem b_localization_m_properties (d : PowerSeriesData k) :
    IsNoetherianRing (Localization.AtPrime (mBIdeal d)) ∧
      IsRegularLocalRing (Localization.AtPrime (mBIdeal d)) ∧
      IsDiscreteValuationRing (Localization.AtPrime (mBIdeal d)) ∧
      ringKrullDim (Localization.AtPrime (mBIdeal d)) = 1 ∧
      Nonempty (IsLocalRing.ResidueField (Localization.AtPrime (mBIdeal d)) ≃+* k) := by
  sorry

theorem b_localization_n_properties (d : PowerSeriesData k) :
    IsNoetherianRing (Localization.AtPrime (nBIdeal d)) ∧
      IsRegularLocalRing (Localization.AtPrime (nBIdeal d)) ∧
      ringKrullDim (Localization.AtPrime (nBIdeal d)) = 2 ∧
      Nonempty (IsLocalRing.ResidueField (Localization.AtPrime (nBIdeal d)) ≃+* k) := by
  sorry

theorem b_isNoetherian (d : PowerSeriesData k) :
    IsNoetherianRing (B d) := by
  sorry

theorem b_dimension_two (d : PowerSeriesData k) :
    ringKrullDim (B d) = 2 := by
  sorry

end TheTwoLocalizations

section ScalarPlusRadical

variable {k : Type u} [Field k]

/- The Jacobson radical is the intersection of the two maximal ideals. -/
noncomputable def jacobsonRadical (d : PowerSeriesData k) : Ideal (B d) :=
  Ring.jacobson (B d)

theorem jacobsonRadical_eq_inf (d : PowerSeriesData k) :
    jacobsonRadical d = mBIdeal d ⊓ nBIdeal d := by
  sorry

/- The canonical subalgebra implementation of `A = k + rad(B)`. -/
noncomputable def A (d : PowerSeriesData k) : Subalgebra k (B d) :=
  Algebra.adjoin k (jacobsonRadical d : Set (B d))

noncomputable instance a_commRing_instance (d : PowerSeriesData k) : CommRing (A d) :=
  inferInstance

/- The source's scalar-plus-Jacobson-radical carrier description. -/
def scalarPlusJacobianSet (d : PowerSeriesData k) : Set (B d) :=
  {b | ∃ c : k, ∃ r : B d, r ∈ jacobsonRadical d ∧
    b = algebraMap k (B d) c + r}

theorem a_carrier_eq_scalarPlusJacobianSet (d : PowerSeriesData k) :
    (A d : Set (B d)) = scalarPlusJacobianSet d := by
  sorry

/- The maximal ideal of `A`, obtained by pulling back the Jacobson radical. -/
noncomputable def aMaximalIdeal (d : PowerSeriesData k) : Ideal (A d) :=
  Ideal.comap (A d).val.toRingHom (jacobsonRadical d)

theorem b_finite_over_a (d : PowerSeriesData k) :
    Module.Finite (A d) (B d) := by
  sorry

theorem b_finite_type_over_a (d : PowerSeriesData k) :
    Algebra.FiniteType (A d) (B d) := by
  sorry

theorem eakin_noetherian_descent (d : PowerSeriesData k)
    (hB : IsNoetherianRing (B d)) (hfinite : Module.Finite (A d) (B d)) :
    IsNoetherianRing (A d) := by
  sorry

theorem a_isNoetherian (d : PowerSeriesData k) :
    IsNoetherianRing (A d) := by
  sorry

theorem a_isDomain (d : PowerSeriesData k) :
    IsDomain (A d) := by
  sorry

theorem a_isLocal (d : PowerSeriesData k) :
    IsLocalRing (A d) := by
  sorry

instance a_isDomain_instance (d : PowerSeriesData k) : IsDomain (A d) := a_isDomain d

instance a_isLocal_instance (d : PowerSeriesData k) : IsLocalRing (A d) := a_isLocal d

theorem aMaximalIdeal_isMaximal (d : PowerSeriesData k) :
    (aMaximalIdeal d).IsMaximal := by
  sorry

theorem a_residue_field (d : PowerSeriesData k) :
    Nonempty (A d ⧸ aMaximalIdeal d ≃+* k) := by
  sorry

theorem a_same_fraction_field (d : PowerSeriesData k) :
    Nonempty (FractionRing (A d) ≃+* FractionRing (B d)) := by
  sorry

theorem a_dimension_two (d : PowerSeriesData k) :
    ringKrullDim (A d) = 2 := by
  sorry

/-- The image of the original generator `x` in `B`. -/
noncomputable def xInB (d : PowerSeriesData k) : B d :=
  algebraMap (R d) (B d) (xInGeneratedRing d)

/-- The assertion that `B = A[x]`. -/
theorem b_generated_by_x_over_a (d : PowerSeriesData k) :
    Algebra.adjoin (A d) ({xInB d} : Set (B d)) = ⊤ := by
  sorry

/-- Evaluation at `x` gives the polynomial presentation of `B` over `A`. -/
noncomputable def bPolynomialEvaluation (d : PowerSeriesData k) :
    Polynomial (A d) →+* B d :=
  (Polynomial.aeval (R := A d) (xInB d)).toRingHom

noncomputable def bPresentationPrime (d : PowerSeriesData k) :
    Ideal (Polynomial (A d)) :=
  RingHom.ker (bPolynomialEvaluation d)

theorem bPresentationPrime_isPrime (d : PowerSeriesData k) :
    (bPresentationPrime d).IsPrime := by
  sorry

theorem b_polynomial_presentation (d : PowerSeriesData k) :
    Nonempty (Polynomial (A d) ⧸ bPresentationPrime d ≃+* B d) := by
  sorry

/-- The maximal ideal `m'` of `A[x]` lying over `mB`. -/
noncomputable def mPrime (d : PowerSeriesData k) : Ideal (Polynomial (A d)) :=
  Ideal.comap (bPolynomialEvaluation d) (mBIdeal d)

theorem mPrime_isMaximal (d : PowerSeriesData k) :
    (mPrime d).IsMaximal := by
  sorry

theorem mPrime_isPrime (d : PowerSeriesData k) :
    (mPrime d).IsPrime :=
  (mPrime_isMaximal d).isPrime

instance mPrime_isPrime_instance (d : PowerSeriesData k) :
    (mPrime d).IsPrime := mPrime_isPrime d

/-- The localization of `A[x]` at the maximal ideal `m'`. -/
def mPrimeLocalization (d : PowerSeriesData k) :=
  Localization.AtPrime (mPrime d)

instance mPrimeLocalization_commRing_instance (d : PowerSeriesData k) :
    CommRing (mPrimeLocalization d) := by
  unfold mPrimeLocalization
  infer_instance

noncomputable instance mPrimeLocalization_algebra (d : PowerSeriesData k) :
    Algebra (Polynomial (A d)) (mPrimeLocalization d) := by
  unfold mPrimeLocalization
  infer_instance

instance mPrimeLocalization_isLocalRing (d : PowerSeriesData k) :
    IsLocalRing (mPrimeLocalization d) := by
  unfold mPrimeLocalization
  infer_instance

/-- The localization of the prime `p` in the displayed chain. -/
noncomputable def pLocalizedIdeal (d : PowerSeriesData k) :
    Ideal (mPrimeLocalization d) :=
  Ideal.map (algebraMap (Polynomial (A d)) (mPrimeLocalization d))
    (bPresentationPrime d)

/-- The maximal ideal in the local ring at `m'`. -/
noncomputable def mPrimeLocalizedIdeal (d : PowerSeriesData k) :
    Ideal (mPrimeLocalization d) :=
  IsLocalRing.maximalIdeal (mPrimeLocalization d)

theorem displayed_prime_chain_strict (d : PowerSeriesData k) :
    (⊥ : Ideal (mPrimeLocalization d)) < pLocalizedIdeal d ∧
      pLocalizedIdeal d < mPrimeLocalizedIdeal d := by
  sorry

theorem mPrime_local_isNoetherian (d : PowerSeriesData k) :
    IsNoetherianRing (mPrimeLocalization d) := by
  sorry

theorem mPrime_local_dimension_three (d : PowerSeriesData k) :
    ringKrullDim (mPrimeLocalization d) = 3 := by
  sorry

end ScalarPlusRadical

section Catenarity

variable {k : Type u} [Field k]

/-- A finite totally ordered set of prime ideals between two fixed endpoints. -/
structure PrimeChainBetween (R : Type*) [CommRing R] (p q : Ideal R) where
  ideals : Set (Ideal R)
  finite : ideals.Finite
  contains_left : p ∈ ideals
  contains_right : q ∈ ideals
  lower_bound : ∀ I ∈ ideals, p ≤ I
  upper_bound : ∀ I ∈ ideals, I ≤ q
  prime : ∀ I ∈ ideals, I.IsPrime
  comparable : ∀ ⦃I J : Ideal R⦄, I ∈ ideals → J ∈ ideals → I ≤ J ∨ J ≤ I

namespace PrimeChainBetween

def length {R : Type*} [CommRing R] {p q : Ideal R}
    (c : PrimeChainBetween R p q) : ℕ :=
  c.ideals.ncard - 1

/-- No prime ideal can be inserted between two members of a saturated chain. -/
def IsSaturated {R : Type*} [CommRing R] {p q : Ideal R}
    (c : PrimeChainBetween R p q) : Prop :=
  ¬ ∃ r : Ideal R, r.IsPrime ∧ r ∉ c.ideals ∧
    ∃ I ∈ c.ideals, ∃ J ∈ c.ideals, I < r ∧ r < J

end PrimeChainBetween

/-- Catenarity expressed by bounded finite chains and equal lengths of finite
    saturated prime chains. -/
def IsCatenaryRing (R : Type*) [CommRing R] : Prop :=
  ∀ (p q : Ideal R), p.IsPrime → q.IsPrime → p ≤ q →
    ∃ n : ℕ, (∀ c : PrimeChainBetween R p q, c.length ≤ n) ∧
      ∀ c d : PrimeChainBetween R p q,
        c.IsSaturated → d.IsSaturated → c.length = d.length

/-- Universal catenarity for a Noetherian ring and all its finite-type
    algebras. -/
def IsUniversallyCatenary (R : Type*) [CommRing R] : Prop :=
  IsNoetherianRing R ∧
    ∀ (S : Type*) [CommRing S] [Algebra R S] [Algebra.FiniteType R S],
      IsCatenaryRing S

def IsNonCatenaryRing (R : Type*) [CommRing R] : Prop :=
  ¬ IsCatenaryRing R

theorem a_isCatenary (d : PowerSeriesData k) :
    IsCatenaryRing (A d) := by
  sorry

theorem universal_catenary_implies_b_m_dimension_two (d : PowerSeriesData k)
    (hA : IsUniversallyCatenary (A d)) :
    ringKrullDim (Localization.AtPrime (mBIdeal d)) = 2 := by
  sorry

theorem b_m_dimension_one (d : PowerSeriesData k) :
    ringKrullDim (Localization.AtPrime (mBIdeal d)) = 1 := by
  sorry

theorem a_not_universally_catenary (d : PowerSeriesData k) :
    ¬ IsUniversallyCatenary (A d) := by
  sorry

noncomputable def displayedPrimeChainIdeals (d : PowerSeriesData k) :
    Set (Ideal (mPrimeLocalization d)) :=
  {⊥, pLocalizedIdeal d, mPrimeLocalizedIdeal d}

theorem exists_displayed_maximal_prime_chain (d : PowerSeriesData k) :
    ∃ c : PrimeChainBetween (mPrimeLocalization d) ⊥ (mPrimeLocalizedIdeal d),
      c.ideals = displayedPrimeChainIdeals d ∧
        c.IsSaturated ∧ c.length = 2 := by
  sorry

theorem polynomial_localization_is_nonCatenary_noetherian_local
    (d : PowerSeriesData k) :
    IsNoetherianRing (mPrimeLocalization d) ∧
      IsLocalRing (mPrimeLocalization d) ∧
      IsNonCatenaryRing (mPrimeLocalization d) := by
  sorry

end Catenarity

section FinalExample

variable {k : Type u} [Field k]

theorem exists_powerSeriesData (k : Type u) [Field k] :
    Nonempty (PowerSeriesData k) := by
  sorry

theorem constructed_A_properties (d : PowerSeriesData k) :
    IsNoetherianRing (A d) ∧ IsLocalRing (A d) ∧ IsDomain (A d) ∧
      ringKrullDim (A d) = 2 ∧ ¬ IsUniversallyCatenary (A d) := by
  sorry

theorem exists_nonCatenaryNoetherianLocalRing (k : Type u) [Field k] :
    ∃ d : PowerSeriesData k,
      IsNoetherianRing (mPrimeLocalization d) ∧
        IsLocalRing (mPrimeLocalization d) ∧
          IsNonCatenaryRing (mPrimeLocalization d) := by
  sorry

end FinalExample

end Formalization.Books.Examples.Unit19
