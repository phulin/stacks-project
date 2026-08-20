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
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.RegularLocalRing.Polynomial

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
      simp [zTail, PowerSeries.coeff_mk, Nat.add_comm,
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
  have hj' : (j - 1) + 1 = j := Nat.sub_add_cancel hj
  have hsub :
      (PowerSeries.X ^ j) * zTail (k := k) d.coefficients j =
        zPowerSeries (k := k) d.coefficients -
          zPrefix (k := k) d.coefficients j :=
    (eq_sub_iff_add_eq).2 (by
      simpa only [hj'] using hpow ((j - 1) + 1))
  let f := algebraMap (PowerSeries k) (LaurentSeriesField k)
  have hmap := congrArg f hsub
  have hx : f PowerSeries.X ≠ 0 := by
    intro h
    have h' :
        (algebraMap (PowerSeries k) (LaurentSeriesField k)) PowerSeries.X =
          (algebraMap (PowerSeries k) (LaurentSeriesField k)) 0 := by
      rw [map_zero]
      simp only [f] at h
      exact h
    have hX : (PowerSeries.X : PowerSeries k) = 0 :=
      (IsFractionRing.injective (PowerSeries k) (LaurentSeriesField k)) h'
    have hcoeff := congrArg (PowerSeries.coeff 1) hX
    norm_num at hcoeff
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
  have hrec : ∀ n : ℕ,
      PowerSeries.X * zTail (k := k) d.coefficients (n + 1) +
          PowerSeries.C (d.coefficients n) =
        zTail (k := k) d.coefficients n := by
    intro n
    rw [PowerSeries.eq_X_mul_shift_add_const
      (zTail (k := k) d.coefficients n)]
    congr 1
    · ext m
      simp [zTail, PowerSeries.coeff_mk, Nat.add_comm, Nat.add_left_comm]
    · simp [zTail, PowerSeries.constantCoeff_mk]
  have hj' : (j - 1) + 1 = j := Nat.sub_add_cancel hj
  simpa only [hj'] using hrec ((j - 1) + 1)

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

private noncomputable abbrev rationalFunctionAlgebraInst (k : Type u) [Field k] :
    Algebra (FractionRing (Polynomial k)) (LaurentSeriesField k) :=
  rationalFunctionAlgebra k

private noncomputable abbrev polynomialFractionRingSelfAlgebraicInst (k : Type u) [Field k] :
    Algebra.IsAlgebraic (FractionRing (Polynomial (Polynomial k)))
      (FractionRing (Polynomial (Polynomial k))) :=
  Algebra.IsAlgebraic.of_finite _ _

private noncomputable abbrev polynomialFractionRingAlgebraicInst (k : Type u) [Field k] :
    Algebra.IsAlgebraic (Polynomial (Polynomial k))
      (FractionRing (Polynomial (Polynomial k))) :=
  (IsFractionRing.comap_isAlgebraic_iff
    (A := Polynomial (Polynomial k))
    (K := FractionRing (Polynomial (Polynomial k)))
    (C := FractionRing (Polynomial (Polynomial k)))).2
      (polynomialFractionRingSelfAlgebraicInst k)


/- The source's assertion that the fraction field of `R` has transcendence
   degree two over `k`. -/
attribute [local instance] fractionFieldRAlgebraInst rationalFunctionAlgebraInst
  polynomialFractionRingSelfAlgebraicInst polynomialFractionRingAlgebraicInst in
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
          simp [PowerSeries.coeff_monomial]
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
    norm_num at hcoeff
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
  let f : R d →+* k :=
    (PowerSeries.constantCoeff (R := k)).comp (generatedRingInclusion d)
  have hdecomp : ∀ (y : PowerSeries k) (hy : y ∈ generatedRing d),
      (⟨y, hy⟩ : R d) - algebraMap k (R d) (PowerSeries.constantCoeff y) ∈
        mIdeal d := by
    intro y hy
    refine Algebra.adjoin_induction
      (p := fun y hy =>
        (⟨y, hy⟩ : R d) - algebraMap k (R d) (PowerSeries.constantCoeff y) ∈
          mIdeal d)
      ?_ ?_ ?_ ?_ hy
    · rintro y (rfl | hy)
      · change xInGeneratedRing d -
          algebraMap k (R d) (PowerSeries.constantCoeff PowerSeries.X) ∈ mIdeal d
        simp only [PowerSeries.constantCoeff_X, map_zero, sub_zero]
        exact Ideal.subset_span (by simp [mIdeal])
      · rcases Set.mem_insert_iff.mp hy with rfl | hy
        · change zInGeneratedRing d -
            algebraMap k (R d)
              (PowerSeries.constantCoeff
                (zPowerSeries (k := k) d.coefficients)) ∈ mIdeal d
          simp only [zPowerSeries, PowerSeries.constantCoeff_mk,
            d.constantCoeff_zero, map_zero, sub_zero]
          have hz : zInGeneratedRing d =
              xInGeneratedRing d * zSuccInGeneratedRing d 0 := by
            apply Subtype.ext
            simpa [xInGeneratedRing, zInGeneratedRing, zSuccInGeneratedRing]
              using z_eq_X_mul_zTail_one d
          rw [hz]
          exact (mIdeal d).mul_mem_right _ (Ideal.subset_span (by simp [mIdeal]))
        · rcases Set.mem_range.mp hy with ⟨j, rfl⟩
          change zSuccInGeneratedRing d j -
              algebraMap k (R d)
                (PowerSeries.constantCoeff
                  (zTail (k := k) d.coefficients (j + 1))) ∈ mIdeal d
          have hconst : PowerSeries.constantCoeff
              (zTail (k := k) d.coefficients (j + 1)) = d.coefficients (j + 1) := by
            simp [zTail]
          rw [hconst]
          have hrec : xInGeneratedRing d * zSuccInGeneratedRing d (j + 1) +
                algebraMap k (R d) (d.coefficients (j + 1)) =
              zSuccInGeneratedRing d j := by
            apply Subtype.ext
            change PowerSeries.X * zTail (k := k) d.coefficients (j + 2) +
                PowerSeries.C (d.coefficients (j + 1)) =
              zTail (k := k) d.coefficients (j + 1)
            exact X_mul_zTail_succ_add_coeff_eq_zTail d (by omega)
          have hmem : xInGeneratedRing d * zSuccInGeneratedRing d (j + 1) ∈
              mIdeal d :=
            (mIdeal d).mul_mem_right _ (Ideal.subset_span (by simp [mIdeal]))
          convert hmem using 1
          rw [← hrec]
          ring
    · intro c
      change algebraMap k (R d) c - algebraMap k (R d) c ∈ mIdeal d
      simp
    · intro y z _ _ hy hz
      have hmem := (mIdeal d).add_mem hy hz
      rw [sub_add_sub_comm] at hmem
      convert hmem using 1
      apply Subtype.ext
      simp [map_add]
    · intro y z hyY hyZ hy hz
      have hmem := (mIdeal d).add_mem
        ((mIdeal d).mul_mem_right (⟨z, hyZ⟩ : R d) hy) ((mIdeal d).mul_mem_left
          (algebraMap k (R d) (PowerSeries.constantCoeff y)) hz)
      convert hmem using 1
      apply Subtype.ext
      simp [map_mul]
      ring
  have hker : RingHom.ker f = mIdeal d := by
    apply le_antisymm
    · intro r hr
      have h := hdecomp r.1 r.2
      change PowerSeries.constantCoeff r.1 = 0 at hr
      simpa [hr] using h
    · rw [mIdeal, Ideal.span_le]
      intro r hr
      rcases hr with rfl
      simp [f, xInGeneratedRing, generatedRingInclusion]
  exact ⟨Ideal.quotEquivOfEq hker.symm |>.trans <|
    RingHom.quotientKerEquivOfSurjective (f := f) (by
      intro c
      exact ⟨algebraMap k (R d) c, by simp [f, generatedRingInclusion]⟩)⟩

private theorem generatedRing_sub_constantCoeff_mem_mIdeal
    (d : PowerSeriesData k) (y : PowerSeries k) (hy : y ∈ generatedRing d) :
    (⟨y, hy⟩ : R d) - algebraMap k (R d) (PowerSeries.constantCoeff y) ∈
      mIdeal d := by
  refine Algebra.adjoin_induction
    (p := fun y hy =>
      (⟨y, hy⟩ : R d) - algebraMap k (R d) (PowerSeries.constantCoeff y) ∈
        mIdeal d)
    ?_ ?_ ?_ ?_ hy
  · rintro y (rfl | hy)
    · change xInGeneratedRing d -
        algebraMap k (R d) (PowerSeries.constantCoeff PowerSeries.X) ∈ mIdeal d
      simp only [PowerSeries.constantCoeff_X, map_zero, sub_zero]
      exact Ideal.subset_span (by simp [mIdeal])
    · rcases Set.mem_insert_iff.mp hy with rfl | hy
      · change zInGeneratedRing d -
          algebraMap k (R d)
            (PowerSeries.constantCoeff
              (zPowerSeries (k := k) d.coefficients)) ∈ mIdeal d
        simp only [zPowerSeries, PowerSeries.constantCoeff_mk,
          d.constantCoeff_zero, map_zero, sub_zero]
        have hz : zInGeneratedRing d =
            xInGeneratedRing d * zSuccInGeneratedRing d 0 := by
          apply Subtype.ext
          simpa [xInGeneratedRing, zInGeneratedRing, zSuccInGeneratedRing]
            using z_eq_X_mul_zTail_one d
        rw [hz]
        exact (mIdeal d).mul_mem_right _ (Ideal.subset_span (by simp [mIdeal]))
      · rcases Set.mem_range.mp hy with ⟨j, rfl⟩
        change zSuccInGeneratedRing d j -
            algebraMap k (R d)
              (PowerSeries.constantCoeff
                (zTail (k := k) d.coefficients (j + 1))) ∈ mIdeal d
        have hconst : PowerSeries.constantCoeff
            (zTail (k := k) d.coefficients (j + 1)) = d.coefficients (j + 1) := by
          simp [zTail]
        rw [hconst]
        have hrec : xInGeneratedRing d * zSuccInGeneratedRing d (j + 1) +
              algebraMap k (R d) (d.coefficients (j + 1)) =
            zSuccInGeneratedRing d j := by
          apply Subtype.ext
          change PowerSeries.X * zTail (k := k) d.coefficients (j + 2) +
              PowerSeries.C (d.coefficients (j + 1)) =
            zTail (k := k) d.coefficients (j + 1)
          exact X_mul_zTail_succ_add_coeff_eq_zTail d (by omega)
        have hmem : xInGeneratedRing d * zSuccInGeneratedRing d (j + 1) ∈
            mIdeal d :=
          (mIdeal d).mul_mem_right _ (Ideal.subset_span (by simp [mIdeal]))
        convert hmem using 1
        rw [← hrec]
        ring
  · intro c
    change algebraMap k (R d) c - algebraMap k (R d) c ∈ mIdeal d
    simp
  · intro y z _ _ hy hz
    have hmem := (mIdeal d).add_mem hy hz
    rw [sub_add_sub_comm] at hmem
    convert hmem using 1
    apply Subtype.ext
    simp [map_add]
  · intro y z hyY hyZ hy hz
    have hmem := (mIdeal d).add_mem
      ((mIdeal d).mul_mem_right (⟨z, hyZ⟩ : R d) hy) ((mIdeal d).mul_mem_left
        (algebraMap k (R d) (PowerSeries.constantCoeff y)) hz)
    convert hmem using 1
    apply Subtype.ext
    simp [map_mul]
    ring

/-- The ideal `𝔪` is maximal. -/
theorem mIdeal_isMaximal (d : PowerSeriesData k) :
    (mIdeal d).IsMaximal := by
  rcases quotient_mIdeal_equiv d with ⟨e⟩
  apply Ideal.Quotient.maximal_of_isField
  exact e.toMulEquiv.isField (Field.toIsField k)

private noncomputable def xzPolynomialMap (d : PowerSeriesData k) :
    Polynomial (Polynomial k) →+* FractionRing (R d) :=
  Polynomial.eval₂RingHom
    (Polynomial.eval₂RingHom
      (algebraMap k (FractionRing (R d)))
      (algebraMap (R d) (FractionRing (R d)) (xInGeneratedRing d)))
    (algebraMap (R d) (FractionRing (R d)) (zInGeneratedRing d))

private theorem xzPolynomialMap_injective (d : PowerSeriesData k) :
    Function.Injective (xzPolynomialMap d) := by
  letI := rationalFunctionAlgebraInst k
  let gL : R d →+* LaurentSeriesField k :=
    (algebraMap (PowerSeries k) (LaurentSeriesField k)).comp
      (generatedRingInclusion d)
  have hgL : Function.Injective gL := by
    intro a b h
    apply Subtype.ext
    apply (IsFractionRing.injective (PowerSeries k) (LaurentSeriesField k))
    exact h
  let γ : FractionRing (R d) →+* LaurentSeriesField k :=
    IsFractionRing.lift (A := R d) (K := FractionRing (R d))
      (L := LaurentSeriesField k) hgL
  have hscalar (a : k) :
      algebraMap k (FractionRing (R d)) a =
        algebraMap (R d) (FractionRing (R d)) (algebraMap k (R d) a) := by
    rfl
  have hγk : γ.comp (algebraMap k (FractionRing (R d))) =
      algebraMap k (LaurentSeriesField k) := by
    ext c
    change γ (algebraMap k (FractionRing (R d)) c) =
      algebraMap k (LaurentSeriesField k) c
    rw [hscalar c, IsFractionRing.lift_algebraMap]
    rfl
  let xL : LaurentSeriesField k :=
    algebraMap (PowerSeries k) (LaurentSeriesField k) PowerSeries.X
  let zL : LaurentSeriesField k :=
    algebraMap (PowerSeries k) (LaurentSeriesField k)
      (zPowerSeries (k := k) d.coefficients)
  have hγx : γ (algebraMap (R d) (FractionRing (R d))
      (xInGeneratedRing d)) = xL := by
    rw [IsFractionRing.lift_algebraMap]
    rfl
  have hγz : γ (algebraMap (R d) (FractionRing (R d))
      (zInGeneratedRing d)) = zL := by
    rw [IsFractionRing.lift_algebraMap]
    rfl
  let xK : FractionRing (R d) :=
    algebraMap (R d) (FractionRing (R d)) (xInGeneratedRing d)
  let zK : FractionRing (R d) :=
    algebraMap (R d) (FractionRing (R d)) (zInGeneratedRing d)
  let cL : Polynomial k →+* LaurentSeriesField k :=
    Polynomial.eval₂RingHom (algebraMap k (LaurentSeriesField k)) xL
  let cK : Polynomial k →+* FractionRing (R d) :=
    Polynomial.eval₂RingHom (algebraMap k (FractionRing (R d))) xK
  let eL : Polynomial (Polynomial k) →+* LaurentSeriesField k :=
    Polynomial.eval₂RingHom cL zL
  have hγc : γ.comp cK = cL := by
    apply RingHom.ext
    intro p
    change γ (Polynomial.eval₂ (algebraMap k (FractionRing (R d))) xK p) =
      Polynomial.eval₂ (algebraMap k (LaurentSeriesField k)) xL p
    rw [Polynomial.hom_eval₂, hγk, hγx]
  have hγe : γ.comp (xzPolynomialMap d) = eL := by
    apply RingHom.ext
    intro p
    change γ (Polynomial.eval₂ cK zK p) = Polynomial.eval₂ cL zL p
    rw [Polynomial.hom_eval₂, hγc, hγz]
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
        simp [cL] at hp hq ⊢
        rw [hp, hq]
    | monomial n a =>
        have hm : PowerSeries.monomial n a =
            PowerSeries.C a * PowerSeries.X ^ n := by
          ext m
          simp [PowerSeries.coeff_monomial]
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
      _ = cL p := RingHom.congr_fun hcL p
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
  intro p q hpq
  apply heL
  have h' : eL p = eL q := by
    rw [← RingHom.congr_fun hγe p, ← RingHom.congr_fun hγe q]
    exact congrArg γ hpq
  exact h'

private theorem quotient_xSubOne_generated_surjective
    (d : PowerSeriesData k)
    (g : Polynomial k →+* (R d ⧸ xSubOneIdeal d))
    (htailQ : ∀ n : ℕ, ∃ p : Polynomial k,
      Ideal.Quotient.mk (xSubOneIdeal d) (zSuccInGeneratedRing d n) = g p)
    (hgX : g Polynomial.X =
      Ideal.Quotient.mk (xSubOneIdeal d) (zInGeneratedRing d))
    (hgC : ∀ c : k, g (Polynomial.C c) =
      algebraMap k (R d ⧸ xSubOneIdeal d) c) :
    ∀ (y : PowerSeries k) (hy : y ∈ generatedRing d),
      ∃ p : Polynomial k,
        Ideal.Quotient.mk (xSubOneIdeal d) ⟨y, hy⟩ = g p := by
  intro y hy
  change localization_n_presentation_hasRep (d := d) (S := S) gP
    (⟨y, hy⟩ : R d)
  refine Algebra.adjoin_induction
    (p := fun y hy =>
      ∃ p : Polynomial k,
        Ideal.Quotient.mk (xSubOneIdeal d) ⟨y, hy⟩ = g p)
    ?_ ?_ ?_ ?_ hy
  · rintro y (rfl | hy)
    · refine ⟨1, ?_⟩
      change Ideal.Quotient.mk (xSubOneIdeal d) (xInGeneratedRing d) = g 1
      have hxQ : Ideal.Quotient.mk (xSubOneIdeal d) (xInGeneratedRing d) = 1 :=
        (Ideal.Quotient.mk_eq_one_iff_sub_mem
          (I := xSubOneIdeal d) (xInGeneratedRing d)).2
          (Ideal.subset_span (by simp [xSubOneIdeal]))
      rw [hxQ]
      simp
    · rcases Set.mem_insert_iff.mp hy with rfl | hy
      · refine ⟨Polynomial.X, ?_⟩
        rw [hgX]
        congr 1
      · rcases Set.mem_range.mp hy with ⟨n, hn⟩
        subst y
        obtain ⟨p, hp⟩ := htailQ n
        refine ⟨p, ?_⟩
        calc
          Ideal.Quotient.mk (xSubOneIdeal d)
              (⟨zTail (k := k) d.coefficients (n + 1), _⟩ : R d) =
            Ideal.Quotient.mk (xSubOneIdeal d)
              (zSuccInGeneratedRing d n) := by congr 1
          _ = g p := hp
  · intro c
    refine ⟨Polynomial.C c, ?_⟩
    have hcalc :
        Ideal.Quotient.mk (xSubOneIdeal d) (algebraMap k (R d) c) =
          g (Polynomial.C c) := by
      calc
        Ideal.Quotient.mk (xSubOneIdeal d) (algebraMap k (R d) c) =
            algebraMap k (R d ⧸ xSubOneIdeal d) c :=
          rfl
        _ = g (Polynomial.C c) := (hgC c).symm
    exact hcalc
  · intro y z hyY hyZ hy hz
    rcases hy with ⟨py, hpy⟩
    rcases hz with ⟨pz, hpz⟩
    refine ⟨py + pz, ?_⟩
    have hsum : y + z ∈ generatedRing d :=
      (generatedRing d).add_mem hyY hyZ
    calc
      Ideal.Quotient.mk (xSubOneIdeal d) (⟨y + z, hsum⟩ : R d) =
          Ideal.Quotient.mk (xSubOneIdeal d)
            ((⟨y, hyY⟩ : R d) + ⟨z, hyZ⟩) := by
              congr 1
      _ = Ideal.Quotient.mk (xSubOneIdeal d) (⟨y, hyY⟩ : R d) +
            Ideal.Quotient.mk (xSubOneIdeal d) (⟨z, hyZ⟩ : R d) := by
              rw [map_add]
      _ = g py + g pz := by rw [hpy, hpz]
      _ = g (py + pz) := by rw [map_add]
  · intro y z hyY hyZ hy hz
    rcases hy with ⟨py, hpy⟩
    rcases hz with ⟨pz, hpz⟩
    refine ⟨py * pz, ?_⟩
    have hprod : y * z ∈ generatedRing d :=
      (generatedRing d).mul_mem hyY hyZ
    calc
      Ideal.Quotient.mk (xSubOneIdeal d) (⟨y * z, hprod⟩ : R d) =
          Ideal.Quotient.mk (xSubOneIdeal d)
            ((⟨y, hyY⟩ : R d) * ⟨z, hyZ⟩) := by
              congr 1
      _ = Ideal.Quotient.mk (xSubOneIdeal d) (⟨y, hyY⟩ : R d) *
            Ideal.Quotient.mk (xSubOneIdeal d) (⟨z, hyZ⟩ : R d) := by
              rw [map_mul]
      _ = g py * g pz := by rw [hpy, hpz]
      _ = g (py * pz) := by rw [map_mul]

private theorem xzPolynomialMap_eval₂_X (d : PowerSeriesData k) (p : Polynomial k) :
    xzPolynomialMap d
        (Polynomial.eval₂ (algebraMap k (Polynomial (Polynomial k)))
          (Polynomial.X : Polynomial (Polynomial k)) p) =
      Polynomial.eval₂ (algebraMap k (FractionRing (R d)))
        (algebraMap (R d) (FractionRing (R d)) (zInGeneratedRing d)) p := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
      rw [Polynomial.eval₂_add, map_add, Polynomial.eval₂_add, hp, hq]
  | monomial n a =>
      simp [xzPolynomialMap]

private theorem algebraMap_eval₂_z (d : PowerSeriesData k) (p : Polynomial k) :
    algebraMap (R d) (FractionRing (R d))
        (Polynomial.eval₂ (algebraMap k (R d)) (zInGeneratedRing d) p) =
      Polynomial.eval₂ (algebraMap k (FractionRing (R d)))
        (algebraMap (R d) (FractionRing (R d)) (zInGeneratedRing d)) p := by
  rw [Polynomial.hom_eval₂]
  have hcomp :
      (algebraMap (R d) (FractionRing (R d))).comp (algebraMap k (R d)) =
        algebraMap k (FractionRing (R d)) := by
    ext a
    exact (IsScalarTower.algebraMap_apply k (R d) (FractionRing (R d)) a).symm
  rw [hcomp]

private theorem evalP_eval_X (p : Polynomial k) :
    (Polynomial.eval₂RingHom
        (Polynomial.eval₂RingHom (Polynomial.C : k →+* Polynomial k) 1)
        (Polynomial.X : Polynomial k))
      (Polynomial.eval₂ (algebraMap k (Polynomial (Polynomial k)))
        (Polynomial.X : Polynomial (Polynomial k)) p) = p := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
      rw [Polynomial.eval₂_add, map_add, hp, hq]
  | monomial n a =>
      simp
      ext m
      by_cases h : m = n
      · subst m
        simp
      · have h' : n ≠ m := by exact Ne.symm h
        simp [Polynomial.coeff_monomial, h, h']

private theorem quotient_xSubOneIdeal_tailQ
    (d : PowerSeriesData k)
    (qz : R d ⧸ xSubOneIdeal d)
    (g : Polynomial k →+* (R d ⧸ xSubOneIdeal d))
    (hqz : qz = Ideal.Quotient.mk (xSubOneIdeal d) (zInGeneratedRing d))
    (hg : g = Polynomial.eval₂RingHom
      (algebraMap k (R d ⧸ xSubOneIdeal d)) qz) :
    ∀ n : ℕ, ∃ p : Polynomial k,
      Ideal.Quotient.mk (xSubOneIdeal d) (zSuccInGeneratedRing d n) = g p := by
  subst qz
  subst g
  let qz : R d ⧸ xSubOneIdeal d :=
    Ideal.Quotient.mk (xSubOneIdeal d) (zInGeneratedRing d)
  let g : Polynomial k →+* (R d ⧸ xSubOneIdeal d) :=
    Polynomial.eval₂RingHom
      (algebraMap k (R d ⧸ xSubOneIdeal d)) qz
  intro n
  induction n with
  | zero =>
      refine ⟨Polynomial.X, ?_⟩
      change Ideal.Quotient.mk (xSubOneIdeal d) (zSuccInGeneratedRing d 0) =
        g Polynomial.X
      have hzero :
          Ideal.Quotient.mk (xSubOneIdeal d) (zSuccInGeneratedRing d 0) =
            Ideal.Quotient.mk (xSubOneIdeal d) (zInGeneratedRing d) := by
        rw [Ideal.Quotient.mk_eq_mk_iff_sub_mem]
        have hzR : zInGeneratedRing d =
            xInGeneratedRing d * zSuccInGeneratedRing d 0 := by
          apply Subtype.ext
          simpa [xInGeneratedRing, zInGeneratedRing, zSuccInGeneratedRing]
            using z_eq_X_mul_zTail_one d
        have hxmem : xInGeneratedRing d - 1 ∈ xSubOneIdeal d :=
          Ideal.subset_span (by simp [xSubOneIdeal])
        rw [hzR]
        have hdiff : zSuccInGeneratedRing d 0 -
            xInGeneratedRing d * zSuccInGeneratedRing d 0 =
            -(xInGeneratedRing d - 1) * zSuccInGeneratedRing d 0 := by ring
        rw [hdiff]
        have hmem := (xSubOneIdeal d).neg_mem
          ((xSubOneIdeal d).mul_mem_right
            (zSuccInGeneratedRing d 0) hxmem)
        convert hmem using 1 <;> ring
      simpa [g, qz] using hzero
  | succ n ih =>
      obtain ⟨p, hp⟩ := ih
      refine ⟨p - Polynomial.C (d.coefficients (n + 1)), ?_⟩
      have hrecR : xInGeneratedRing d * zSuccInGeneratedRing d (n + 1) +
          algebraMap k (R d) (d.coefficients (n + 1)) =
            zSuccInGeneratedRing d n := by
        apply Subtype.ext
        change PowerSeries.X * zTail (k := k) d.coefficients (n + 2) +
            PowerSeries.C (d.coefficients (n + 1)) =
          zTail (k := k) d.coefficients (n + 1)
        exact X_mul_zTail_succ_add_coeff_eq_zTail d (by omega)
      have hxQ : Ideal.Quotient.mk (xSubOneIdeal d) (xInGeneratedRing d) = 1 :=
        (Ideal.Quotient.mk_eq_one_iff_sub_mem
          (I := xSubOneIdeal d) (xInGeneratedRing d)).2
          (Ideal.subset_span (by simp [xSubOneIdeal]))
      have hrecQ := congrArg (Ideal.Quotient.mk (xSubOneIdeal d)) hrecR
      rw [map_add, map_mul, hxQ] at hrecQ
      have hrecQ' :
          Ideal.Quotient.mk (xSubOneIdeal d) (zSuccInGeneratedRing d (n + 1)) +
            algebraMap k (R d ⧸ xSubOneIdeal d) (d.coefficients (n + 1)) =
          Ideal.Quotient.mk (xSubOneIdeal d) (zSuccInGeneratedRing d n) := by
        simpa using hrecQ
      change Ideal.Quotient.mk (xSubOneIdeal d)
          (zSuccInGeneratedRing d (n + 1)) =
        g (p - Polynomial.C (d.coefficients (n + 1)))
      calc
        Ideal.Quotient.mk (xSubOneIdeal d)
            (zSuccInGeneratedRing d (n + 1)) =
          g p - algebraMap k (R d ⧸ xSubOneIdeal d)
              (d.coefficients (n + 1)) := by
          have htail_eq :
              Ideal.Quotient.mk (xSubOneIdeal d)
                  (zSuccInGeneratedRing d (n + 1)) =
                Ideal.Quotient.mk (xSubOneIdeal d)
                    (zSuccInGeneratedRing d n) -
                  algebraMap k (R d ⧸ xSubOneIdeal d)
                    (d.coefficients (n + 1)) := by
            rw [← hrecQ']
            ring
          rw [htail_eq, hp]
        _ = g (p - Polynomial.C (d.coefficients (n + 1))) := by
          rw [map_sub]
          congr 1
          simp [g, Polynomial.eval₂RingHom]

private theorem quotient_xSubOneIdeal_kernel
    (d : PowerSeriesData k)
    (xP zP : Polynomial (Polynomial k))
    (L : Type u) [CommRing L] [Algebra (Polynomial (Polynomial k)) L]
    (xK zK : FractionRing (R d))
    (eLoc : L →+* FractionRing (R d))
    (heLoc : Function.Injective eLoc)
    (evalP : Polynomial (Polynomial k) →+* Polynomial k)
    (evalL : L →+* Polynomial k)
    (hevalP_x : evalP xP = 1)
    (hevalP_z : evalP zP = Polynomial.X)
    (hevalP_eval : ∀ p : Polynomial k,
      evalP (Polynomial.eval₂ (algebraMap k (Polynomial (Polynomial k)))
        (Polynomial.X : Polynomial (Polynomial k)) p) = p)
    (hevalL_alg : ∀ p : Polynomial (Polynomial k),
      evalL (algebraMap (Polynomial (Polynomial k)) L p) = evalP p)
    (heLoc_alg : ∀ p : Polynomial (Polynomial k),
      eLoc (algebraMap (Polynomial (Polynomial k)) L p) = xzPolynomialMap d p)
    (hrange : ∀ (y : PowerSeries k) (hy : y ∈ generatedRing d),
      ∃ q : L, eLoc q = algebraMap (R d) (FractionRing (R d)) ⟨y, hy⟩)
    (qz : R d ⧸ xSubOneIdeal d)
    (g : Polynomial k →+* (R d ⧸ xSubOneIdeal d))
    (hxP : xP = Polynomial.C Polynomial.X)
    (hzP : zP = Polynomial.X)
    (hxK : xK = algebraMap (R d) (FractionRing (R d)) (xInGeneratedRing d))
    (hzK : zK = algebraMap (R d) (FractionRing (R d)) (zInGeneratedRing d))
    (hqz : qz = Ideal.Quotient.mk (xSubOneIdeal d) (zInGeneratedRing d))
    (hg : g = Polynomial.eval₂RingHom
      (algebraMap k (R d ⧸ xSubOneIdeal d)) qz) :
    RingHom.ker g = ⊥ := by
  subst xP
  subst zP
  subst xK
  subst zK
  subst qz
  subst g
  let xP : Polynomial (Polynomial k) := Polynomial.C Polynomial.X
  let zP : Polynomial (Polynomial k) := Polynomial.X
  let xK : FractionRing (R d) :=
    algebraMap (R d) (FractionRing (R d)) (xInGeneratedRing d)
  let zK : FractionRing (R d) :=
    algebraMap (R d) (FractionRing (R d)) (zInGeneratedRing d)
  let qz : R d ⧸ xSubOneIdeal d :=
    Ideal.Quotient.mk (xSubOneIdeal d) (zInGeneratedRing d)
  let g : Polynomial k →+* (R d ⧸ xSubOneIdeal d) :=
    Polynomial.eval₂RingHom (algebraMap k (R d ⧸ xSubOneIdeal d)) qz
  apply le_antisymm
  · intro p hp
    rw [RingHom.mem_ker] at hp
    let pR : R d :=
      Polynomial.eval₂ (algebraMap k (R d)) (zInGeneratedRing d) p
    have hgp : g p = Ideal.Quotient.mk (xSubOneIdeal d) pR := by
      change Polynomial.eval₂ (algebraMap k (R d ⧸ xSubOneIdeal d)) qz p =
        Ideal.Quotient.mk (xSubOneIdeal d)
          (Polynomial.eval₂ (algebraMap k (R d)) (zInGeneratedRing d) p)
      rw [Polynomial.hom_eval₂]
      rfl
    have hpRmem : pR ∈ xSubOneIdeal d := by
      rw [← Ideal.Quotient.eq_zero_iff_mem]
      rw [← hgp]
      exact hp
    obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.mp hpRmem
    obtain ⟨q, hq⟩ := hrange a.1 a.2
    let pP : Polynomial (Polynomial k) :=
      Polynomial.eval₂ (algebraMap k (Polynomial (Polynomial k))) zP p
    have hmap_p :
        algebraMap (R d) (FractionRing (R d)) pR =
          Polynomial.eval₂ (algebraMap k (FractionRing (R d))) zK p := by
      simpa [pR, zK] using algebraMap_eval₂_z d p
    have heLoc_pP :
        eLoc (algebraMap (Polynomial (Polynomial k)) L pP) =
          Polynomial.eval₂ (algebraMap k (FractionRing (R d))) zK p := by
      rw [heLoc_alg]
      simpa [pP, zP, zK] using xzPolynomialMap_eval₂_X d p
    have hprod := congrArg (algebraMap (R d) (FractionRing (R d))) ha
    rw [map_mul] at hprod
    have hprod' :
        algebraMap (R d) (FractionRing (R d)) a * (xK - 1) =
          algebraMap (R d) (FractionRing (R d)) pR := by
      simpa [xK] using hprod
    have hqeq :
        algebraMap (Polynomial (Polynomial k)) L pP =
          (algebraMap (Polynomial (Polynomial k)) L xP - 1) * q := by
      apply heLoc
      calc
        eLoc (algebraMap (Polynomial (Polynomial k)) L pP) =
            algebraMap (R d) (FractionRing (R d)) pR := by
              rw [heLoc_pP, ← hmap_p]
        _ = algebraMap (R d) (FractionRing (R d)) a * (xK - 1) :=
              hprod'.symm
        _ = (xK - 1) * algebraMap (R d) (FractionRing (R d)) a := by ring
        _ = eLoc ((algebraMap (Polynomial (Polynomial k)) L xP - 1) * q) := by
          rw [map_mul, map_sub, heLoc_alg, hq]
          simp [xP, xK, xzPolynomialMap]
    have heval_pP :
        evalL (algebraMap (Polynomial (Polynomial k)) L pP) = p := by
      rw [hevalL_alg]
      simpa [pP, zP] using hevalP_eval p
    have heval_eq := congrArg evalL hqeq
    rw [heval_pP, map_mul, map_sub, hevalL_alg] at heval_eq
    have hx : evalP xP = 1 := by simpa [xP] using hevalP_x
    rw [hx, map_one, sub_self, zero_mul] at heval_eq
    simpa using heval_eq
  · exact bot_le

/-- The quotient by `(x - 1)` is the polynomial ring `k[z]`. -/
private theorem quotient_xSubOneIdeal_equiv_with_z (d : PowerSeriesData k) :
    ∃ e : R d ⧸ xSubOneIdeal d ≃+* Polynomial k,
      e (Ideal.Quotient.mk (xSubOneIdeal d) (zInGeneratedRing d)) =
        Polynomial.X := by
  let xP : Polynomial (Polynomial k) := Polynomial.C Polynomial.X
  let zP : Polynomial (Polynomial k) := Polynomial.X
  let L := Localization.Away xP
  let xK : FractionRing (R d) :=
    algebraMap (R d) (FractionRing (R d)) (xInGeneratedRing d)
  let zK : FractionRing (R d) :=
    algebraMap (R d) (FractionRing (R d)) (zInGeneratedRing d)
  have hxK : xK ≠ 0 := by
    intro h
    have h' : algebraMap (R d) (FractionRing (R d))
        (xInGeneratedRing d) = algebraMap (R d) (FractionRing (R d)) 0 := by
      simpa [xK] using h
    have hR : xInGeneratedRing d = 0 :=
      (IsFractionRing.injective (R d) (FractionRing (R d))) h'
    have hX : (PowerSeries.X : PowerSeries k) = 0 :=
      congrArg Subtype.val hR
    have hcoeff := congrArg (PowerSeries.coeff 1) hX
    norm_num at hcoeff
  have heK : Function.Injective (xzPolynomialMap d) :=
    xzPolynomialMap_injective d
  letI : CommRing L := inferInstance
  have hunit : ∀ y : Submonoid.powers xP,
      IsUnit (xzPolynomialMap d y) := by
    intro y
    obtain ⟨n, hn⟩ := y.property
    rw [← hn, map_pow]
    have hxmap : xzPolynomialMap d xP = xK := by
      simp [xzPolynomialMap, xP, xK]
    rw [hxmap]
    exact isUnit_iff_ne_zero.mpr (pow_ne_zero n hxK)
  let eLoc : L →+* FractionRing (R d) :=
    IsLocalization.lift hunit
  have heLoc : Function.Injective eLoc := by
    change Function.Injective (IsLocalization.lift hunit)
    rw [IsLocalization.lift_injective_iff]
    intro a b
    constructor
    · intro h
      have h' := congrArg (IsLocalization.lift hunit) h
      simpa only [IsLocalization.lift_eq] using h'
    · intro h
      apply congrArg (algebraMap (Polynomial (Polynomial k)) L)
      apply heK
      exact h
  let evalP : Polynomial (Polynomial k) →+* Polynomial k :=
    Polynomial.eval₂RingHom
      (Polynomial.eval₂RingHom (Polynomial.C : k →+* Polynomial k) 1) Polynomial.X
  have hevalP_x : evalP xP = 1 := by
    simp [evalP, xP]
  have hevalP_z : evalP zP = Polynomial.X := by
    simp [evalP, zP]
  have hevalP_x_unit : IsUnit (evalP xP) := by
    rw [hevalP_x]
    exact isUnit_one
  let evalL : L →+* Polynomial k :=
    IsLocalization.Away.lift xP hevalP_x_unit
  have hevalL_alg (p : Polynomial (Polynomial k)) :
      evalL (algebraMap (Polynomial (Polynomial k)) L p) = evalP p := by
    exact IsLocalization.Away.lift_eq xP _ p
  have heLoc_alg (p : Polynomial (Polynomial k)) :
      eLoc (algebraMap (Polynomial (Polynomial k)) L p) =
        xzPolynomialMap d p := by
    change IsLocalization.lift hunit
        (algebraMap (Polynomial (Polynomial k)) L p) = _
    exact IsLocalization.lift_eq hunit p
  have heLoc_scalar (c : k) :
      eLoc (algebraMap k L c) = algebraMap k (FractionRing (R d)) c := by
    change eLoc (algebraMap (Polynomial (Polynomial k)) L
      (algebraMap k (Polynomial (Polynomial k)) c)) = _
    rw [heLoc_alg]
    simp [xzPolynomialMap]
  have hinvLoc :
      eLoc (IsLocalization.Away.invSelf xP) = xK⁻¹ := by
    have hxmap : xzPolynomialMap d xP = xK := by
      simp [xzPolynomialMap, xP, xK]
    apply (mul_left_cancel₀ hxK)
    calc
      xK * eLoc (IsLocalization.Away.invSelf xP) =
          eLoc (algebraMap (Polynomial (Polynomial k)) L xP) *
            eLoc (IsLocalization.Away.invSelf xP) := by rw [heLoc_alg, hxmap]
      _ = eLoc (algebraMap (Polynomial (Polynomial k)) L xP *
          IsLocalization.Away.invSelf xP) := by rw [map_mul]
      _ = 1 := by rw [IsLocalization.Away.mul_invSelf, map_one]
      _ = xK * xK⁻¹ := by rw [mul_inv_cancel₀ hxK]
  have htail : ∀ n : ℕ, ∃ q : L,
      eLoc q = algebraMap (R d) (FractionRing (R d))
        (zSuccInGeneratedRing d n) := by
    intro n
    induction n with
    | zero =>
        refine ⟨IsLocalization.Away.invSelf xP *
          algebraMap (Polynomial (Polynomial k)) L zP, ?_⟩
        have hzR : xInGeneratedRing d * zSuccInGeneratedRing d 0 =
            zInGeneratedRing d := by
          apply Subtype.ext
          exact (z_eq_X_mul_zTail_one d).symm
        have hzK := congrArg (algebraMap (R d) (FractionRing (R d))) hzR
        rw [map_mul] at hzK
        rw [map_mul, hinvLoc, heLoc_alg]
        have hzmap : xzPolynomialMap d zP = zK := by
          simp [xzPolynomialMap, zP, zK]
        rw [hzmap]
        calc
          xK⁻¹ * zK = xK⁻¹ *
              (xK * algebraMap (R d) (FractionRing (R d))
                (zSuccInGeneratedRing d 0)) := by rw [hzK]
          _ = algebraMap (R d) (FractionRing (R d))
                (zSuccInGeneratedRing d 0) := by
            rw [← mul_assoc, inv_mul_cancel₀ hxK, one_mul]
    | succ n ih =>
        obtain ⟨q, hq⟩ := ih
        refine ⟨IsLocalization.Away.invSelf xP *
          (q - algebraMap k L (d.coefficients (n + 1))), ?_⟩
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
        have hscalar (c : k) :
            algebraMap k (FractionRing (R d)) c =
              algebraMap (R d) (FractionRing (R d)) (algebraMap k (R d) c) := by
          rfl
        have hrecK' : xK * algebraMap (R d) (FractionRing (R d))
              (zSuccInGeneratedRing d (n + 1)) +
              algebraMap k (FractionRing (R d)) (d.coefficients (n + 1)) =
            algebraMap (R d) (FractionRing (R d))
              (zSuccInGeneratedRing d n) := by
          rw [hscalar]
          simpa [xK] using hrecK
        rw [map_mul, hinvLoc, map_sub, hq, heLoc_scalar]
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
      ∃ q : L, eLoc q = algebraMap (R d) (FractionRing (R d)) ⟨y, hy⟩ := by
    intro y hy
    refine Algebra.adjoin_induction
      (p := fun y hy =>
        ∃ q : L, eLoc q = algebraMap (R d) (FractionRing (R d)) ⟨y, hy⟩)
      ?_ ?_ ?_ ?_ hy
    · rintro y (rfl | hy)
      · refine ⟨algebraMap (Polynomial (Polynomial k)) L xP, ?_⟩
        rw [heLoc_alg]
        change xzPolynomialMap d xP = xK
        simp [xzPolynomialMap, xP, xK]
      · rcases Set.mem_insert_iff.mp hy with rfl | hy
        · refine ⟨algebraMap (Polynomial (Polynomial k)) L zP, ?_⟩
          rw [heLoc_alg]
          change xzPolynomialMap d zP = zK
          simp [xzPolynomialMap, zP, zK]
        · rcases Set.mem_range.mp hy with ⟨n, rfl⟩
          obtain ⟨q, hq⟩ := htail n
          exact ⟨q, hq.trans (by rfl)⟩
    · intro c
      refine ⟨algebraMap k L c, ?_⟩
      rw [heLoc_scalar]
      rfl
    · intro y z _ _ hy hz
      rcases hy with ⟨qy, hqy⟩
      rcases hz with ⟨qz, hqz⟩
      refine ⟨qy + qz, ?_⟩
      rw [map_add, hqy, hqz, ← map_add]
      rfl
    · intro y z _ _ hy hz
      rcases hy with ⟨qy, hqy⟩
      rcases hz with ⟨qz, hqz⟩
      refine ⟨qy * qz, ?_⟩
      rw [map_mul, hqy, hqz, ← map_mul]
      rfl
  let qz : R d ⧸ xSubOneIdeal d :=
    Ideal.Quotient.mk (xSubOneIdeal d) (zInGeneratedRing d)
  let g : Polynomial k →+* (R d ⧸ xSubOneIdeal d) :=
    Polynomial.eval₂RingHom
      (algebraMap k (R d ⧸ xSubOneIdeal d)) qz
  have htailQ : ∀ n : ℕ, ∃ p : Polynomial k,
      Ideal.Quotient.mk (xSubOneIdeal d) (zSuccInGeneratedRing d n) = g p :=
    quotient_xSubOneIdeal_tailQ d qz g (by rfl) (by rfl)
  have hg_surjective : Function.Surjective g := by
    intro r
    obtain ⟨r0, rfl⟩ := Ideal.Quotient.mk_surjective r
    have hquot_gen := quotient_xSubOne_generated_surjective d g htailQ
      (by simp [g, qz]) (by intro c; simp [g])
    obtain ⟨p, hp⟩ := hquot_gen r0.1 r0.2
    exact ⟨p, hp.symm⟩
  have hevalP_eval : ∀ p : Polynomial k,
      evalP (Polynomial.eval₂ (algebraMap k (Polynomial (Polynomial k)))
        (Polynomial.X : Polynomial (Polynomial k)) p) = p := by
    intro p
    simpa [evalP] using evalP_eval_X (k := k) p
  have hker : RingHom.ker g = ⊥ :=
    quotient_xSubOneIdeal_kernel d xP zP L xK zK eLoc heLoc evalP evalL
      hevalP_x hevalP_z hevalP_eval hevalL_alg heLoc_alg hrange qz g
      (by rfl) (by rfl)
      (by rfl) (by rfl) (by rfl) (by rfl)
  let eQ := RingHom.quotientKerEquivOfSurjective (f := g) hg_surjective
  let e : R d ⧸ xSubOneIdeal d ≃+* Polynomial k :=
    eQ.symm.trans ((Ideal.quotEquivOfEq hker).trans
      (RingEquiv.quotientBot (Polynomial k)))
  refine ⟨e, ?_⟩
  dsimp [e]
  have hgX : g Polynomial.X =
      Ideal.Quotient.mk (xSubOneIdeal d) (zInGeneratedRing d) := by
    simp [g, qz]
  rw [← hgX]
  rw [RingHom.quotientKerEquivOfSurjective_symm_apply]
  simp

theorem quotient_xSubOneIdeal_equiv (d : PowerSeriesData k) :
    Nonempty (R d ⧸ xSubOneIdeal d ≃+* Polynomial k) := by
  rcases quotient_xSubOneIdeal_equiv_with_z d with ⟨e, _⟩
  exact ⟨e⟩

theorem nIdeal_eq_span_xSubOne_z (d : PowerSeriesData k) :
    nIdeal d = Ideal.span {xInGeneratedRing d - 1, zInGeneratedRing d} := by
  let J : Ideal (R d) :=
    Ideal.span {xInGeneratedRing d - 1, zInGeneratedRing d}
  change nIdeal d = J
  have hx1 : xInGeneratedRing d - 1 ∈ J :=
    Ideal.subset_span (by simp [J])
  have hz : zInGeneratedRing d ∈ J :=
    Ideal.subset_span (by simp [J])
  have hgen : ∀ j : ℕ, nGenerator d j ∈ J := by
    intro j
    induction j with
    | zero =>
        have hmem := J.sub_mem hz (J.mul_mem_right
          (zSuccInGeneratedRing d 0) hx1)
        have heq : nGenerator d 0 =
            zInGeneratedRing d -
              (xInGeneratedRing d - 1) * zSuccInGeneratedRing d 0 := by
          apply Subtype.ext
          simp only [nGenerator, initialCoefficientSum, Finset.sum_range_zero,
            map_zero, add_zero]
          change zTail (k := k) d.coefficients 1 =
            zPowerSeries (k := k) d.coefficients -
              (PowerSeries.X - 1) * zTail (k := k) d.coefficients 1
          rw [z_eq_X_mul_zTail_one d]
          ring
        rw [heq]
        exact hmem
    | succ j ih =>
        have hrec := X_mul_zTail_succ_add_coeff_eq_zTail d (by omega : 1 ≤ j + 1)
        have hnrec : nGenerator d j =
            nGenerator d (j + 1) +
              (xInGeneratedRing d - 1) * zSuccInGeneratedRing d (j + 1) := by
          apply Subtype.ext
          change zTail (k := k) d.coefficients (j + 1) +
              PowerSeries.C (initialCoefficientSum d j) =
            (zTail (k := k) d.coefficients (j + 2) +
                PowerSeries.C (initialCoefficientSum d (j + 1))) +
              (PowerSeries.X - 1) * zTail (k := k) d.coefficients (j + 2)
          have hsum : initialCoefficientSum d (j + 1) =
              initialCoefficientSum d j + d.coefficients (j + 1) := by
            simp [initialCoefficientSum, Finset.sum_range_succ]
          rw [hsum]
          rw [← hrec]
          rw [map_add]
          ring
        have hmem := J.sub_mem ih (J.mul_mem_right
          (zSuccInGeneratedRing d (j + 1)) hx1)
        convert hmem using 1
        rw [hnrec]
        ring
  apply le_antisymm
  · rw [nIdeal, Ideal.span_le]
    intro y hy
    rcases Set.mem_insert_iff.mp hy with rfl | hy
    · exact hx1
    · rcases Set.mem_range.mp hy with ⟨j, rfl⟩
      exact hgen j
  · rw [Ideal.span_le]
    intro y hy
    rcases Set.mem_insert_iff.mp hy with rfl | rfl
    · exact Ideal.subset_span (by simp [nIdeal])
    · have hn0 : nGenerator d 0 ∈ nIdeal d :=
        Ideal.subset_span (by
          simp [nIdeal])
      have hz1 : zSuccInGeneratedRing d 0 ∈ nIdeal d := by
        simpa [nGenerator, initialCoefficientSum] using hn0
      have hzR : zInGeneratedRing d =
          xInGeneratedRing d * zSuccInGeneratedRing d 0 := by
        apply Subtype.ext
        simpa [xInGeneratedRing, zInGeneratedRing, zSuccInGeneratedRing]
          using z_eq_X_mul_zTail_one d
      have hmem := (nIdeal d).mul_mem_right
        (xInGeneratedRing d) hz1
      rw [hzR]
      simpa [mul_comm] using hmem

/-- The ideal `𝔫` is maximal. -/
theorem nIdeal_isMaximal (d : PowerSeriesData k) :
    (nIdeal d).IsMaximal := by
  rcases quotient_xSubOneIdeal_equiv_with_z d with ⟨e, hez⟩
  let q : R d →+* R d ⧸ xSubOneIdeal d :=
    Ideal.Quotient.mk (xSubOneIdeal d)
  let f : R d →+* k :=
    Polynomial.constantCoeff.comp (e.toRingHom.comp q)
  have hez' : e (q (zInGeneratedRing d)) = Polynomial.X := by
    simpa [q] using hez
  have hxJ : xInGeneratedRing d - 1 ∈
      Ideal.span {xInGeneratedRing d - 1, zInGeneratedRing d} := by
    exact Ideal.subset_span (by simp)
  have hzJ : zInGeneratedRing d ∈
      Ideal.span {xInGeneratedRing d - 1, zInGeneratedRing d} := by
    exact Ideal.subset_span (by simp)
  have hkerJ : RingHom.ker f =
      Ideal.span {xInGeneratedRing d - 1, zInGeneratedRing d} := by
    apply le_antisymm
    · intro r hr
      change Polynomial.constantCoeff (e (q r)) = 0 at hr
      have hpoly : e (q r) ∈
          Ideal.span {(Polynomial.X : Polynomial k)} := by
        rw [← Polynomial.ker_constantCoeff]
        exact hr
      obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.mp hpoly
      let a₀ := e.symm a
      obtain ⟨s, hs⟩ := Ideal.Quotient.mk_surjective a₀
      have hea : e a₀ = a := by
        simp [a₀]
      have heq : e (q r) = e (q (zInGeneratedRing d) * q s) := by
        rw [map_mul, hez', hs, hea]
        simpa [mul_comm] using ha.symm
      have hqr : q r = q (zInGeneratedRing d) * q s :=
        e.injective heq
      have hdiff : r - zInGeneratedRing d * s ∈ xSubOneIdeal d := by
        rw [← Ideal.Quotient.eq_zero_iff_mem]
        change q (r - zInGeneratedRing d * s) = 0
        rw [map_sub, map_mul, hqr]
        ring
      obtain ⟨b, hb⟩ := by
        rw [xSubOneIdeal] at hdiff
        exact Ideal.mem_span_singleton'.mp hdiff
      have hdiff' : r - zInGeneratedRing d * s ∈
          Ideal.span {xInGeneratedRing d - 1, zInGeneratedRing d} := by
        rw [← hb]
        simpa [mul_comm] using
          (Ideal.span {xInGeneratedRing d - 1, zInGeneratedRing d}).mul_mem_right b hxJ
      have hzs : zInGeneratedRing d * s ∈
          Ideal.span {xInGeneratedRing d - 1, zInGeneratedRing d} := by
        have h := (Ideal.span {xInGeneratedRing d - 1, zInGeneratedRing d}).mul_mem_right s hzJ
        simpa [mul_comm] using h
      simpa [sub_add_cancel] using
        (Ideal.span {xInGeneratedRing d - 1, zInGeneratedRing d}).add_mem hdiff' hzs
    · rw [Ideal.span_le]
      intro r hr
      change Polynomial.constantCoeff (e (q r)) = 0
      rcases Set.mem_insert_iff.mp hr with rfl | rfl
      · have hq : q (xInGeneratedRing d - 1) = 0 := by
          change Ideal.Quotient.mk (xSubOneIdeal d)
            (xInGeneratedRing d - 1) = 0
          rw [Ideal.Quotient.eq_zero_iff_mem]
          exact Ideal.subset_span (by simp [xSubOneIdeal])
        rw [hq]
        simp
      · rw [hez']
        simp
  have hker : RingHom.ker f = nIdeal d := by
    rw [nIdeal_eq_span_xSubOne_z d]
    exact hkerJ
  have hf : Function.Surjective f := by
    intro c
    obtain ⟨r, hr⟩ :=
      Ideal.Quotient.mk_surjective (e.symm (Polynomial.C c))
    refine ⟨r, ?_⟩
    change Polynomial.constantCoeff (e (q r)) = c
    have hqr : q r = e.symm (Polynomial.C c) := by
      simpa [q] using hr
    rw [hqr]
    simp
  let eF := (Ideal.quotEquivOfEq hker.symm).trans
    (RingHom.quotientKerEquivOfSurjective (f := f) hf)
  apply Ideal.Quotient.maximal_of_isField
  exact eF.toMulEquiv.isField (Field.toIsField k)

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
  intro r hr
  have hconst : PowerSeries.constantCoeff (r : PowerSeries k) ≠ 0 := by
    intro hzero
    apply hr
    have h := generatedRing_sub_constantCoeff_mem_mIdeal d r.1 r.2
    simpa [hzero] using h
  change IsUnit (r : PowerSeries k)
  rw [PowerSeries.isUnit_iff_constantCoeff]
  exact isUnit_iff_ne_zero.mpr hconst

/-- The localization `R_𝔪` embeds in `k⟦x⟧`. -/
theorem localization_m_embeds_in_powerSeries (d : PowerSeriesData k) :
    ∃ f : Localization.AtPrime (mIdeal d) →+* PowerSeries k,
      Function.Injective f ∧
        f.comp (algebraMap (R d) (Localization.AtPrime (mIdeal d))) =
          generatedRingInclusion d := by
  have hunit : ∀ y : (mIdeal d).primeCompl,
      IsUnit (generatedRingInclusion d y) := by
    intro y
    exact non_m_maps_to_powerSeries_unit d y.1 (show y.1 ∉ mIdeal d from y.2)
  let f : Localization.AtPrime (mIdeal d) →+* PowerSeries k :=
    IsLocalization.lift (M := (mIdeal d).primeCompl)
      (g := generatedRingInclusion d) hunit
  refine ⟨f, ?_, ?_⟩
  · rw [IsLocalization.lift_injective_iff]
    intro x y
    constructor
    · intro h
      exact IsLocalization.eq_of_eq hunit h
    · intro h
      have hxy : x = y := by
        apply Subtype.ext
        exact h
      exact congrArg (algebraMap (R d) (Localization.AtPrime (mIdeal d))) hxy
  · exact IsLocalization.lift_comp hunit

/-- `R_𝔪` is a discrete valuation ring with residue field `k`. -/
theorem localization_m_is_dvr (d : PowerSeriesData k) :
    IsDiscreteValuationRing (Localization.AtPrime (mIdeal d)) := by
  have hfactor : ∀ (n : ℕ) (r : R d),
      generatedRingInclusion d r ≠ 0 →
        PowerSeries.order (generatedRingInclusion d r) = n →
          ∃ u : R d, r = xInGeneratedRing d ^ n * u ∧
            PowerSeries.constantCoeff (generatedRingInclusion d u) ≠ 0 := by
    intro n
    induction n with
    | zero =>
        intro r hr horder
        have hconst : PowerSeries.constantCoeff (generatedRingInclusion d r) ≠ 0 := by
          intro hzero
          have horder' := (PowerSeries.order_ne_zero_iff_constCoeff_eq_zero).2 hzero
          rw [horder] at horder'
          simp at horder'
        exact ⟨r, by simp, hconst⟩
    | succ n ih =>
        intro r hr horder
        have hconst : PowerSeries.constantCoeff (generatedRingInclusion d r) = 0 := by
          apply (PowerSeries.order_ne_zero_iff_constCoeff_eq_zero).1
          rw [horder]
          simp
        have hrmem : r ∈ mIdeal d := by
          have h := generatedRing_sub_constantCoeff_mem_mIdeal d r.1 r.2
          have hconst' : PowerSeries.constantCoeff (r : PowerSeries k) = 0 := hconst
          rw [hconst', map_zero, sub_zero] at h
          exact h
        obtain ⟨u, hu⟩ := Ideal.mem_span_singleton'.mp
          (show r ∈ Ideal.span {xInGeneratedRing d} from by
            simpa [mIdeal] using hrmem)
        have hru : r = xInGeneratedRing d * u := by
          simpa [mul_comm] using hu.symm
        have hu0 : generatedRingInclusion d u ≠ 0 := by
          intro hzero
          apply hr
          simp [hru, hzero]
        have horderu : PowerSeries.order (generatedRingInclusion d u) = n := by
          have hmul := congrArg PowerSeries.order
            (congrArg (fun z : R d => generatedRingInclusion d z) hru)
          rw [map_mul, PowerSeries.order_mul] at hmul
          have hxmap : generatedRingInclusion d (xInGeneratedRing d) =
              PowerSeries.X := rfl
          rw [hxmap, PowerSeries.order_X, horder] at hmul
          rw [← PowerSeries.coe_toNat_order hu0] at hmul
          have hmulNat : n + 1 =
              1 + (generatedRingInclusion d u).order.toNat := by
            exact_mod_cast hmul
          have horderNat : (generatedRingInclusion d u).order.toNat = n := by
            omega
          rw [← horderNat]
          exact (PowerSeries.coe_toNat_order hu0).symm
        obtain ⟨v, hv, hvc⟩ := ih u hu0 horderu
        refine ⟨v, ?_, hvc⟩
        rw [hru, hv]
        calc
          xInGeneratedRing d * (xInGeneratedRing d ^ n * v) =
              (xInGeneratedRing d ^ n * xInGeneratedRing d) * v := by ring
          _ = xInGeneratedRing d ^ (n + 1) * v := by rw [pow_succ]
  have hmapinj : Function.Injective
      (algebraMap (R d) (Localization.AtPrime (mIdeal d))) := by
    rw [IsLocalization.injective_iff_isRegular (mIdeal d).primeCompl]
    intro y
    refine ⟨?_, ?_⟩
    · intro a b hab
      change (↑y : R d) * a = ↑y * b at hab
      apply sub_eq_zero.mp
      apply (mem_nonZeroDivisors_iff.mp
        ((mIdeal d).primeCompl_le_nonZeroDivisors y.2)).1
      rw [mul_sub, hab, sub_self]
    · intro a b hab
      change a * (↑y : R d) = b * ↑y at hab
      apply sub_eq_zero.mp
      apply (mem_nonZeroDivisors_iff.mp
        ((mIdeal d).primeCompl_le_nonZeroDivisors y.2)).2
      rw [sub_mul, hab, sub_self]
  have hfactorS : ∀ a : Localization.AtPrime (mIdeal d), a ≠ 0 →
      ∃ n : ℕ, ∃ u : (Localization.AtPrime (mIdeal d))ˣ,
        (algebraMap (R d) (Localization.AtPrime (mIdeal d))
          (xInGeneratedRing d)) ^ n * (u : Localization.AtPrime (mIdeal d)) = a := by
    intro a ha
    obtain ⟨r, s, hrs⟩ :=
      IsLocalization.exists_mk'_eq (mIdeal d).primeCompl a
    have hmk : IsLocalization.mk' (Localization.AtPrime (mIdeal d)) r s ≠ 0 := by
      simpa [hrs] using ha
    have hr0 : r ≠ 0 := IsLocalization.ne_zero_of_mk'_ne_zero
      (S := Localization.AtPrime (mIdeal d))
      (M := (mIdeal d).primeCompl) hmk
    have hgr0 : generatedRingInclusion d r ≠ 0 := by
      intro h
      apply hr0
      apply Subtype.ext
      exact h
    obtain ⟨u, hru, huc⟩ := hfactor (generatedRingInclusion d r).order.toNat r
      hgr0 (PowerSeries.coe_toNat_order hgr0).symm
    have hum : u ∉ mIdeal d := by
      intro hum
      obtain ⟨v, hv⟩ := Ideal.mem_span_singleton'.mp
        (show u ∈ Ideal.span {xInGeneratedRing d} from by
          simpa [mIdeal] using hum)
      apply huc
      have hvu : u = v * xInGeneratedRing d := hv.symm
      rw [hvu, map_mul]
      have hxconst : PowerSeries.constantCoeff
          (generatedRingInclusion d (xInGeneratedRing d)) = 0 := by
        change PowerSeries.constantCoeff (PowerSeries.X : PowerSeries k) = 0
        simp
      rw [(PowerSeries.constantCoeff (R := k)).map_mul, hxconst, mul_zero]
    have hvunit : IsUnit (IsLocalization.mk'
        (Localization.AtPrime (mIdeal d)) u s) := by
      rw [IsLocalization.mk'_eq_mul_mk'_one]
      refine (IsLocalization.map_units _
        (⟨u, hum⟩ : (mIdeal d).primeCompl)).mul ?_
      refine isUnit_iff_exists_inv.mpr ⟨algebraMap (R d)
        (Localization.AtPrime (mIdeal d)) s, ?_⟩
      simpa [mul_comm] using
        (IsLocalization.mk'_spec (S := Localization.AtPrime (mIdeal d))
          (M := (mIdeal d).primeCompl) (1 : R d) s)
    refine ⟨(generatedRingInclusion d r).order.toNat,
      hvunit.unit, ?_⟩
    calc
      (algebraMap (R d) (Localization.AtPrime (mIdeal d))
          (xInGeneratedRing d)) ^ (generatedRingInclusion d r).order.toNat *
          IsLocalization.mk' (Localization.AtPrime (mIdeal d)) u s =
          IsLocalization.mk' (Localization.AtPrime (mIdeal d))
            (xInGeneratedRing d ^ (generatedRingInclusion d r).order.toNat * u) s := by
        rw [← map_pow, IsLocalization.mul_mk'_eq_mk'_of_mul]
      _ = IsLocalization.mk' (Localization.AtPrime (mIdeal d)) r s := by
        exact congrArg (fun z : R d =>
          IsLocalization.mk' (Localization.AtPrime (mIdeal d)) z s) hru.symm
      _ = a := hrs
  let p : Localization.AtPrime (mIdeal d) :=
    algebraMap (R d) (Localization.AtPrime (mIdeal d)) (xInGeneratedRing d)
  have hx0 : xInGeneratedRing d ≠ 0 := by
    intro hx
    apply PowerSeries.X_ne_zero (R := k)
    simpa [xInGeneratedRing] using congrArg Subtype.val hx
  have hp0 : p ≠ 0 := by
    intro hp
    apply hx0
    apply hmapinj
    simpa [p] using hp
  have hpnu : ¬ IsUnit p := by
    intro hpunit
    obtain ⟨s, hs, hdiv⟩ :=
      (IsLocalization.algebraMap_isUnit_iff
        (S := Localization.AtPrime (mIdeal d))
        (M := (mIdeal d).primeCompl)).mp (by simpa [p] using hpunit)
    obtain ⟨v, hv⟩ := hdiv
    apply hs
    rw [hv]
    exact (mIdeal d).mul_mem_right v (Ideal.subset_span (by simp [mIdeal]))
  have hpprime : Prime p := by
    refine ⟨hp0, hpnu, ?_⟩
    intro a b hab
    by_cases ha0 : a = 0
    · left
      simpa [ha0] using dvd_zero p
    by_cases hb0 : b = 0
    · right
      simpa [hb0] using dvd_zero p
    obtain ⟨na, ua, hfa⟩ := hfactorS a ha0
    obtain ⟨nb, ub, hfb⟩ := hfactorS b hb0
    have hfa' : p ^ na * (ua : Localization.AtPrime (mIdeal d)) = a := by
      simpa [p] using hfa
    have hfb' : p ^ nb * (ub : Localization.AtPrime (mIdeal d)) = b := by
      simpa [p] using hfb
    by_cases hna : na = 0
    · by_cases hnb : nb = 0
      · exfalso
        apply hpnu
        apply isUnit_of_dvd_unit hab
        have haunit : IsUnit a := by
          rw [← hfa', hna, pow_zero, one_mul]
          exact ua.isUnit
        have hbunit : IsUnit b := by
          rw [← hfb', hnb, pow_zero, one_mul]
          exact ub.isUnit
        exact haunit.mul hbunit
      · right
        rw [← hfb']
        exact dvd_mul_of_dvd_left (dvd_pow_self p hnb) _
    · left
      rw [← hfa']
      exact dvd_mul_of_dvd_left (dvd_pow_self p hna) _
  apply IsDiscreteValuationRing.ofHasUnitMulPowIrreducibleFactorization
  refine ⟨p, hpprime.irreducible, ?_⟩
  intro a ha
  obtain ⟨n, u, hu⟩ := hfactorS a ha
  refine ⟨n, ?_⟩
  exact ⟨u, by simpa [p] using hu⟩

theorem localization_m_is_noetherian_regular (d : PowerSeriesData k) :
    IsNoetherianRing (Localization.AtPrime (mIdeal d)) ∧
      IsRegularLocalRing (Localization.AtPrime (mIdeal d)) := by
  letI : IsDiscreteValuationRing (Localization.AtPrime (mIdeal d)) :=
    localization_m_is_dvr d
  letI : IsPrincipalIdealRing (Localization.AtPrime (mIdeal d)) :=
    ((IsDiscreteValuationRing.iff_pid_with_one_nonzero_prime
      (Localization.AtPrime (mIdeal d))).mp
      (inferInstance : IsDiscreteValuationRing (Localization.AtPrime (mIdeal d)))).1
  constructor
  · rw [isNoetherianRing_iff_ideal_fg]
    intro I
    exact Submodule.IsPrincipal.fg (IsPrincipalIdealRing.principal I)
  · infer_instance

theorem localization_m_has_dimension_one (d : PowerSeriesData k) :
    ringKrullDim (Localization.AtPrime (mIdeal d)) = 1 := by
  letI : IsDiscreteValuationRing (Localization.AtPrime (mIdeal d)) :=
    localization_m_is_dvr d
  exact IsDiscreteValuationRing.ringKrullDim_eq_one
    (Localization.AtPrime (mIdeal d))

theorem localization_m_has_residue_field_k (d : PowerSeriesData k) :
    Nonempty (IsLocalRing.ResidueField (Localization.AtPrime (mIdeal d)) ≃+* k) := by
  rcases quotient_mIdeal_equiv d with ⟨e⟩
  exact ⟨(@IsLocalization.AtPrime.equivQuotMaximalIdeal (R d) _ (mIdeal d)
    (mIdeal_isMaximal d) (Localization.AtPrime (mIdeal d)) _ _ _ _).symm.trans e⟩

/-- The residue field at `𝔫` is also `k`. -/
theorem quotient_nIdeal_equiv (d : PowerSeriesData k) :
    Nonempty (R d ⧸ nIdeal d ≃+* k) := by
  rcases quotient_xSubOneIdeal_equiv_with_z d with ⟨e, hez⟩
  let q : R d →+* R d ⧸ xSubOneIdeal d :=
    Ideal.Quotient.mk (xSubOneIdeal d)
  let f : R d →+* k :=
    Polynomial.constantCoeff.comp (e.toRingHom.comp q)
  have hez' : e (q (zInGeneratedRing d)) = Polynomial.X := by
    simpa [q] using hez
  have hxJ : xInGeneratedRing d - 1 ∈
      Ideal.span {xInGeneratedRing d - 1, zInGeneratedRing d} := by
    exact Ideal.subset_span (by simp)
  have hzJ : zInGeneratedRing d ∈
      Ideal.span {xInGeneratedRing d - 1, zInGeneratedRing d} := by
    exact Ideal.subset_span (by simp)
  have hker : RingHom.ker f = nIdeal d := by
    rw [nIdeal_eq_span_xSubOne_z d]
    apply le_antisymm
    · intro r hr
      change Polynomial.constantCoeff (e (q r)) = 0 at hr
      have hpoly : e (q r) ∈
          Ideal.span {(Polynomial.X : Polynomial k)} := by
        rw [← Polynomial.ker_constantCoeff]
        exact hr
      obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.mp hpoly
      let a₀ := e.symm a
      obtain ⟨s, hs⟩ := Ideal.Quotient.mk_surjective a₀
      have hea : e a₀ = a := by
        simp [a₀]
      have heq : e (q r) = e (q (zInGeneratedRing d) * q s) := by
        rw [map_mul, hez', hs, hea]
        simpa [mul_comm] using ha.symm
      have hqr : q r = q (zInGeneratedRing d) * q s :=
        e.injective heq
      have hdiff : r - zInGeneratedRing d * s ∈ xSubOneIdeal d := by
        rw [← Ideal.Quotient.eq_zero_iff_mem]
        change q (r - zInGeneratedRing d * s) = 0
        rw [map_sub, map_mul, hqr]
        ring
      obtain ⟨b, hb⟩ := by
        rw [xSubOneIdeal] at hdiff
        exact Ideal.mem_span_singleton'.mp hdiff
      have hdiff' : r - zInGeneratedRing d * s ∈
          Ideal.span {xInGeneratedRing d - 1, zInGeneratedRing d} := by
        rw [← hb]
        simpa [mul_comm] using
          (Ideal.span {xInGeneratedRing d - 1, zInGeneratedRing d}).mul_mem_right b hxJ
      have hzs : zInGeneratedRing d * s ∈
          Ideal.span {xInGeneratedRing d - 1, zInGeneratedRing d} := by
        have h := (Ideal.span {xInGeneratedRing d - 1, zInGeneratedRing d}).mul_mem_right s hzJ
        simpa [mul_comm] using h
      simpa [sub_add_cancel] using
        (Ideal.span {xInGeneratedRing d - 1, zInGeneratedRing d}).add_mem hdiff' hzs
    · rw [Ideal.span_le]
      intro r hr
      change Polynomial.constantCoeff (e (q r)) = 0
      rcases Set.mem_insert_iff.mp hr with rfl | rfl
      · have hq : q (xInGeneratedRing d - 1) = 0 := by
          change Ideal.Quotient.mk (xSubOneIdeal d)
            (xInGeneratedRing d - 1) = 0
          rw [Ideal.Quotient.eq_zero_iff_mem]
          exact Ideal.subset_span (by simp)
        rw [hq]
        simp
      · rw [hez']
        simp
  have hf : Function.Surjective f := by
    intro c
    obtain ⟨r, hr⟩ :=
      Ideal.Quotient.mk_surjective (e.symm (Polynomial.C c))
    refine ⟨r, ?_⟩
    change Polynomial.constantCoeff (e (q r)) = c
    have hqr : q r = e.symm (Polynomial.C c) := by
      simpa [q] using hr
    rw [hqr]
    simp
  let eF := (Ideal.quotEquivOfEq hker.symm).trans
    (RingHom.quotientKerEquivOfSurjective (f := f) hf)
  exact ⟨eF⟩

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
  let e : Polynomial k →+* k := Polynomial.evalRingHom 1
  have heX : e (Polynomial.X : Polynomial k) = 1 := by
    simp [e]
  have heunits : ∀ y : Submonoid.powers (Polynomial.X : Polynomial k), IsUnit (e y) := by
    rintro ⟨y, hy⟩
    obtain ⟨n, rfl⟩ := hy
    simp [map_pow, heX]
  let g : LaurentPolynomialRing k →+* k :=
    IsLocalization.lift (M := Submonoid.powers (Polynomial.X : Polynomial k))
      (g := e) heunits
  have hgcomp :
      g.comp (algebraMap (Polynomial k) (LaurentPolynomialRing k)) = e :=
    IsLocalization.lift_comp heunits
  have hgx : g (xInLaurentPolynomialRing k) = 1 := by
    change (g.comp (algebraMap (Polynomial k) (LaurentPolynomialRing k)))
      (Polynomial.X : Polynomial k) = 1
    rw [hgcomp, heX]
  have hgk (c : k) : g (algebraMap k (LaurentPolynomialRing k) c) = c := by
    change (g.comp (algebraMap (Polynomial k) (LaurentPolynomialRing k)))
      (Polynomial.C c) = c
    rw [hgcomp]
    simp [e]
  let J : Ideal (LaurentPolynomialRing k) :=
    Ideal.map (algebraMap (Polynomial k) (LaurentPolynomialRing k))
      (Ideal.span {(Polynomial.X : Polynomial k) - 1})
  have hker : RingHom.ker g = J := by
    apply le_antisymm
    · intro y hy
      obtain ⟨p, s, rfl⟩ :=
        IsLocalization.exists_mk'_eq (Submonoid.powers (Polynomial.X : Polynomial k)) y
      change g (IsLocalization.mk' (LaurentPolynomialRing k) p s) = 0 at hy
      have hp : e p = 0 := by
        have h := (IsLocalization.lift_mk'_spec heunits p 0 s).mp hy
        simpa using h
      have hpJ : p ∈ Ideal.span
          {(Polynomial.X : Polynomial k) - Polynomial.C 1} := by
        rw [← Polynomial.ker_evalRingHom (1 : k)]
        change e p = 0
        exact hp
      change IsLocalization.mk' (LaurentPolynomialRing k) p s ∈ J
      rw [IsLocalization.mk'_mem_map_algebraMap_iff]
      exact ⟨1, by simp, by simpa using hpJ⟩
    · rw [Ideal.map_le_iff_le_comap, Ideal.span_le]
      intro p hp
      rcases hp with rfl
      change (g.comp (algebraMap (Polynomial k) (LaurentPolynomialRing k)))
        ((Polynomial.X : Polynomial k) - 1) = 0
      rw [hgcomp]
      simp [e]
  let f : nPresentationRing k →+* k := Polynomial.eval₂RingHom g 0
  let I : Ideal (nPresentationRing k) :=
    Ideal.span {algebraMap (LaurentPolynomialRing k) (nPresentationRing k)
        (xInLaurentPolynomialRing k) - 1, Polynomial.X}
  have hkerF : RingHom.ker f = I := by
    apply le_antisymm
    · intro p hp
      change f p = 0 at hp
      have hc : g p.constantCoeff = 0 := by
        simpa [f] using hp
      have hpc : p.constantCoeff ∈ J := hker ▸ hc
      have hmapJ :
          J.map (algebraMap (LaurentPolynomialRing k) (nPresentationRing k)) ≤ I := by
        dsimp [J]
        rw [Ideal.map_le_iff_le_comap, Ideal.map_le_iff_le_comap, Ideal.span_le]
        intro c hc
        rcases Set.mem_singleton_iff.mp hc with rfl
        apply Ideal.subset_span
        left
        simp [xInLaurentPolynomialRing]
      have hC : Polynomial.C p.constantCoeff ∈ I := by
        apply hmapJ
        simpa using (Ideal.mem_map_of_mem
          (algebraMap (LaurentPolynomialRing k) (nPresentationRing k)) hpc)
      have hXI : Polynomial.X ∈ I := Ideal.subset_span (by simp [I])
      have hX : Polynomial.X * p.divX ∈ I := by
        have h := I.mul_mem_left p.divX hXI
        simpa [mul_comm] using h
      rw [← Polynomial.X_mul_divX_add p]
      exact I.add_mem hX hC
    · rw [Ideal.span_le]
      intro p hp
      change f p = 0
      rcases Set.mem_insert_iff.mp hp with rfl | rfl
      · have hfg : f (algebraMap (LaurentPolynomialRing k) (nPresentationRing k)
            (xInLaurentPolynomialRing k)) = g (xInLaurentPolynomialRing k) := by
          change f (Polynomial.C (xInLaurentPolynomialRing k)) =
            g (xInLaurentPolynomialRing k)
          simp [f]
        calc
          f (algebraMap (LaurentPolynomialRing k) (nPresentationRing k)
              (xInLaurentPolynomialRing k) - 1) =
              f (algebraMap (LaurentPolynomialRing k) (nPresentationRing k)
                (xInLaurentPolynomialRing k)) - f 1 := by rw [map_sub]
          _ = g (xInLaurentPolynomialRing k) - 1 := by rw [hfg, map_one]
          _ = 0 := by rw [hgx]; simp
      · change Polynomial.eval₂ g 0 (Polynomial.X : Polynomial (LaurentPolynomialRing k)) = 0
        simp
  have hf : Function.Surjective f := by
    intro c
    refine ⟨Polynomial.C (algebraMap k (LaurentPolynomialRing k) c), ?_⟩
    change Polynomial.eval₂ g 0
        (Polynomial.C (algebraMap k (LaurentPolynomialRing k) c)) = c
    rw [Polynomial.eval₂_C]
    exact hgk c
  let eF := (Ideal.quotEquivOfEq hkerF.symm).trans
    (RingHom.quotientKerEquivOfSurjective (f := f) hf)
  rw [show nPresentationIdeal k = I by rfl]
  apply Ideal.Quotient.maximal_of_isField
  exact eF.toMulEquiv.isField (Field.toIsField k)

instance nPresentationIdeal_isPrime_instance :
    (nPresentationIdeal k).IsPrime :=
  (nPresentationIdeal_isMaximal k).isPrime

private theorem localization_n_presentation_hrep_tail (d : PowerSeriesData k)
    (S : Type*) [CommRing S] [Algebra (R d) S]
    [Algebra k S] [IsScalarTower k (R d) S]
    [IsLocalization (nIdeal d).primeCompl S]
    (gP : nPresentationRing k →+* S)
    [IsScalarTower k (R d) S]
    (hgen_x : gP (algebraMap (LaurentPolynomialRing k) (nPresentationRing k)
        (xInLaurentPolynomialRing k)) =
      algebraMap (R d) S (xInGeneratedRing d))
    (hgen_z : gP (Polynomial.X : nPresentationRing k) =
      algebraMap (R d) S (zInGeneratedRing d))
    (hgP_C : ∀ c : k,
      gP (Polynomial.C (algebraMap k (LaurentPolynomialRing k) c)) = algebraMap k S c)
    (qx : (nPresentationIdeal k).primeCompl)
    (hqx : (qx : nPresentationRing k) = Polynomial.C (xInLaurentPolynomialRing k)) :
    ∀ n : ℕ, ∃ p : nPresentationRing k,
      ∃ q : (nPresentationIdeal k).primeCompl,
        algebraMap (R d) S (zSuccInGeneratedRing d n) * gP q = gP p := by
  intro n
  induction n with
  | zero =>
      refine ⟨Polynomial.X, qx, ?_⟩
      have hzR : xInGeneratedRing d * zSuccInGeneratedRing d 0 =
          zInGeneratedRing d := by
        apply Subtype.ext
        exact (z_eq_X_mul_zTail_one d).symm
      have hzS := congrArg (algebraMap (R d) S) hzR
      rw [map_mul] at hzS
      change algebraMap (R d) S (zSuccInGeneratedRing d 0) * gP qx =
        gP Polynomial.X
      have hqxS : gP qx = algebraMap (R d) S (xInGeneratedRing d) := by
        rw [hqx]
        change gP (Polynomial.C (xInLaurentPolynomialRing k)) = _
        exact hgen_x
      rw [hqxS, hgen_z, ← hzS]
      ring
  | succ n ih =>
      rcases ih with ⟨p, q, hq⟩
      let c : k := d.coefficients (n + 1)
      let pc : nPresentationRing k :=
        Polynomial.C (algebraMap k (LaurentPolynomialRing k) c)
      have hrecR : xInGeneratedRing d * zSuccInGeneratedRing d (n + 1) +
          algebraMap k (R d) c = zSuccInGeneratedRing d n := by
        apply Subtype.ext
        change PowerSeries.X * zTail (k := k) d.coefficients (n + 2) +
            PowerSeries.C c = zTail (k := k) d.coefficients (n + 1)
        exact X_mul_zTail_succ_add_coeff_eq_zTail d (by omega)
      have hrecS := congrArg (algebraMap (R d) S) hrecR
      rw [map_add, map_mul] at hrecS
      have hpc : gP pc = algebraMap k S c := by
        exact hgP_C c
      refine ⟨p - pc * q, q * qx, ?_⟩
      change algebraMap (R d) S (zSuccInGeneratedRing d (n + 1)) *
        gP (↑(q * qx)) = gP (p - pc * (q : nPresentationRing k))
      have hqprod : gP (↑(q * qx) : nPresentationRing k) =
          gP (q : nPresentationRing k) * gP (qx : nPresentationRing k) := by
        change gP ((q : nPresentationRing k) * (qx : nPresentationRing k)) = _
        rw [map_mul]
      have hqxS : gP (qx : nPresentationRing k) =
          algebraMap (R d) S (xInGeneratedRing d) := by
        rw [hqx]
        change gP (Polynomial.C (xInLaurentPolynomialRing k)) = _
        exact hgen_x
      have hq' : algebraMap (R d) S (zSuccInGeneratedRing d n) * gP q = gP p := by
        simpa only [zSuccInGeneratedRing] using hq
      have hmul :
          (algebraMap (R d) S (xInGeneratedRing d) *
              algebraMap (R d) S (zSuccInGeneratedRing d (n + 1)) +
            algebraMap k S c) * gP q = gP p := by
        rw [IsScalarTower.algebraMap_apply k (R d) S c, hrecS, hq']
      rw [hqprod, hqxS, map_sub, map_mul]
      calc
        algebraMap (R d) S (zSuccInGeneratedRing d (n + 1)) *
              (gP q * algebraMap (R d) S (xInGeneratedRing d)) =
            (algebraMap (R d) S (xInGeneratedRing d) *
                algebraMap (R d) S (zSuccInGeneratedRing d (n + 1)) +
              algebraMap k S c) * gP q -
              algebraMap k S c * gP q := by ring
        _ = gP p - algebraMap k S c * gP q := by
          exact congrArg (fun t : S => t - algebraMap k S c * gP q) hmul
        _ = gP p - gP pc * gP q := by
          exact congrArg (fun t : S => gP p - t * gP q) hpc.symm

private theorem localization_n_presentation_hrep_x (d : PowerSeriesData k)
    (S : Type*) [CommRing S] [Algebra (R d) S]
    (gP : nPresentationRing k →+* S)
    (hgen_x : gP (algebraMap (LaurentPolynomialRing k) (nPresentationRing k)
        (xInLaurentPolynomialRing k)) =
      algebraMap (R d) S (xInGeneratedRing d)) :
    algebraMap (R d) S (xInGeneratedRing d) * gP 1 =
      gP (Polynomial.C (xInLaurentPolynomialRing k)) := by
  rw [map_one, mul_one]
  change algebraMap (R d) S (xInGeneratedRing d) =
    gP (algebraMap (LaurentPolynomialRing k) (nPresentationRing k)
      (xInLaurentPolynomialRing k))
  exact hgen_x.symm

private theorem localization_n_presentation_hrep_z (d : PowerSeriesData k)
    (S : Type*) [CommRing S] [Algebra (R d) S]
    (gP : nPresentationRing k →+* S)
    (hgen_z : gP (Polynomial.X : nPresentationRing k) =
      algebraMap (R d) S (zInGeneratedRing d)) :
    algebraMap (R d) S (zInGeneratedRing d) * gP 1 = gP Polynomial.X := by
  rw [map_one, mul_one]
  exact hgen_z.symm

private theorem localization_n_presentation_hrep_const (d : PowerSeriesData k)
    (S : Type*) [CommRing S] [Algebra (R d) S] [Algebra k S]
    [IsScalarTower k (R d) S]
    (gP : nPresentationRing k →+* S) (c : k)
    (hgP_C : gP (Polynomial.C (algebraMap k (LaurentPolynomialRing k) c)) =
      algebraMap k S c) :
    algebraMap (R d) S (algebraMap k (R d) c) * gP 1 =
      gP (Polynomial.C (algebraMap k (LaurentPolynomialRing k) c)) := by
  calc
    algebraMap (R d) S (algebraMap k (R d) c) * gP 1 = algebraMap k S c := by
      rw [map_one, mul_one]
      exact (IsScalarTower.algebraMap_apply k (R d) S c).symm
    _ = gP (Polynomial.C (algebraMap k (LaurentPolynomialRing k) c)) := hgP_C.symm

private theorem localization_n_presentation_hrep_add (d : PowerSeriesData k)
    (S : Type*) [CommRing S] [Algebra (R d) S]
    (gP : nPresentationRing k →+* S) (y z : R d)
    (hy : ∃ p : nPresentationRing k,
      ∃ q : (nPresentationIdeal k).primeCompl,
        algebraMap (R d) S y * gP q = gP p)
    (hz : ∃ p : nPresentationRing k,
      ∃ q : (nPresentationIdeal k).primeCompl,
        algebraMap (R d) S z * gP q = gP p) :
    ∃ p : nPresentationRing k,
      ∃ q : (nPresentationIdeal k).primeCompl,
        algebraMap (R d) S (y + z) * gP q = gP p := by
  rcases hy with ⟨p, q, hq⟩
  rcases hz with ⟨p', q', hq'⟩
  refine ⟨p * q' + p' * q, q * q', ?_⟩
  change algebraMap (R d) S (y + z) * gP (↑(q * q')) =
    gP (p * (q' : nPresentationRing k) + p' * q)
  rw [map_add]
  have hqprod : gP (↑(q * q') : nPresentationRing k) =
      gP (q : nPresentationRing k) * gP (q' : nPresentationRing k) := by
    change gP ((q : nPresentationRing k) * (q' : nPresentationRing k)) = _
    rw [map_mul]
  rw [hqprod, map_add, map_mul, map_mul]
  calc
    ((algebraMap (R d) S y + algebraMap (R d) S z) *
        (gP q * gP q')) =
      (algebraMap (R d) S y * gP q) * gP q' +
        (algebraMap (R d) S z * gP q') * gP q := by ring
    _ = gP p * gP q' + gP p' * gP q := by rw [hq, hq']

private theorem localization_n_presentation_hrep_mul (d : PowerSeriesData k)
    (S : Type*) [CommRing S] [Algebra (R d) S]
    (gP : nPresentationRing k →+* S) (y z : R d)
    (hy : ∃ p : nPresentationRing k,
      ∃ q : (nPresentationIdeal k).primeCompl,
        algebraMap (R d) S y * gP q = gP p)
    (hz : ∃ p : nPresentationRing k,
      ∃ q : (nPresentationIdeal k).primeCompl,
        algebraMap (R d) S z * gP q = gP p) :
    ∃ p : nPresentationRing k,
      ∃ q : (nPresentationIdeal k).primeCompl,
        algebraMap (R d) S (y * z) * gP q = gP p := by
  rcases hy with ⟨p, q, hq⟩
  rcases hz with ⟨p', q', hq'⟩
  refine ⟨p * p', q * q', ?_⟩
  change algebraMap (R d) S (y * z) * gP (↑(q * q')) = gP (p * p')
  rw [map_mul]
  have hqprod : gP (↑(q * q') : nPresentationRing k) =
      gP (q : nPresentationRing k) * gP (q' : nPresentationRing k) := by
    change gP ((q : nPresentationRing k) * (q' : nPresentationRing k)) = _
    rw [map_mul]
  rw [hqprod]
  calc
    (algebraMap (R d) S y * algebraMap (R d) S z) *
        (gP (q : nPresentationRing k) * gP (q' : nPresentationRing k)) =
      (algebraMap (R d) S y * gP q) *
        (algebraMap (R d) S z * gP q') := by ring
    _ = gP p * gP p' := by rw [hq, hq']
    _ = gP (p * p') := by rw [map_mul]

private def localization_n_presentation_rep (d : PowerSeriesData k)
    (S : Type*) [CommRing S] [Algebra (R d) S]
    (gP : nPresentationRing k →+* S) (r : R d) : Prop :=
  ∃ p : nPresentationRing k,
    ∃ q : (nPresentationIdeal k).primeCompl,
      algebraMap (R d) S r * gP q = gP p

private theorem localization_n_presentation_adjoin_representation
    (d : PowerSeriesData k) (S : Type*) [CommRing S] [Algebra (R d) S]
    (gP : nPresentationRing k →+* S)
    (hX : localization_n_presentation_rep (d := d) (S := S) gP
      (xInGeneratedRing d))
    (hZ : localization_n_presentation_rep (d := d) (S := S) gP
      (zInGeneratedRing d))
    (hTail : ∀ n : ℕ,
      localization_n_presentation_rep (d := d) (S := S) gP
        (zSuccInGeneratedRing d n))
    (hC : ∀ c : k,
      localization_n_presentation_rep (d := d) (S := S) gP
        (algebraMap k (R d) c))
    (hAdd : ∀ y z : R d,
      localization_n_presentation_rep (d := d) (S := S) gP y →
      localization_n_presentation_rep (d := d) (S := S) gP z →
      localization_n_presentation_rep (d := d) (S := S) gP (y + z))
    (hMul : ∀ y z : R d,
      localization_n_presentation_rep (d := d) (S := S) gP y →
      localization_n_presentation_rep (d := d) (S := S) gP z →
      localization_n_presentation_rep (d := d) (S := S) gP (y * z)) :
      ∀ (y : PowerSeries k) (hy : y ∈ generatedRing d),
      localization_n_presentation_rep (d := d) (S := S) gP (⟨y, hy⟩ : R d) := by
  intro y hy
  refine Algebra.adjoin_induction
    (R := k)
    (A := PowerSeries k)
    (s := insert PowerSeries.X
      (insert (zPowerSeries (k := k) d.coefficients)
        (Set.range (fun j : ℕ => zTail (k := k) d.coefficients (j + 1)))))
    (p := fun y hy =>
      localization_n_presentation_rep (d := d) (S := S) gP (⟨y, hy⟩ : R d))
    ?_ ?_ ?_ ?_ hy
  · rintro y (rfl | hr)
    · exact hX
    · rcases Set.mem_insert_iff.mp hr with rfl | hr
      · exact hZ
      · rcases Set.mem_range.mp hr with ⟨n, rfl⟩
        exact hTail n
  · intro c
    exact hC c
  · intro y z hy' hz' hy hz
    exact hAdd (⟨y, hy'⟩ : R d) (⟨z, hz'⟩ : R d) hy hz
  · intro y z hy' hz' hy hz
    exact hMul (⟨y, hy'⟩ : R d) (⟨z, hz'⟩ : R d) hy hz

private theorem localization_n_presentation_rep_x (d : PowerSeriesData k)
    (S : Type*) [CommRing S] [Algebra (R d) S]
    (gP : nPresentationRing k →+* S)
    (hgen_x : gP (algebraMap (LaurentPolynomialRing k) (nPresentationRing k)
        (xInLaurentPolynomialRing k)) =
      algebraMap (R d) S (xInGeneratedRing d)) :
    localization_n_presentation_rep (d := d) (S := S) gP (xInGeneratedRing d) := by
  change ∃ p : nPresentationRing k,
    ∃ q : (nPresentationIdeal k).primeCompl,
      algebraMap (R d) S (xInGeneratedRing d) * gP q = gP p
  exact ⟨Polynomial.C (xInLaurentPolynomialRing k), 1,
    localization_n_presentation_hrep_x (d := d) (S := S) gP hgen_x⟩

private theorem localization_n_presentation_rep_z (d : PowerSeriesData k)
    (S : Type*) [CommRing S] [Algebra (R d) S]
    (gP : nPresentationRing k →+* S)
    (hgen_z : gP (Polynomial.X : nPresentationRing k) =
      algebraMap (R d) S (zInGeneratedRing d)) :
    localization_n_presentation_rep (d := d) (S := S) gP (zInGeneratedRing d) := by
  change ∃ p : nPresentationRing k,
    ∃ q : (nPresentationIdeal k).primeCompl,
      algebraMap (R d) S (zInGeneratedRing d) * gP q = gP p
  exact ⟨Polynomial.X, 1,
    localization_n_presentation_hrep_z (d := d) (S := S) gP hgen_z⟩

private theorem localization_n_presentation_rep_tail (d : PowerSeriesData k)
    (S : Type*) [CommRing S] [Algebra (R d) S]
    [Algebra k S] [IsScalarTower k (R d) S]
    [IsLocalization (nIdeal d).primeCompl S]
    (gP : nPresentationRing k →+* S)
    (hgen_x : gP (algebraMap (LaurentPolynomialRing k) (nPresentationRing k)
        (xInLaurentPolynomialRing k)) =
      algebraMap (R d) S (xInGeneratedRing d))
    (hgen_z : gP (Polynomial.X : nPresentationRing k) =
      algebraMap (R d) S (zInGeneratedRing d))
    (hgP_C : ∀ c : k,
      gP (Polynomial.C (algebraMap k (LaurentPolynomialRing k) c)) = algebraMap k S c)
    (qx : (nPresentationIdeal k).primeCompl)
    (hqx : (qx : nPresentationRing k) = Polynomial.C (xInLaurentPolynomialRing k))
    (n : ℕ) :
    localization_n_presentation_rep (d := d) (S := S) gP
      (zSuccInGeneratedRing d n) := by
  change ∃ p : nPresentationRing k,
    ∃ q : (nPresentationIdeal k).primeCompl,
      algebraMap (R d) S (zSuccInGeneratedRing d n) * gP q = gP p
  exact localization_n_presentation_hrep_tail
    (d := d) (S := S) gP hgen_x hgen_z hgP_C qx hqx n

private theorem localization_n_presentation_rep_const (d : PowerSeriesData k)
    (S : Type*) [CommRing S] [Algebra (R d) S] [Algebra k S]
    [IsScalarTower k (R d) S]
    (gP : nPresentationRing k →+* S) (hgP_C : ∀ c : k,
      gP (Polynomial.C (algebraMap k (LaurentPolynomialRing k) c)) = algebraMap k S c)
    (c : k) :
    localization_n_presentation_rep (d := d) (S := S) gP (algebraMap k (R d) c) := by
  change ∃ p : nPresentationRing k,
    ∃ q : (nPresentationIdeal k).primeCompl,
      algebraMap (R d) S (algebraMap k (R d) c) * gP q = gP p
  exact ⟨Polynomial.C (algebraMap k (LaurentPolynomialRing k) c), 1,
    localization_n_presentation_hrep_const (d := d) (S := S) gP c (hgP_C c)⟩

private theorem localization_n_presentation_rep_add (d : PowerSeriesData k)
    (S : Type*) [CommRing S] [Algebra (R d) S]
    (gP : nPresentationRing k →+* S) (y z : R d)
    (hy : localization_n_presentation_rep (d := d) (S := S) gP y)
    (hz : localization_n_presentation_rep (d := d) (S := S) gP z) :
    localization_n_presentation_rep (d := d) (S := S) gP (y + z) := by
  change ∃ p : nPresentationRing k,
    ∃ q : (nPresentationIdeal k).primeCompl,
      algebraMap (R d) S y * gP q = gP p at hy
  change ∃ p : nPresentationRing k,
    ∃ q : (nPresentationIdeal k).primeCompl,
      algebraMap (R d) S z * gP q = gP p at hz
  change ∃ p : nPresentationRing k,
    ∃ q : (nPresentationIdeal k).primeCompl,
      algebraMap (R d) S (y + z) * gP q = gP p
  exact localization_n_presentation_hrep_add (d := d) (S := S) gP y z hy hz

private theorem localization_n_presentation_rep_mul (d : PowerSeriesData k)
    (S : Type*) [CommRing S] [Algebra (R d) S]
    (gP : nPresentationRing k →+* S) (y z : R d)
    (hy : localization_n_presentation_rep (d := d) (S := S) gP y)
    (hz : localization_n_presentation_rep (d := d) (S := S) gP z) :
    localization_n_presentation_rep (d := d) (S := S) gP (y * z) := by
  change ∃ p : nPresentationRing k,
    ∃ q : (nPresentationIdeal k).primeCompl,
      algebraMap (R d) S y * gP q = gP p at hy
  change ∃ p : nPresentationRing k,
    ∃ q : (nPresentationIdeal k).primeCompl,
      algebraMap (R d) S z * gP q = gP p at hz
  change ∃ p : nPresentationRing k,
    ∃ q : (nPresentationIdeal k).primeCompl,
      algebraMap (R d) S (y * z) * gP q = gP p
  exact localization_n_presentation_hrep_mul (d := d) (S := S) gP y z hy hz

private theorem localization_n_presentation_hrep (d : PowerSeriesData k)
    (S : Type*) [CommRing S] [Algebra (R d) S]
    [Algebra k S] [IsScalarTower k (R d) S]
    [IsLocalization (nIdeal d).primeCompl S]
    (gP : nPresentationRing k →+* S)
    (hgen_x : gP (algebraMap (LaurentPolynomialRing k) (nPresentationRing k)
        (xInLaurentPolynomialRing k)) =
      algebraMap (R d) S (xInGeneratedRing d))
    (hgen_z : gP (Polynomial.X : nPresentationRing k) =
      algebraMap (R d) S (zInGeneratedRing d))
    (hgP_C : ∀ c : k,
      gP (Polynomial.C (algebraMap k (LaurentPolynomialRing k) c)) = algebraMap k S c)
    (qx : (nPresentationIdeal k).primeCompl)
    (hqx : (qx : nPresentationRing k) = Polynomial.C (xInLaurentPolynomialRing k)) :
    ∀ (y : PowerSeries k) (hy : y ∈ generatedRing d),
      ∃ p : nPresentationRing k,
        ∃ q : (nPresentationIdeal k).primeCompl,
        algebraMap (R d) S (⟨y, hy⟩ : R d) * gP q = gP p := by
  exact localization_n_presentation_adjoin_representation
    (d := d) (S := S) gP
    (localization_n_presentation_rep_x (d := d) (S := S) gP hgen_x)
    (localization_n_presentation_rep_z (d := d) (S := S) gP hgen_z)
    (localization_n_presentation_rep_tail
      (d := d) (S := S) gP hgen_x hgen_z hgP_C qx hqx)
    (localization_n_presentation_rep_const
      (d := d) (S := S) gP hgP_C)
    (localization_n_presentation_rep_add (d := d) (S := S) gP)
    (localization_n_presentation_rep_mul (d := d) (S := S) gP)

private theorem localization_n_presentation_lift_surjective
    (d : PowerSeriesData k) (S : Type*) [CommRing S] [Algebra (R d) S]
    [Algebra k S] [IsScalarTower k (R d) S]
    [IsLocalization (nIdeal d).primeCompl S] [IsLocalRing S]
    (gP : nPresentationRing k →+* S) (fP : nPresentationRing k →+* k)
    (hres : S ⧸ IsLocalRing.maximalIdeal S ≃+* k)
    (hrescomp : (hres.toRingHom.comp
      (Ideal.Quotient.mk (IsLocalRing.maximalIdeal S))).comp gP = fP)
    (hkerP : RingHom.ker fP = nPresentationIdeal k)
    (hunitP : ∀ y : (nPresentationIdeal k).primeCompl, IsUnit (gP y))
    (hrep : ∀ (y : PowerSeries k) (hy : y ∈ generatedRing d),
      ∃ p : nPresentationRing k,
        ∃ q : (nPresentationIdeal k).primeCompl,
          algebraMap (R d) S (⟨y, hy⟩ : R d) * gP q = gP p) :
    Function.Surjective
      (IsLocalization.lift (S := Localization.AtPrime (nPresentationIdeal k))
        (M := (nPresentationIdeal k).primeCompl)
        (g := gP) hunitP) := by
  rw [IsLocalization.lift_surjective_iff]
  intro y
  obtain ⟨rs, hrs⟩ :=
    IsLocalization.surj (R := R d) (S := S) (nIdeal d).primeCompl y
  let r : R d := rs.1
  let s : (nIdeal d).primeCompl := rs.2
  obtain ⟨p, q, hp⟩ := hrep r.1 r.2
  obtain ⟨u, t, hu⟩ := hrep s.1.1 s.1.2
  have hp' : algebraMap (R d) S (r : R d) * gP q = gP p := by
    simpa [r] using hp
  have hu' : algebraMap (R d) S (s : R d) * gP t = gP u := by
    simpa [s] using hu
  have huunit : IsUnit (gP u) := by
    rw [← hu']
    exact (IsLocalization.map_units S s).mul (hunitP t)
  have huP : u ∉ nPresentationIdeal k := by
    intro huP
    have hfu : fP u = 0 := by
      change u ∈ RingHom.ker fP
      rw [hkerP]
      exact huP
    have huM : gP u ∈ IsLocalRing.maximalIdeal S := by
      rw [← Ideal.Quotient.eq_zero_iff_mem]
      have hcomp := congrArg (fun h : nPresentationRing k →+* k => h u) hrescomp
      apply hres.injective
      change hres (Ideal.Quotient.mk (IsLocalRing.maximalIdeal S) (gP u)) = hres 0
      calc
        hres (Ideal.Quotient.mk (IsLocalRing.maximalIdeal S) (gP u)) =
            ((hres.toRingHom.comp (Ideal.Quotient.mk
              (IsLocalRing.maximalIdeal S))).comp gP) u := rfl
        _ = fP u := hcomp
        _ = 0 := hfu
        _ = hres 0 := by simp
    exact (IsLocalRing.notMem_maximalIdeal.mpr huunit) huM
  refine ⟨⟨p * t, ⟨u * q, ?_⟩⟩, ?_⟩
  · exact Submonoid.mul_mem _ huP q.prop
  · calc
      y * gP (u * q) = y * (gP u * gP q) := by rw [map_mul]
      _ = y * (algebraMap (R d) S (s : R d) * gP t) * gP q := by rw [hu']; ring
      _ = (y * algebraMap (R d) S (s : R d)) * gP t * gP q := by ring
      _ = algebraMap (R d) S (r : R d) * gP t * gP q := by rw [hrs]
      _ = (algebraMap (R d) S (r : R d) * gP q) * gP t := by ring
      _ = gP p * gP t := by rw [hp']
      _ = gP (p * t) := by rw [map_mul]

private theorem localization_n_presentation_gP_injective
    (d : PowerSeriesData k) (S : Type*) [CommRing S] [Algebra (R d) S]
    [Algebra k S] [IsLocalization (nIdeal d).primeCompl S]
    [IsScalarTower k (R d) S]
    (gP : nPresentationRing k →+* S)
    (hgen_x : gP (algebraMap (LaurentPolynomialRing k) (nPresentationRing k)
        (xInLaurentPolynomialRing k)) =
      algebraMap (R d) S (xInGeneratedRing d))
    (hgen_z : gP (Polynomial.X : nPresentationRing k) =
      algebraMap (R d) S (zInGeneratedRing d))
    (hgP_C : ∀ c : k,
      gP (Polynomial.C (algebraMap k (LaurentPolynomialRing k) c)) = algebraMap k S c)
    (hxunit : IsUnit (algebraMap (R d) S (xInGeneratedRing d))) :
    Function.Injective gP := by
  let hSFrac : S →+* FractionRing (R d) :=
    IsLocalization.lift (S := S) (M := (nIdeal d).primeCompl)
      (g := algebraMap (R d) (FractionRing (R d))) (by
        intro y
        have hy0 : (y : R d) ≠ 0 := by
          intro hy
          exact y.prop (hy ▸ (nIdeal d).zero_mem)
        exact IsLocalization.map_units (R := R d) (M := nonZeroDivisors (R d))
          (FractionRing (R d))
          ⟨y, mem_nonZeroDivisors_iff_ne_zero.mpr hy0⟩)
  have hSFraccomp : hSFrac.comp (algebraMap (R d) S) =
      algebraMap (R d) (FractionRing (R d)) := by
    apply IsLocalization.lift_comp
  have hSFrac_inj : Function.Injective hSFrac := by
    apply IsLocalization.injective_of_map_algebraMap_zero
      (R := R d) (M := (nIdeal d).primeCompl) S hSFrac
    intro x hx
    have hx' : algebraMap (R d) (FractionRing (R d)) x = 0 := by
      rw [← hSFraccomp]
      exact hx
    have hx0 : x = 0 := by
      apply (IsFractionRing.injective (R d) (FractionRing (R d)))
      simpa using hx'
    simpa [hx0]
  letI : Algebra (Polynomial k) (LaurentPolynomialRing k) := inferInstance
  letI : Algebra (Polynomial (Polynomial k)) (nPresentationRing k) :=
    Polynomial.algebra (Polynomial k) (LaurentPolynomialRing k)
  let gC : Polynomial (Polynomial k) →+* S :=
    Polynomial.eval₂RingHom
      (Polynomial.eval₂RingHom (algebraMap k S)
        (algebraMap (R d) S (xInGeneratedRing d)))
      (algebraMap (R d) S (zInGeneratedRing d))
  have hgCcomp : hSFrac.comp gC = xzPolynomialMap d := by
    apply Polynomial.ringHom_ext
    · intro p
      have hgc : gC (Polynomial.C p) =
          Polynomial.eval₂ (algebraMap k S)
            (algebraMap (R d) S (xInGeneratedRing d)) p := by
        simp only [gC, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C]
      have hxz : xzPolynomialMap d (Polynomial.C p) =
          Polynomial.eval₂ (algebraMap k (FractionRing (R d)))
            (algebraMap (R d) (FractionRing (R d))
              (xInGeneratedRing d)) p := by
        simp [xzPolynomialMap]
      change hSFrac (gC (Polynomial.C p)) =
        xzPolynomialMap d (Polynomial.C p)
      rw [hgc, hxz]
      rw [Polynomial.hom_eval₂]
      rw [show hSFrac.comp (algebraMap k S) = algebraMap k (FractionRing (R d)) by
        apply RingHom.ext
        intro c
        have hsc : algebraMap k S c =
            algebraMap (R d) S (algebraMap k (R d) c) := by
          rw [IsScalarTower.algebraMap_apply k (R d) S]
        change hSFrac (algebraMap k S c) = algebraMap k (FractionRing (R d)) c
        rw [hsc]
        exact (congrArg (fun h : R d →+* FractionRing (R d) =>
          h (algebraMap k (R d) c)) hSFraccomp).trans
          (IsScalarTower.algebraMap_apply k (R d) (FractionRing (R d)) c).symm]
      congr 1
      exact congrArg (fun h : R d →+* FractionRing (R d) =>
        h (xInGeneratedRing d)) hSFraccomp
    · simp only [RingHom.coe_comp, Function.comp_apply, gC,
        Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X, xzPolynomialMap]
      change hSFrac (algebraMap (R d) S (zInGeneratedRing d)) =
        algebraMap (R d) (FractionRing (R d)) (zInGeneratedRing d)
      exact congrArg (fun h : R d →+* FractionRing (R d) =>
        h (zInGeneratedRing d)) hSFraccomp
  have hgCinj : Function.Injective gC := by
    intro p q hpq
    apply xzPolynomialMap_injective d
    rw [← hgCcomp]
    exact congrArg hSFrac hpq
  let M0 : Submonoid (Polynomial (Polynomial k)) :=
    (Submonoid.powers (Polynomial.X : Polynomial k)).map
      (Polynomial.C : Polynomial k →+* Polynomial (Polynomial k)).toMonoidHom
  letI : IsLocalization M0 (nPresentationRing k) := by
    change IsLocalization
      ((Submonoid.powers (Polynomial.X : Polynomial k)).map
        (Polynomial.C : Polynomial k →+* Polynomial (Polynomial k)).toMonoidHom)
      (Polynomial (LaurentPolynomialRing k))
    exact Polynomial.isLocalization (Submonoid.powers (Polynomial.X : Polynomial k))
      (LaurentPolynomialRing k)
  have hunitC : ∀ y : M0, IsUnit (gC y) := by
    rintro ⟨y, ⟨s, hs, rfl⟩⟩
    obtain ⟨n, rfl⟩ := hs
    change IsUnit (Polynomial.eval₂
      (Polynomial.eval₂RingHom (algebraMap k S)
        (algebraMap (R d) S (xInGeneratedRing d)))
      (algebraMap (R d) S (zInGeneratedRing d))
      (Polynomial.C (Polynomial.X ^ n)))
    rw [Polynomial.eval₂_C]
    simpa only [Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X_pow] using hxunit.pow n
  let F0 : nPresentationRing k →+* S :=
    IsLocalization.lift (S := nPresentationRing k) (M := M0) (g := gC) hunitC
  have hF0comp : F0.comp (algebraMap (Polynomial (Polynomial k))
      (nPresentationRing k)) = gC :=
    IsLocalization.lift_comp hunitC
  have hFcomp : gP.comp (algebraMap (Polynomial (Polynomial k))
      (nPresentationRing k)) = gC := by
    apply Polynomial.ringHom_ext
    intro p
    have hcoeff :
        (gP.comp (algebraMap (LaurentPolynomialRing k) (nPresentationRing k))).comp
            (algebraMap (Polynomial k) (LaurentPolynomialRing k)) =
          Polynomial.eval₂RingHom (algebraMap k S)
            (algebraMap (R d) S (xInGeneratedRing d)) := by
      apply Polynomial.ringHom_ext
      · intro c
        change gP (Polynomial.C (algebraMap k (LaurentPolynomialRing k) c)) = _
        simpa only [Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C] using hgP_C c
      · change gP (Polynomial.C (xInLaurentPolynomialRing k)) = _
        simpa [Polynomial.algebraMap_apply] using hgen_x
    have hcoeffp := congrArg (fun h : Polynomial k →+* S => h p) hcoeff
    simpa [RingHom.coe_comp, Function.comp_apply, Polynomial.algebraMap_def,
      Polynomial.mapRingHom, gC] using hcoeffp
    · simpa [gC, Polynomial.algebraMap_def, Polynomial.mapRingHom] using hgen_z
  have hF0eq : F0 = gP := by
    apply IsLocalization.ringHom_ext M0
    rw [hF0comp, hFcomp]
  have hF0inj : Function.Injective F0 := by
    rw [IsLocalization.lift_injective_iff]
    intro p q
    constructor
    · intro hpq
      have hpq' := congrArg F0 hpq
      change (F0.comp (algebraMap (Polynomial (Polynomial k))
        (nPresentationRing k))) p =
        (F0.comp (algebraMap (Polynomial (Polynomial k))
          (nPresentationRing k))) q at hpq'
      rw [hF0comp] at hpq'
      exact hpq'
    · intro hpq
      exact congrArg (algebraMap (Polynomial (Polynomial k))
        (nPresentationRing k)) (hgCinj hpq)
  rw [← hF0eq]
  exact hF0inj

private theorem localization_n_presentation_gP_data
    (d : PowerSeriesData k) (S : Type*) [CommRing S] [Algebra (R d) S]
    [Algebra k S] [IsScalarTower k (R d) S]
    [IsLocalization (nIdeal d).primeCompl S] :
    ∃ gP : nPresentationRing k →+* S,
      IsUnit (algebraMap (R d) S (xInGeneratedRing d)) ∧
      gP (algebraMap (LaurentPolynomialRing k) (nPresentationRing k)
        (xInLaurentPolynomialRing k)) =
        algebraMap (R d) S (xInGeneratedRing d) ∧
      gP (Polynomial.X : nPresentationRing k) =
        algebraMap (R d) S (zInGeneratedRing d) ∧
      (∀ c : k,
        gP (Polynomial.C (algebraMap k (LaurentPolynomialRing k) c)) =
          algebraMap k S c) := by
  have hxnot : xInGeneratedRing d ∉ nIdeal d := by
    intro hx
    have hxm : xInGeneratedRing d - 1 ∈ nIdeal d := by
      rw [nIdeal_eq_span_xSubOne_z d]
      exact Ideal.subset_span (by simp)
    have hone : (1 : R d) ∈ nIdeal d := by
      have h := (nIdeal d).sub_mem hx hxm
      simpa [sub_sub] using h
    exact ((Ideal.ne_top_iff_one (nIdeal d)).mp (nIdeal_isMaximal d).ne_top) hone
  have hxunit : IsUnit (algebraMap (R d) S (xInGeneratedRing d)) := by
    exact IsLocalization.map_units S
      (⟨xInGeneratedRing d, hxnot⟩ : (nIdeal d).primeCompl)
  let e0 : Polynomial k →+* S :=
    Polynomial.eval₂RingHom (algebraMap k S)
      (algebraMap (R d) S (xInGeneratedRing d))
  have hxunit0 : IsUnit (e0 (Polynomial.X : Polynomial k)) := by
    simpa [e0] using hxunit
  let gQ : LaurentPolynomialRing k →+* S :=
    IsLocalization.Away.lift (g := e0) Polynomial.X hxunit0
  let gP : nPresentationRing k →+* S :=
    Polynomial.eval₂RingHom gQ (algebraMap (R d) S (zInGeneratedRing d))
  have hgQ : gQ (xInLaurentPolynomialRing k) =
      algebraMap (R d) S (xInGeneratedRing d) := by
    change gQ (algebraMap (Polynomial k) (LaurentPolynomialRing k) Polynomial.X) = _
    rw [IsLocalization.Away.lift_eq (g := e0) Polynomial.X hxunit0]
    simp [e0, xInLaurentPolynomialRing]
  have hgen_x : gP (algebraMap (LaurentPolynomialRing k) (nPresentationRing k)
      (xInLaurentPolynomialRing k)) =
      algebraMap (R d) S (xInGeneratedRing d) := by
    change gP (Polynomial.C (xInLaurentPolynomialRing k)) = _
    change Polynomial.eval₂ gQ (algebraMap (R d) S (zInGeneratedRing d))
        (Polynomial.C (xInLaurentPolynomialRing k)) = _
    rw [Polynomial.eval₂_C]
    exact hgQ
  have hgen_z : gP (Polynomial.X : nPresentationRing k) =
      algebraMap (R d) S (zInGeneratedRing d) := by
    change Polynomial.eval₂ gQ (algebraMap (R d) S (zInGeneratedRing d))
        (Polynomial.X : Polynomial (LaurentPolynomialRing k)) = _
    rw [Polynomial.eval₂_X]
  have hgP_C : ∀ c : k,
      gP (Polynomial.C (algebraMap k (LaurentPolynomialRing k) c)) = algebraMap k S c := by
    intro c
    change Polynomial.eval₂ gQ (algebraMap (R d) S (zInGeneratedRing d))
      (Polynomial.C (algebraMap k (LaurentPolynomialRing k) c)) = _
    rw [Polynomial.eval₂_C]
    change gQ (algebraMap k (LaurentPolynomialRing k) c) = _
    change (gQ.comp (algebraMap (Polynomial k) (LaurentPolynomialRing k)))
      (Polynomial.C c) = _
    rw [IsLocalization.Away.lift_comp]
    simp [e0]
  exact ⟨gP, hxunit, hgen_x, hgen_z, hgP_C⟩

private theorem localization_n_presentation_fP_data
    (d : PowerSeriesData k) :
    ∃ (fP : nPresentationRing k →+* k),
      Function.Surjective fP ∧
      RingHom.ker fP = nPresentationIdeal k ∧
      ∃ qx : (nPresentationIdeal k).primeCompl,
        (qx : nPresentationRing k) = Polynomial.C (xInLaurentPolynomialRing k) := by
  let e : Polynomial k →+* k := Polynomial.evalRingHom 1
  have heX : e (Polynomial.X : Polynomial k) = 1 := by simp [e]
  have heunits : ∀ y : Submonoid.powers (Polynomial.X : Polynomial k), IsUnit (e y) := by
    rintro ⟨y, hy⟩
    obtain ⟨n, rfl⟩ := hy
    simp [map_pow, heX]
  let g : LaurentPolynomialRing k →+* k :=
    IsLocalization.lift (M := Submonoid.powers (Polynomial.X : Polynomial k))
      (g := e) heunits
  let fP : nPresentationRing k →+* k := Polynomial.eval₂RingHom g 0
  have hfP : Function.Surjective fP := by
    intro c
    refine ⟨Polynomial.C (algebraMap k (LaurentPolynomialRing k) c), ?_⟩
    change Polynomial.eval₂ g 0
        (Polynomial.C (algebraMap k (LaurentPolynomialRing k) c)) = c
    rw [Polynomial.eval₂_C]
    change g (algebraMap k (LaurentPolynomialRing k) c) = c
    change (g.comp (algebraMap (Polynomial k) (LaurentPolynomialRing k)))
        (Polynomial.C c) = c
    rw [IsLocalization.lift_comp]
    simp [e]
  have hleP : nPresentationIdeal k ≤ RingHom.ker fP := by
    change Ideal.span {algebraMap (LaurentPolynomialRing k) (nPresentationRing k)
        (xInLaurentPolynomialRing k) - 1, Polynomial.X} ≤ RingHom.ker fP
    rw [Ideal.span_le]
    intro p hp
    change fP p = 0
    rcases Set.mem_insert_iff.mp hp with rfl | rfl
    · change fP (Polynomial.C (xInLaurentPolynomialRing k) - 1) = 0
      have hfg : fP (Polynomial.C (xInLaurentPolynomialRing k)) =
          g (xInLaurentPolynomialRing k) := by
        change Polynomial.eval₂ g 0
            (Polynomial.C (xInLaurentPolynomialRing k)) =
          g (xInLaurentPolynomialRing k)
        rw [Polynomial.eval₂_C]
      have hgx : g (xInLaurentPolynomialRing k) = 1 := by
        change (g.comp (algebraMap (Polynomial k) (LaurentPolynomialRing k)))
            (Polynomial.X : Polynomial k) = 1
        rw [IsLocalization.lift_comp, heX]
      calc
        fP (Polynomial.C (xInLaurentPolynomialRing k) - 1) =
            fP (Polynomial.C (xInLaurentPolynomialRing k)) - fP 1 := by
              rw [map_sub]
        _ = g (xInLaurentPolynomialRing k) - 1 := by rw [hfg, map_one]
        _ = 0 := by rw [hgx]; simp
    · change Polynomial.eval₂ g 0 (Polynomial.X : Polynomial (LaurentPolynomialRing k)) = 0
      rw [Polynomial.eval₂_X]
  have hkerP : RingHom.ker fP = nPresentationIdeal k := by
    have hmax : (RingHom.ker fP).IsMaximal := by
      apply Ideal.Quotient.maximal_of_isField
      exact (RingHom.quotientKerEquivOfSurjective (f := fP) hfP).toMulEquiv.isField
        (Field.toIsField k)
    exact (nPresentationIdeal_isMaximal k).eq_of_le hmax.ne_top hleP |>.symm
  have hxPnot : (Polynomial.C (xInLaurentPolynomialRing k) : nPresentationRing k) ∉
      nPresentationIdeal k := by
    intro hx
    have hxm : Polynomial.C (xInLaurentPolynomialRing k) - 1 ∈ nPresentationIdeal k :=
      Ideal.subset_span (by simp [nPresentationIdeal])
    have hone : (1 : nPresentationRing k) ∈ nPresentationIdeal k := by
      have h := (nPresentationIdeal k).sub_mem hx hxm
      simpa [sub_sub] using h
    exact ((Ideal.ne_top_iff_one (nPresentationIdeal k)).mp
      (nPresentationIdeal_isMaximal k).ne_top) hone
  let qx : (nPresentationIdeal k).primeCompl :=
    ⟨Polynomial.C (xInLaurentPolynomialRing k), by
      exact hxPnot⟩
  exact ⟨fP, hfP, hkerP, qx, rfl⟩

private theorem localization_n_presentation_predata (d : PowerSeriesData k) :
    ∃ (gP : nPresentationRing k →+* Localization.AtPrime (nIdeal d))
      (fP : nPresentationRing k →+* k)
      (hres : IsLocalRing.ResidueField (Localization.AtPrime (nIdeal d)) ≃+* k),
      IsUnit (algebraMap (R d) (Localization.AtPrime (nIdeal d))
        (xInGeneratedRing d)) ∧
      gP (algebraMap (LaurentPolynomialRing k) (nPresentationRing k)
        (xInLaurentPolynomialRing k)) =
        algebraMap (R d) (Localization.AtPrime (nIdeal d))
          (xInGeneratedRing d) ∧
      gP (Polynomial.X : nPresentationRing k) =
        algebraMap (R d) (Localization.AtPrime (nIdeal d))
          (zInGeneratedRing d) ∧
      (∀ c : k,
        gP (Polynomial.C (algebraMap k (LaurentPolynomialRing k) c)) =
          algebraMap k (Localization.AtPrime (nIdeal d)) c) ∧
      Function.Surjective fP ∧ RingHom.ker fP = nPresentationIdeal k ∧
      (∃ qx : (nPresentationIdeal k).primeCompl,
        (qx : nPresentationRing k) = Polynomial.C (xInLaurentPolynomialRing k)) ∧
      ((hres.toRingHom.comp
        (Ideal.Quotient.mk (IsLocalRing.maximalIdeal (Localization.AtPrime (nIdeal d)))))
        .comp gP = fP) ∧
      (∀ y : (nPresentationIdeal k).primeCompl,
        IsUnit (gP y)) := by
  let S := Localization.AtPrime (nIdeal d)
  have hxnot : xInGeneratedRing d ∉ nIdeal d := by
    intro hx
    have hxm : xInGeneratedRing d - 1 ∈ nIdeal d := by
      rw [nIdeal_eq_span_xSubOne_z d]
      exact Ideal.subset_span (by simp)
    have hone : (1 : R d) ∈ nIdeal d := by
      have h := (nIdeal d).sub_mem hx hxm
      simpa [sub_sub] using h
    exact ((Ideal.ne_top_iff_one (nIdeal d)).mp (nIdeal_isMaximal d).ne_top) hone
  have hxunit : IsUnit (algebraMap (R d) S (xInGeneratedRing d)) := by
    exact IsLocalization.map_units S
      (⟨xInGeneratedRing d, hxnot⟩ : (nIdeal d).primeCompl)
  let e0 : Polynomial k →+* S :=
    Polynomial.eval₂RingHom (algebraMap k S)
      (algebraMap (R d) S (xInGeneratedRing d))
  have hxunit0 : IsUnit (e0 (Polynomial.X : Polynomial k)) := by
    simpa [e0] using hxunit
  let gQ : LaurentPolynomialRing k →+* S :=
    IsLocalization.Away.lift (g := e0) Polynomial.X hxunit0
  let gP : nPresentationRing k →+* S :=
    Polynomial.eval₂RingHom gQ (algebraMap (R d) S (zInGeneratedRing d))
  have hgQ : gQ (xInLaurentPolynomialRing k) =
      algebraMap (R d) S (xInGeneratedRing d) := by
    change gQ (algebraMap (Polynomial k) (LaurentPolynomialRing k) Polynomial.X) = _
    rw [IsLocalization.Away.lift_eq (g := e0) Polynomial.X hxunit0]
    simp [e0, xInLaurentPolynomialRing]
  have hgen_x : gP (algebraMap (LaurentPolynomialRing k) (nPresentationRing k)
      (xInLaurentPolynomialRing k)) = algebraMap (R d) S (xInGeneratedRing d) := by
    change gP (Polynomial.C (xInLaurentPolynomialRing k)) = _
    change Polynomial.eval₂ gQ (algebraMap (R d) S (zInGeneratedRing d))
      (Polynomial.C (xInLaurentPolynomialRing k)) = _
    rw [Polynomial.eval₂_C]
    exact hgQ
  have hgen_z : gP (Polynomial.X : nPresentationRing k) =
      algebraMap (R d) S (zInGeneratedRing d) := by
    change Polynomial.eval₂ gQ (algebraMap (R d) S (zInGeneratedRing d))
      (Polynomial.X : Polynomial (LaurentPolynomialRing k)) = _
    rw [Polynomial.eval₂_X]
  have hgP_C : ∀ c : k,
      gP (Polynomial.C (algebraMap k (LaurentPolynomialRing k) c)) = algebraMap k S c := by
    intro c
    change Polynomial.eval₂ gQ (algebraMap (R d) S (zInGeneratedRing d))
      (Polynomial.C (algebraMap k (LaurentPolynomialRing k) c)) = _
    rw [Polynomial.eval₂_C]
    change gQ (algebraMap k (LaurentPolynomialRing k) c) = _
    change (gQ.comp (algebraMap (Polynomial k) (LaurentPolynomialRing k)))
      (Polynomial.C c) = _
    rw [IsLocalization.Away.lift_comp]
    simp [e0]
  let e : Polynomial k →+* k := Polynomial.evalRingHom 1
  have heX : e (Polynomial.X : Polynomial k) = 1 := by simp [e]
  have heunits : ∀ y : Submonoid.powers (Polynomial.X : Polynomial k), IsUnit (e y) := by
    rintro ⟨y, hy⟩
    obtain ⟨n, rfl⟩ := hy
    simp [map_pow, heX]
  let g : LaurentPolynomialRing k →+* k :=
    IsLocalization.lift (M := Submonoid.powers (Polynomial.X : Polynomial k))
      (g := e) heunits
  let fP : nPresentationRing k →+* k := Polynomial.eval₂RingHom g 0
  have hfP : Function.Surjective fP := by
    intro c
    refine ⟨Polynomial.C (algebraMap k (LaurentPolynomialRing k) c), ?_⟩
    change Polynomial.eval₂ g 0 (Polynomial.C (algebraMap k (LaurentPolynomialRing k) c)) = c
    rw [Polynomial.eval₂_C]
    change g (algebraMap k (LaurentPolynomialRing k) c) = c
    change (g.comp (algebraMap (Polynomial k) (LaurentPolynomialRing k)))
      (Polynomial.C c) = c
    rw [IsLocalization.lift_comp]
    simp [e]
  have hleP : nPresentationIdeal k ≤ RingHom.ker fP := by
    change Ideal.span {algebraMap (LaurentPolynomialRing k) (nPresentationRing k)
      (xInLaurentPolynomialRing k) - 1, Polynomial.X} ≤ RingHom.ker fP
    rw [Ideal.span_le]
    intro p hp
    change fP p = 0
    rcases Set.mem_insert_iff.mp hp with rfl | rfl
    · change fP (Polynomial.C (xInLaurentPolynomialRing k) - 1) = 0
      have hfg : fP (Polynomial.C (xInLaurentPolynomialRing k)) =
          g (xInLaurentPolynomialRing k) := by
        change Polynomial.eval₂ g 0 (Polynomial.C (xInLaurentPolynomialRing k)) =
          g (xInLaurentPolynomialRing k)
        rw [Polynomial.eval₂_C]
      have hgx : g (xInLaurentPolynomialRing k) = 1 := by
        change (g.comp (algebraMap (Polynomial k) (LaurentPolynomialRing k)))
          (Polynomial.X : Polynomial k) = 1
        rw [IsLocalization.lift_comp, heX]
      calc
        fP (Polynomial.C (xInLaurentPolynomialRing k) - 1) =
            fP (Polynomial.C (xInLaurentPolynomialRing k)) - fP 1 := by rw [map_sub]
        _ = g (xInLaurentPolynomialRing k) - 1 := by rw [hfg, map_one]
        _ = 0 := by rw [hgx]; simp
    · change Polynomial.eval₂ g 0 (Polynomial.X : Polynomial (LaurentPolynomialRing k)) = 0
      rw [Polynomial.eval₂_X]
  have hkerP : RingHom.ker fP = nPresentationIdeal k := by
    have hmax : (RingHom.ker fP).IsMaximal := by
      apply Ideal.Quotient.maximal_of_isField
      exact (RingHom.quotientKerEquivOfSurjective (f := fP) hfP).toMulEquiv.isField
        (Field.toIsField k)
    exact (nPresentationIdeal_isMaximal k).eq_of_le hmax.ne_top hleP |>.symm
  have hxPnot : (Polynomial.C (xInLaurentPolynomialRing k) : nPresentationRing k) ∉
      nPresentationIdeal k := by
    intro hx
    have hxm : Polynomial.C (xInLaurentPolynomialRing k) - 1 ∈ nPresentationIdeal k :=
      Ideal.subset_span (by simp [nPresentationIdeal])
    have hone : (1 : nPresentationRing k) ∈ nPresentationIdeal k := by
      have h := (nPresentationIdeal k).sub_mem hx hxm
      simpa [sub_sub] using h
    exact ((Ideal.ne_top_iff_one (nPresentationIdeal k)).mp
      (nPresentationIdeal_isMaximal k).ne_top) hone
  let qx : (nPresentationIdeal k).primeCompl :=
    ⟨Polynomial.C (xInLaurentPolynomialRing k), hxPnot⟩
  rcases quotient_nIdeal_equiv d with ⟨eN⟩
  let hres :=
    (@IsLocalization.AtPrime.equivQuotMaximalIdeal (R d) _ (nIdeal d)
      (nIdeal_isMaximal d) S _ _ _ _).symm.trans eN
  have hrescomp : (hres.toRingHom.comp
      (Ideal.Quotient.mk (IsLocalRing.maximalIdeal S))).comp gP = fP := by
    apply Polynomial.ringHom_ext
    · intro c
      simp [gP, fP, hres]
    · simp [gP, fP, hres]
  have hunitP : ∀ y : (nPresentationIdeal k).primeCompl, IsUnit (gP y) := by
    intro y
    rw [← IsLocalRing.notMem_maximalIdeal]
    intro hy
    have hy0 : Ideal.Quotient.mk (IsLocalRing.maximalIdeal S) (gP y) = 0 := by
      rw [Ideal.Quotient.eq_zero_iff_mem]
      exact hy
    have hy' : hres (Ideal.Quotient.mk (IsLocalRing.maximalIdeal S) (gP y)) = 0 := by
      simpa using congrArg hres hy0
    have hfy : fP y = 0 := by
      have hcomp := congrArg (fun h : nPresentationRing k →+* k => h y) hrescomp
      rw [← hcomp]
      exact hy'
    have hyker : y.val ∈ RingHom.ker fP := hfy
    have hyI : y.val ∈ nPresentationIdeal k := by simpa only [hkerP] using hyker
    exact y.prop hyI
  exact ⟨gP, fP, hres, hxunit, hgen_x, hgen_z, hgP_C, hfP, hkerP,
    ⟨qx, rfl⟩, hrescomp, hunitP⟩

private theorem localization_n_presentation_surjective_of_data
    (d : PowerSeriesData k) (S : Type*) [CommRing S] [Algebra (R d) S]
    [Algebra k S] [IsScalarTower k (R d) S]
    [IsLocalization (nIdeal d).primeCompl S] [IsLocalRing S]
    (gP : nPresentationRing k →+* S) (fP : nPresentationRing k →+* k)
    (hres : S ⧸ IsLocalRing.maximalIdeal S ≃+* k)
    (hrescomp : (hres.toRingHom.comp
      (Ideal.Quotient.mk (IsLocalRing.maximalIdeal S))).comp gP = fP)
    (hkerP : RingHom.ker fP = nPresentationIdeal k)
    (hunitP : ∀ y : (nPresentationIdeal k).primeCompl, IsUnit (gP y))
    (qx : (nPresentationIdeal k).primeCompl)
    (hqx : (qx : nPresentationRing k) = Polynomial.C (xInLaurentPolynomialRing k))
    (hgen_x : gP (algebraMap (LaurentPolynomialRing k) (nPresentationRing k)
        (xInLaurentPolynomialRing k)) =
      algebraMap (R d) S (xInGeneratedRing d))
    (hgen_z : gP (Polynomial.X : nPresentationRing k) =
      algebraMap (R d) S (zInGeneratedRing d))
    (hgP_C : ∀ c : k,
      gP (Polynomial.C (algebraMap k (LaurentPolynomialRing k) c)) = algebraMap k S c) :
    Function.Surjective
      (IsLocalization.lift (S := Localization.AtPrime (nPresentationIdeal k))
        (M := (nPresentationIdeal k).primeCompl) (g := gP) hunitP) := by
  have hrep := localization_n_presentation_hrep (d := d) (S := S) gP
    hgen_x hgen_z hgP_C qx hqx
  exact localization_n_presentation_lift_surjective
    (d := d) (S := S) gP fP hres hrescomp hkerP hunitP hrep

private theorem localization_n_presentation_equiv_of_data
    (d : PowerSeriesData k) (S : Type*) [CommRing S] [Algebra (R d) S]
    [Algebra k S] [IsScalarTower k (R d) S]
    [IsLocalization (nIdeal d).primeCompl S] [IsLocalRing S]
    (gP : nPresentationRing k →+* S) (fP : nPresentationRing k →+* k)
    (hres : S ⧸ IsLocalRing.maximalIdeal S ≃+* k)
    (hrescomp : (hres.toRingHom.comp
      (Ideal.Quotient.mk (IsLocalRing.maximalIdeal S))).comp gP = fP)
    (hkerP : RingHom.ker fP = nPresentationIdeal k)
    (hunitP : ∀ y : (nPresentationIdeal k).primeCompl, IsUnit (gP y))
    (hFsurj : Function.Surjective
      (IsLocalization.lift (S := Localization.AtPrime (nPresentationIdeal k))
        (M := (nPresentationIdeal k).primeCompl) (g := gP) hunitP))
    (hgPinj : Function.Injective gP) :
    Nonempty (Localization.AtPrime (nPresentationIdeal k) ≃+* S) := by
  let F : Localization.AtPrime (nPresentationIdeal k) →+* S :=
    IsLocalization.lift (M := (nPresentationIdeal k).primeCompl)
      (g := gP) hunitP
  exact ⟨RingEquiv.ofBijective F ⟨by
    rw [IsLocalization.lift_injective_iff]
    intro p q
    constructor
    · intro hpq
      have hpq' := congrArg F hpq
      change (F.comp (algebraMap (nPresentationRing k)
        (Localization.AtPrime (nPresentationIdeal k)))) p =
        (F.comp (algebraMap (nPresentationRing k)
          (Localization.AtPrime (nPresentationIdeal k)))) q at hpq'
      rw [IsLocalization.lift_comp hunitP] at hpq'
      exact hpq'
    · intro hpq
      exact congrArg (algebraMap (nPresentationRing k)
        (Localization.AtPrime (nPresentationIdeal k)))
        (hgPinj hpq), hFsurj⟩⟩

private theorem localization_n_presentation_compatibility
    (d : PowerSeriesData k) (S : Type*) [CommRing S] [Algebra (R d) S]
    [Algebra k S] [IsScalarTower k (R d) S]
    [IsLocalization (nIdeal d).primeCompl S] [IsLocalRing S]
    (gP : nPresentationRing k →+* S) (fP : nPresentationRing k →+* k)
    (hres : S ⧸ IsLocalRing.maximalIdeal S ≃+* k)
    (hkerP : RingHom.ker fP = nPresentationIdeal k)
    (hrescomp : (hres.toRingHom.comp
      (Ideal.Quotient.mk (IsLocalRing.maximalIdeal S))).comp gP = fP) :
    ∀ y : (nPresentationIdeal k).primeCompl, IsUnit (gP y) := by
    intro y
    rw [← IsLocalRing.notMem_maximalIdeal]
    intro hy
    have hy0 : Ideal.Quotient.mk (IsLocalRing.maximalIdeal S) (gP y) = 0 := by
      rw [Ideal.Quotient.eq_zero_iff_mem]
      exact hy
    have hy' : hres (Ideal.Quotient.mk (IsLocalRing.maximalIdeal S) (gP y)) = 0 := by
      simpa using congrArg hres hy0
    have hfy : fP y = 0 := by
      have hcomp := congrArg (fun h : nPresentationRing k →+* k => h y) hrescomp
      rw [← hcomp]
      exact hy'
    have hyker : y.val ∈ RingHom.ker fP := by
      exact hfy
    have hyI : y.val ∈ nPresentationIdeal k := by
      simpa only [hkerP] using hyker
    exact y.prop hyI

private theorem localization_n_presentation_core (d : PowerSeriesData k) :
    Nonempty (Localization.AtPrime (nPresentationIdeal k) ≃+*
      Localization.AtPrime (nIdeal d)) := by
  let S := Localization.AtPrime (nIdeal d)
  rcases localization_n_presentation_predata d with
    ⟨gP, fP, hres, hxunit, hgen_x, hgen_z, hgP_C, _, hkerP,
      ⟨qx, hqx⟩, hrescomp, hunitP⟩
  have hFsurj := localization_n_presentation_surjective_of_data (d := d) (S := S)
    gP fP hres hrescomp hkerP hunitP qx hqx hgen_x hgen_z hgP_C
  have hgPinj := localization_n_presentation_gP_injective (d := d) (S := S) gP
    hgen_x hgen_z hgP_C hxunit
  exact localization_n_presentation_equiv_of_data (d := d) (S := S) gP fP hres
    hrescomp hkerP hunitP hFsurj hgPinj

/-- The source's presentation of `R_𝔫` by the localization of
`k[x, x⁻¹, z]` at `(x - 1, z)`. -/
theorem localization_n_presentation (d : PowerSeriesData k) :
    Nonempty (Localization.AtPrime (nPresentationIdeal k) ≃+*
      Localization.AtPrime (nIdeal d)) := localization_n_presentation_core d

/-- `R_𝔫` is a regular local ring of dimension `2` and residue field `k`. -/
theorem localization_n_is_regular_local_dim_two (d : PowerSeriesData k) :
    IsNoetherianRing (Localization.AtPrime (nIdeal d)) ∧
      IsRegularLocalRing (Localization.AtPrime (nIdeal d)) ∧
      ringKrullDim (Localization.AtPrime (nIdeal d)) = 2 ∧
      Nonempty (IsLocalRing.ResidueField (Localization.AtPrime (nIdeal d)) ≃+* k) := by
  rcases localization_n_presentation d with ⟨e⟩
  haveI : IsRegularRing (LaurentPolynomialRing k) := by
    rw [isRegularRing_iff]
    intro p hp
    let q : Ideal (Polynomial k) :=
      p.comap (algebraMap (Polynomial k) (LaurentPolynomialRing k))
    haveI : q.IsPrime := by
      dsimp [q]
      infer_instance
    have hd : Disjoint (Submonoid.powers (Polynomial.X : Polynomial k) : Set (Polynomial k))
        (q : Set (Polynomial k)) := by
      refine Set.disjoint_left.mpr ?_
      intro a ha hq
      obtain ⟨n, rfl⟩ := ha
      have hunit : IsUnit (algebraMap (Polynomial k) (LaurentPolynomialRing k)
          ((Polynomial.X : Polynomial k) ^ n)) := by
        exact IsLocalization.map_units (M := Submonoid.powers (Polynomial.X : Polynomial k))
          (LaurentPolynomialRing k) ⟨(Polynomial.X : Polynomial k) ^ n, ⟨n, rfl⟩⟩
      exact hp.ne_top (p.eq_top_of_isUnit_mem hq hunit)
    letI : IsRegularRing (Polynomial k) := by infer_instance
    exact IsRegularLocalRing.of_ringEquiv
      (IsLocalization.localizationLocalizationAtPrimeIsoLocalization
        (M := Submonoid.powers (Polynomial.X : Polynomial k)) p).toRingEquiv
  haveI : IsRegularRing (nPresentationRing k) := by infer_instance
  haveI : IsRegularLocalRing (Localization.AtPrime (nPresentationIdeal k)) := by
    infer_instance
  have hregS : IsRegularLocalRing (Localization.AtPrime (nIdeal d)) :=
    IsRegularLocalRing.of_ringEquiv
      (R := Localization.AtPrime (nPresentationIdeal k)) e
  have hdimP : ringKrullDim (Localization.AtPrime (nPresentationIdeal k)) = 2 := by
    rw [IsLocalization.AtPrime.ringKrullDim_eq_height
      (nPresentationIdeal k) (Localization.AtPrime (nPresentationIdeal k))]
    let q : Ideal (LaurentPolynomialRing k) :=
      (nPresentationIdeal k).comap
        (algebraMap (LaurentPolynomialRing k) (nPresentationRing k))
    letI : (nPresentationIdeal k).LiesOver q := ⟨rfl⟩
    have hqprime : q.IsPrime :=
      Ideal.isPrime_of_liesOver (nPresentationIdeal k) q
    have hxne : xInLaurentPolynomialRing k - 1 ≠ 0 := by
      intro h
      have h' : (Polynomial.X : Polynomial k) - 1 = 0 := by
        apply IsLocalization.injective (LaurentPolynomialRing k)
          (powers_le_nonZeroDivisors_of_noZeroDivisors (x := (Polynomial.X : Polynomial k))
            (by simp))
        simpa [xInLaurentPolynomialRing] using h
      exact (Polynomial.X_sub_C_ne_zero (1 : k)) (by simpa using h')
    have hqnebot : q ≠ ⊥ := by
      intro hq
      have hxm : xInLaurentPolynomialRing k - 1 ∈ q := by
        change algebraMap (LaurentPolynomialRing k) (nPresentationRing k)
            (xInLaurentPolynomialRing k - 1) ∈ nPresentationIdeal k
        rw [map_sub]
        exact Ideal.subset_span (by simp [nPresentationIdeal])
      rw [hq] at hxm
      exact hxne (by simpa using hxm)
    have hLaurentDomain : IsDomain (LaurentPolynomialRing k) :=
      IsLocalization.isDomain_localization
        (powers_le_nonZeroDivisors_of_noZeroDivisors (x := (Polynomial.X : Polynomial k))
          (by simp))
    have hLaurentPIR : IsPrincipalIdealRing (LaurentPolynomialRing k) := by
      constructor
      intro I
      rw [← IsLocalization.map_under
        (M := Submonoid.powers (Polynomial.X : Polynomial k))
        (S := LaurentPolynomialRing k) I]
      obtain ⟨x, hx⟩ := IsPrincipalIdealRing.principal (I.under (Polynomial k))
      refine ⟨⟨algebraMap (Polynomial k) (LaurentPolynomialRing k) x, ?_⟩⟩
      rw [hx, Ideal.map_span, Set.image_singleton]
    letI : IsDomain (LaurentPolynomialRing k) := hLaurentDomain
    letI : IsPrincipalIdealRing (LaurentPolynomialRing k) := hLaurentPIR
    have hqmax : q.IsMaximal :=
      Ideal.IsPrime.isMaximal hqprime hqnebot
    have hqheight : q.height = 1 := by
      apply IsPrincipalIdealRing.height_eq_one_of_isMaximal q
      exact Ring.not_isField_of_ne_of_ne hqnebot hqmax.ne_top
    have hPmax : (nPresentationIdeal k).IsMaximal := nPresentationIdeal_isMaximal k
    rw [@Polynomial.height_eq_height_add_one (LaurentPolynomialRing k) _ inferInstance q
      (nPresentationIdeal k) hPmax inferInstance, hqheight]
    norm_num
  have hnoethS : IsNoetherianRing (Localization.AtPrime (nIdeal d)) := by
    exact hregS.toIsNoetherian
  refine ⟨hnoethS, hregS, ?_, ?_⟩
  · rw [← hdimP, ringKrullDim_eq_of_ringEquiv e]
  · rcases quotient_nIdeal_equiv d with ⟨eN⟩
    exact ⟨(@IsLocalization.AtPrime.equivQuotMaximalIdeal (R d) _ (nIdeal d)
      (nIdeal_isMaximal d) (Localization.AtPrime (nIdeal d)) _ _ _ _).symm.trans eN⟩

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
  rw [multiplicativeSet_eq_complement_union d]
  constructor
  · simp only [Set.mem_sdiff, Set.mem_univ, true_and, Set.mem_union]
    intro h
    rcases h with h | h
    · exact (Ideal.ne_top_iff_one (mIdeal d)).mp (mIdeal_isMaximal d).ne_top h
    · exact (Ideal.ne_top_iff_one (nIdeal d)).mp (nIdeal_isMaximal d).ne_top h
  · intro r s hr hs
    simp only [Set.mem_sdiff, Set.mem_univ, true_and, Set.mem_union] at hr hs ⊢
    intro h
    rcases h with h | h
    · rcases (mIdeal_isPrime d).mem_or_mem h with h' | h'
      · exact hr (Or.inl h')
      · exact hs (Or.inl h')
    · rcases (nIdeal_isPrime d).mem_or_mem h with h' | h'
      · exact hr (Or.inr h')
      · exact hs (Or.inr h')

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
