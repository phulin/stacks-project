import Formalization.Books.Algebra.Unit88.MittagLefflerModules
import Mathlib.Algebra.DirectSum.Module
import Mathlib.Data.PNat.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.TensorProduct.Pi
import Mathlib.RingTheory.Flat.Localization
import Mathlib.RingTheory.Localization.FractionRing

/-!
# Commutative Algebra, Chapter 89: Interchanging direct products with tensor

The canonical product--tensor map is Mathlib's `TensorProduct.piRightHom`.
The Mittag--Leffler predicate and universal exactness are the canonical
interfaces from Chapters 88 and 82, respectively.
-/

namespace Formalization.Books.Algebra.Unit89

open CategoryTheory
open CategoryTheory.Limits
open Formalization.Books.Algebra.Unit82
open Formalization.Books.Algebra.Unit88
open Formalization.Books.Categories.Unit21
open scoped DirectSum TensorProduct

universe u v w z x

noncomputable section

/-! ## The canonical map and the examples -/

/- The source's notation `M^A` is the ordinary product of copies of `M`. -/
abbrev modulePower (M : Type u) (A : Type v) := A → M

/-- The canonical map from tensoring a product to the product of tensors. -/
def productTensorMap
    {R : Type u} [CommRing R] {A : Type v}
    (M : ModuleCat.{w} R) (Q : A → ModuleCat.{z} R) :
    TensorProduct R (M : Type w) (∀ a, (Q a : Type z)) →ₗ[R]
      ∀ a, TensorProduct R (M : Type w) (Q a : Type z) :=
  TensorProduct.piRightHom R R (M : Type w) (fun a => (Q a : Type z))

@[simp]
theorem productTensorMap_tmul
    {R : Type u} [CommRing R] {A : Type v}
    (M : ModuleCat.{w} R) (Q : A → ModuleCat.{z} R)
    (m : (M : Type w)) (q : ∀ a, (Q a : Type z)) :
    productTensorMap M Q (m ⊗ₜ[R] q) = fun a => m ⊗ₜ[R] q a := by
  rfl

/-- The canonical map `M ⊗ R^A → M^A`, using `M ⊗ R ≅ M` in each factor. -/
def tensorModulePowerMap
    {R : Type u} [CommRing R] {A : Type v}
    (M : ModuleCat.{w} R) :
    TensorProduct R (M : Type w) (modulePower R A) →ₗ[R]
      modulePower (M : Type w) A :=
  (LinearEquiv.piCongrRight (fun _ => TensorProduct.rid R (M : Type w))).toLinearMap.comp
    (productTensorMap M (fun _ : A => ModuleCat.of R R))

@[simp]
theorem tensorModulePowerMap_tmul
    {R : Type u} [CommRing R] {A : Type v}
    (M : ModuleCat.{w} R) (m : (M : Type w)) (q : modulePower R A) :
    tensorModulePowerMap M (m ⊗ₜ[R] q) = fun a => q a • m := by
  ext a
  simp [tensorModulePowerMap, productTensorMap]

/- The first example uses the positive natural numbers as the indexing set,
   so `ZMod n` agrees with the source's `Z/n` for every index. -/

def rationalModule : ModuleCat ℤ := ModuleCat.of ℤ ℚ

def integerQuotientFamily : ℕ+ → ModuleCat ℤ :=
  fun n => ModuleCat.of ℤ (ZMod (n : ℕ))

def integerDiagonalToQuotientProduct :
    ℤ →ₗ[ℤ] ∀ n : ℕ+, ZMod (n : ℕ) :=
  LinearMap.pi (fun n => (Int.castAddHom (ZMod (n : ℕ))).toIntLinearMap)

theorem integerDiagonalToQuotientProduct_injective :
    Function.Injective integerDiagonalToQuotientProduct := by
  intro a b h
  have hcoord : ∀ n : ℕ+, (a : ZMod (n : ℕ)) = (b : ZMod (n : ℕ)) := by
    intro n
    simpa [integerDiagonalToQuotientProduct] using congrFun h n
  have hdiv : ∀ n : ℕ+, ((n : ℕ) : ℤ) ∣ b - a := by
    intro n
    exact (ZMod.intCast_eq_intCast_iff_dvd_sub a b (n : ℕ)).mp (hcoord n)
  let n : ℕ+ := ⟨Int.natAbs (b - a) + 1, Nat.succ_pos _⟩
  obtain ⟨k, hk⟩ := hdiv n
  have hnat := congrArg Int.natAbs hk
  by_contra hab
  have hne : Int.natAbs (b - a) ≠ 0 := by
    exact Int.natAbs_ne_zero.mpr (sub_ne_zero.mpr (Ne.symm hab))
  have hkpos : 0 < Int.natAbs k := by
    by_contra hkpos
    have : k = 0 := Int.natAbs_eq_zero.mp (Nat.eq_zero_of_not_pos hkpos)
    subst k
    simp at hnat
    exact hne (Int.natAbs_eq_zero.mpr hnat)
  simp [n, Int.natAbs_mul] at hnat
  have hnabs : Int.natAbs (|b - a| + 1) = Int.natAbs (b - a) + 1 := by
    have hcast :
        (Int.natAbs (|b - a| + 1) : ℤ) = Int.natAbs (b - a) + 1 := by
      rw [Int.natAbs_of_nonneg]
      simp
      positivity
    exact_mod_cast hcast
  rw [hnabs] at hnat
  have hle : Int.natAbs (b - a) + 1 ≤ Int.natAbs (b - a) := by
    have hle' : Int.natAbs (b - a) + 1 ≤
        (Int.natAbs (b - a) + 1) * Int.natAbs k :=
      Nat.le_mul_of_pos_right _ hkpos
    omega
  omega

def rationalTensorIntegerDiagonal :
    ℚ →ₗ[ℤ] TensorProduct ℤ ℚ (∀ n : ℕ+, ZMod (n : ℕ)) :=
  (integerDiagonalToQuotientProduct.lTensor ℚ).comp
    (TensorProduct.rid ℤ ℚ).symm.toLinearMap

theorem rationalTensorIntegerDiagonal_injective :
    Function.Injective rationalTensorIntegerDiagonal := by
  let : Module.Flat ℤ ℚ := IsLocalization.flat ℚ (Submonoid.pos ℤ)
  exact (Module.Flat.lTensor_preserves_injective_linearMap
    integerDiagonalToQuotientProduct integerDiagonalToQuotientProduct_injective).comp
    (TensorProduct.rid ℤ ℚ).symm.injective

def rationalQuotientTensorMap :
    TensorProduct ℤ ℚ (∀ n : ℕ+, ZMod (n : ℕ)) →ₗ[ℤ]
      ∀ n : ℕ+, TensorProduct ℤ ℚ (ZMod (n : ℕ)) :=
  productTensorMap rationalModule integerQuotientFamily

theorem rationalQuotientTensorProduct_nontrivial :
    Nontrivial (TensorProduct ℤ ℚ (∀ n : ℕ+, ZMod (n : ℕ))) := by
  exact rationalTensorIntegerDiagonal_injective.nontrivial

theorem rationalQuotientTensorProduct_subsingleton :
    Subsingleton (∀ n : ℕ+, TensorProduct ℤ ℚ (ZMod (n : ℕ))) := by
  have hcomponent : ∀ (n : ℕ+) (x : TensorProduct ℤ ℚ (ZMod (n : ℕ))), x = 0 := by
    intro n x
    induction x using TensorProduct.induction_on with
    | zero => rfl
    | tmul q z =>
        have hzero : (n : ℚ) • (q ⊗ₜ[ℤ] z) = 0 := by
          rw [Nat.cast_smul_eq_nsmul]
          change ((n : ℤ) : ℚ) • (q ⊗ₜ[ℤ] z) = 0
          rw [Int.cast_smul_eq_zsmul]
          rw [TensorProduct.smul_tmul']
          rw [TensorProduct.smul_tmul]
          rw [show (n : ℤ) • z = (n : ℕ) • z by simp]
          rw [ZModModule.char_nsmul_eq_zero]
          simp
        apply (smul_eq_zero.mp hzero).resolve_left
        norm_num
    | add x y hx hy => rw [hx, hy, add_zero]
  constructor
  intro x y
  funext n
  exact (hcomponent n (x n)).trans (hcomponent n (y n)).symm

theorem rationalQuotientTensorMap_not_injective :
    ¬Function.Injective rationalQuotientTensorMap := by
  intro h
  let : Subsingleton (∀ n : ℕ+, TensorProduct ℤ ℚ (ZMod (n : ℕ))) :=
    rationalQuotientTensorProduct_subsingleton
  let : Subsingleton (TensorProduct ℤ ℚ (∀ n : ℕ+, ZMod (n : ℕ))) :=
    h.subsingleton
  let : Nontrivial (TensorProduct ℤ ℚ (∀ n : ℕ+, ZMod (n : ℕ))) :=
    rationalQuotientTensorProduct_nontrivial
  exact (not_subsingleton _) (inferInstance :
    Subsingleton (TensorProduct ℤ ℚ (∀ n : ℕ+, ZMod (n : ℕ))))

def integerFamily : ℕ+ → ModuleCat ℤ :=
  fun _ => ModuleCat.of ℤ ℤ

def integerProductTensorEquiv :
    (∀ _ : ℕ+, TensorProduct ℤ ℚ ℤ) ≃ₗ[ℤ] ∀ _ : ℕ+, ℚ :=
  LinearEquiv.piCongrRight (fun _ => TensorProduct.rid ℤ ℚ)

def rationalIntegerProductTensorMap :
    TensorProduct ℤ ℚ (∀ _ : ℕ+, ℤ) →ₗ[ℤ] ∀ _ : ℕ+, ℚ :=
  integerProductTensorEquiv.toLinearMap.comp
    (productTensorMap rationalModule integerFamily)

def commonDenominatorSequences {A : Type v} : Set (A → ℚ) :=
  {x | ∃ m : ℤ, m ≠ 0 ∧ ∀ a, ∃ z : ℤ, x a = (z : ℚ) / (m : ℚ)}

theorem rationalIntegerProductTensorMap_range :
    Set.range rationalIntegerProductTensorMap =
      commonDenominatorSequences (A := ℕ+) := by
  have hmap (q : ℚ) (z : ∀ _ : ℕ+, ℤ) :
      rationalIntegerProductTensorMap (q ⊗ₜ[ℤ] z) =
        fun a => (z a : ℚ) • q := by
    ext a
    change (TensorProduct.rid ℤ ℚ) (q ⊗ₜ[ℤ] z a) = _
    simp [smul_eq_mul]
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    induction y using TensorProduct.induction_on with
    | zero =>
        refine ⟨1, one_ne_zero, ?_⟩
        intro a
        refine ⟨0, ?_⟩
        simp [rationalIntegerProductTensorMap]
    | tmul q z =>
        have hq : q = (q.num : ℚ) / (q.den : ℚ) := by
          simpa using q.num_div_den.symm
        refine ⟨(q.den : ℤ), Int.natCast_ne_zero.mpr q.den_nz, ?_⟩
        intro a
        refine ⟨z a * q.num, ?_⟩
        rw [hmap]
        change (z a : ℚ) * q = _
        conv_lhs => rw [hq]
        simp [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm]
    | add x y hx hy =>
        rcases hx with ⟨m, hm, hx⟩
        rcases hy with ⟨n, hn, hy⟩
        rw [map_add]
        refine ⟨m * n, mul_ne_zero hm hn, ?_⟩
        intro a
        obtain ⟨zx, hzx⟩ := hx a
        obtain ⟨zy, hzy⟩ := hy a
        refine ⟨zx * n + zy * m, ?_⟩
        change rationalIntegerProductTensorMap x a + rationalIntegerProductTensorMap y a = _
        rw [hzx, hzy]
        have hm' : (m : ℚ) ≠ 0 := by exact_mod_cast hm
        have hn' : (n : ℚ) ≠ 0 := by exact_mod_cast hn
        field_simp [hm', hn']
        simp only [Int.cast_add, Int.cast_mul]
        ring
  · rintro ⟨m, hm, hx⟩
    choose z hz using hx
    refine ⟨(1 / (m : ℚ)) ⊗ₜ[ℤ] z, ?_⟩
    ext a
    rw [hmap, hz a]
    simp [smul_eq_mul, div_eq_mul_inv]
/-
  have hmap (q : ℚ) (z : ∀ _ : ℕ+, ℤ) :
      rationalIntegerProductTensorMap (q ⊗ₜ[ℤ] z) =
        fun a => (z a : ℚ) • q := by
    ext a
    simp [rationalIntegerProductTensorMap, integerProductTensorEquiv,
      productTensorMap, Int.cast_smul_eq_zsmul]
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    induction y using TensorProduct.induction_on with
    | zero =>
        refine ⟨1, one_ne_zero, ?_⟩
        intro a
        refine ⟨0, ?_⟩
        simp [rationalIntegerProductTensorMap]
    | tmul q z =>
        have hq : q = (q.num : ℚ) / (q.den : ℚ) := by
          simpa using q.num_div_den.symm
        refine ⟨(q.den : ℤ), Int.natCast_ne_zero.mpr q.den_nz, ?_⟩
        intro a
        refine ⟨z a * q.num, ?_⟩
        rw [hmap, hq]
        simp [smul_eq_mul, div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm]
    | add x y hx hy =>
        rcases hx with ⟨m, hm, hx⟩
        rcases hy with ⟨n, hn, hy⟩
        rw [map_add]
        refine ⟨m * n, mul_ne_zero hm hn, ?_⟩
        intro a
        obtain ⟨zx, hzx⟩ := hx a
        obtain ⟨zy, hzy⟩ := hy a
        refine ⟨zx * n + zy * m, ?_⟩
        rw [hzx, hzy]
        have hm' : (m : ℚ) ≠ 0 := by exact_mod_cast hm
        have hn' : (n : ℚ) ≠ 0 := by exact_mod_cast hn
        field_simp [hm', hn'] <;> ring
  · rintro ⟨m, hm, hx⟩
    choose z hz using hx
    refine ⟨(1 / (m : ℚ)) ⊗ₜ[ℤ] z, ?_⟩
    ext a
    rw [hmap, hz a]
        simp [smul_eq_mul, div_eq_mul_inv] -/

theorem rationalIntegerProductTensorMap_not_surjective :
    ¬Function.Surjective rationalIntegerProductTensorMap := by
  intro h
  let x : ℕ+ → ℚ := fun n => 1 / (n : ℚ)
  have hx : x ∈ commonDenominatorSequences (A := ℕ+) := by
    rw [← rationalIntegerProductTensorMap_range]
    rcases h x with ⟨y, hy⟩
    exact ⟨y, hy⟩
  rcases hx with ⟨m, hm, hx⟩
  let N : ℕ := m.natAbs + 1
  let n : ℕ+ := ⟨N, Nat.succ_pos _⟩
  obtain ⟨z, hz⟩ := hx n
  have hn0 : (N : ℚ) ≠ 0 := by
    exact_mod_cast n.property.ne'
  have hz' : (1 : ℚ) / (N : ℚ) = (z : ℚ) / (m : ℚ) := by
    simpa [x, n, N] using hz
  have hcross : (m : ℚ) = (z : ℚ) * (N : ℚ) := by
    have hm0 : (m : ℚ) ≠ 0 := by exact_mod_cast hm
    field_simp [hm0, hn0] at hz'
    simpa [mul_comm] using hz'
  have hcrossZ : m = z * (N : ℤ) := by
    exact_mod_cast hcross
  have hdvd : (N : ℤ) ∣ m := by
    refine ⟨z, ?_⟩
    rw [hcrossZ, mul_comm]
  have hle : N ≤ m.natAbs := by
    exact Nat.le_of_dvd (by omega) (Int.natCast_dvd.mp hdvd)
  dsimp [N] at hle
  omega
/-
  intro h
  let x : ℕ+ → ℚ := fun n => 1 / (n : ℚ)
  have hx : x ∈ commonDenominatorSequences (A := ℕ+) := by
    rw [← rationalIntegerProductTensorMap_range]
    rcases h x with ⟨y, hy⟩
    exact ⟨y, hy⟩
  rcases hx with ⟨m, hm, hx⟩
  let N : ℕ := m.natAbs + 1
  let n : ℕ+ := ⟨N, Nat.succ_pos _⟩
  obtain ⟨z, hz⟩ := hx n
  have hn0 : (N : ℚ) ≠ 0 := by
    exact_mod_cast n.property.ne'
  have hz' : (1 : ℚ) / (N : ℚ) = (z : ℚ) / (m : ℚ) := by
    simpa [x, n, N] using hz
  have hcross : (m : ℚ) = (z : ℚ) * (N : ℚ) := by
    have hm0 : (m : ℚ) ≠ 0 := by exact_mod_cast hm
    field_simp [hm0, hn0] at hz'
    simpa [mul_comm] using hz'
  have hcrossZ : m = z * (N : ℤ) := by
    exact_mod_cast hcross
  have hdvd : (N : ℤ) ∣ m := by
    refine ⟨z, ?_⟩
    rw [hcrossZ, mul_comm]
  have hle : N ≤ m.natAbs := by
    exact Nat.le_of_dvd (by omega) (Int.natCast_dvd.mp hdvd)
  dsimp [N] at hle
  omega -/

/-! ## Finitely generated and finitely presented modules -/

/-- The four equivalent criteria for finite generation from Proposition 89.1. -/
theorem finite_generation_tensor_iff
    {R : Type u} [CommRing R] (M : ModuleCat.{w} R) :
    List.TFAE [
      Module.Finite R (M : Type w),
      ∀ (A : Type (max v w)) (Q : A → ModuleCat.{max u z} R),
        Function.Surjective (productTensorMap M Q),
      ∀ (Q : ModuleCat.{max u z} R) (A : Type (max v w)),
        Function.Surjective (productTensorMap M (fun _ : A => Q)),
      ∀ (A : Type (max v w)),
        Function.Surjective (tensorModulePowerMap M (A := A))
    ] := by
  classical
  tfae_have 1 → 2 := by
    intro h A Q
    ·
      let : Module.Finite R (M : Type w) := h
      obtain ⟨n, f, hf⟩ := Module.Finite.exists_fin' R (M : Type w)
      let g : Fin n → (M : Type w) := fun i => f (Pi.single i 1)
      have hgen : ∀ m : (M : Type w), ∃ c : Fin n → R,
          m = ∑ i, c i • g i := by
        intro m
        obtain ⟨c, hc⟩ := hf m
        have hc' : c = ∑ i, c i • Pi.single i (1 : R) := by
          calc
            c = ∑ i, Pi.single i (c i) := (Finset.univ_sum_single c).symm
            _ = ∑ i, c i • Pi.single i (1 : R) := by
              apply Finset.sum_congr rfl
              intro i hi
              ext j
              by_cases hij : i = j <;> simp [hij]
        refine ⟨c, ?_⟩
        calc
          m = f c := hc.symm
          _ = f (∑ i, c i • Pi.single i (1 : R)) := congrArg f hc'
          _ = ∑ i, c i • g i := by simp [g]
      have hdecomp (a : A)
          (x : TensorProduct R (M : Type w) (Q a : Type (max u z))) :
          ∃ q : Fin n → (Q a : Type (max u z)),
            x = ∑ i, g i ⊗ₜ[R] q i := by
        induction x using TensorProduct.induction_on with
        | zero =>
            refine ⟨fun _ => 0, ?_⟩
            simp
        | tmul m q =>
            obtain ⟨c, hc⟩ := hgen m
            refine ⟨fun i => c i • q, ?_⟩
            rw [hc, TensorProduct.sum_tmul]
            apply Finset.sum_congr rfl
            intro i hi
            simp [TensorProduct.smul_tmul, TensorProduct.tmul_smul]
        | add x y hx hy =>
            obtain ⟨qx, hqx⟩ := hx
            obtain ⟨qy, hqy⟩ := hy
            refine ⟨fun i => qx i + qy i, ?_⟩
            rw [hqx, hqy, ← Finset.sum_add_distrib]
            apply Finset.sum_congr rfl
            intro i hi
            rw [TensorProduct.tmul_add]
      intro y
      choose q hq using fun a => hdecomp a (y a)
      let t : TensorProduct R (M : Type w)
          (∀ a, (Q a : Type (max u z))) :=
        ∑ i, g i ⊗ₜ[R] (fun a => q a i)
      refine ⟨t, ?_⟩
      ext a
      simpa [t, productTensorMap] using (hq a).symm
  tfae_have 2 → 3 := by
    intro h Q A
    exact h A (fun _ => Q)
  tfae_have 3 → 4 := by
    intro h A y
    let U := ULift.{max u z} R
    let Q : ModuleCat.{max u z} R := ModuleCat.of R U
    let eU : TensorProduct R (M : Type w) U ≃ₗ[R] (M : Type w) :=
      (TensorProduct.congr (LinearEquiv.refl R (M : Type w))
        (ULift.moduleEquiv (R := R) (M := R))).trans
          (TensorProduct.rid R (M : Type w))
    let ePi : (A → U) ≃ₗ[R] (A → R) :=
      LinearEquiv.piCongrRight (fun _ => ULift.moduleEquiv)
    let eSource : TensorProduct R (M : Type w) (A → U) ≃ₗ[R]
        TensorProduct R (M : Type w) (A → R) :=
      TensorProduct.congr (LinearEquiv.refl R (M : Type w)) ePi
    let eTarget : (∀ _ : A, TensorProduct R (M : Type w) U) ≃ₗ[R]
        (A → (M : Type w)) :=
      LinearEquiv.piCongrRight (fun _ => eU)
    obtain ⟨x, hx⟩ := h Q A (eTarget.symm y)
    refine ⟨eSource x, ?_⟩
    have hcomm : tensorModulePowerMap M (eSource x) =
        eTarget (productTensorMap M (fun _ : A => Q) x) := by
      clear hx y
      induction x using TensorProduct.induction_on with
      | zero => simp [eSource, eTarget]
      | tmul m q =>
          ext a
          simp [eSource, eTarget, eU, ePi, Q, U,
            tensorModulePowerMap_tmul, productTensorMap_tmul]
      | add x y hx hy => simp [map_add, hx, hy]
    rw [hcomm, hx, eTarget.apply_symm_apply]
  tfae_have 4 → 1 := by
    intro h
    ·
      have hrepr {A : Type (max v w)}
          (x : TensorProduct R (M : Type w) (A → R)) :
          ∃ k, ∃ (m : Fin k → (M : Type w)),
            ∃ (q : Fin k → (A → R)),
            tensorModulePowerMap M x = fun y => ∑ i, q i y • m i := by
        induction x using TensorProduct.induction_on with
        | zero =>
            refine ⟨0, (fun i => Fin.elim0 i), (fun i => Fin.elim0 i), ?_⟩
            ext y
            simp [tensorModulePowerMap]
        | tmul m q =>
            refine ⟨1, (fun _ => m), (fun _ => q), ?_⟩
            ext y
            simp [tensorModulePowerMap_tmul]
        | add x y hx hy =>
            obtain ⟨k, m, q, hx⟩ := hx
            obtain ⟨l, m', q', hy⟩ := hy
            refine ⟨k + l, Fin.addCases m m', Fin.addCases q q', ?_⟩
            rw [map_add, hx, hy]
            ext y
            simp [Fin.sum_univ_add]
      let A := ULift.{max v} (M : Type w)
      obtain ⟨x, hx⟩ := h A (fun y : A => y.down)
      obtain ⟨k, m, q, hq⟩ := hrepr x
      refine Module.Finite.of_surjective (Fintype.linearCombination R m) ?_
      intro y
      refine ⟨fun i => q i (ULift.up y), ?_⟩
      rw [Fintype.linearCombination_apply]
      exact (congrFun (hx.symm.trans hq) (ULift.up y)).symm
  tfae_finish

/-- Reorder two (possibly large) products. -/
private def piSwapLinearEquiv {R : Type u} [CommRing R]
    {A : Type v} {B : Type w} {X : A → Type z}
    [∀ a, AddCommGroup (X a)] [∀ a, Module R (X a)] :
    (B → ∀ a, X a) ≃ₗ[R] (∀ a, B → X a) where
  toFun f a b := f b a
  invFun f b a := f a b
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Coordinates identify tensoring a finite free module with a finite product. -/
private def finFreeTensorEquiv {R : Type u} [CommRing R]
    (n : ℕ) (X : Type v) [AddCommGroup X] [Module R X] :
    TensorProduct R (Fin n → R) X ≃ₗ[R] (Fin n → X) :=
  (TensorProduct.piLeft R X (fun _ : Fin n => R)).trans
    (LinearEquiv.piCongrRight (fun _ => TensorProduct.lid R X))

/-- Tensoring a finite free module commutes with arbitrary products. -/
private def finFreeProductTensorEquiv {R : Type u} [CommRing R]
    (n : ℕ) {A : Type v} (Q : A → ModuleCat.{z} R) :
    TensorProduct R (Fin n → R) (∀ a, (Q a : Type z)) ≃ₗ[R]
      ∀ a, TensorProduct R (Fin n → R) (Q a : Type z) :=
  (finFreeTensorEquiv n (∀ a, (Q a : Type z))).trans <|
    piSwapLinearEquiv.trans <|
      LinearEquiv.piCongrRight (fun a =>
        (finFreeTensorEquiv n (Q a : Type z)).symm)

private lemma finFreeProductTensorEquiv_apply {R : Type u} [CommRing R]
    (n : ℕ) {A : Type v} (Q : A → ModuleCat.{z} R)
    (x : TensorProduct R (Fin n → R) (∀ a, (Q a : Type z))) :
    finFreeProductTensorEquiv n Q x =
      productTensorMap (ModuleCat.of R (Fin n → R)) Q x := by
  induction x using TensorProduct.induction_on with
  | zero => simp [finFreeProductTensorEquiv]
  | tmul m q =>
      ext a
      apply (finFreeTensorEquiv n (Q a : Type z)).injective
      ext i
      simp [finFreeProductTensorEquiv, finFreeTensorEquiv,
        piSwapLinearEquiv, productTensorMap]
  | add x y hx hy => simp [map_add, hx, hy]

private lemma productTensorMap_rTensor {R : Type u} [CommRing R]
    {A : Type v} {P : ModuleCat.{x} R} {M : ModuleCat.{w} R}
    (Q : A → ModuleCat.{z} R)
    (f : (P : Type x) →ₗ[R] (M : Type w))
    (x : TensorProduct R (P : Type x) (∀ a, (Q a : Type z))) :
    productTensorMap M Q (f.rTensor (∀ a, (Q a : Type z)) x) =
      fun a => f.rTensor (Q a : Type z) (productTensorMap P Q x a) := by
  induction x using TensorProduct.induction_on with
  | zero => ext a; simp
  | tmul p q => ext a; simp [productTensorMap]
  | add x y hx hy => ext a; simp [map_add, hx, hy]

private lemma tensorModulePowerMap_rTensor {R : Type u} [CommRing R]
    {A : Type v} {P : ModuleCat.{x} R} {M : ModuleCat.{w} R}
    (f : (P : Type x) →ₗ[R] (M : Type w))
    (t : TensorProduct R (P : Type x) (A → R)) :
    tensorModulePowerMap M (f.rTensor (A → R) t) =
      fun a => f (tensorModulePowerMap P t a) := by
  induction t using TensorProduct.induction_on with
  | zero => ext a; simp
  | tmul p q => ext a; simp [tensorModulePowerMap_tmul]
  | add x y hx hy => ext a; simp [map_add, hx, hy]

/-- The four equivalent criteria for finite presentation from Proposition 89.2. -/
theorem finite_presentation_tensor_iff
    {R : Type u} [CommRing R] (M : ModuleCat.{w} R) :
    List.TFAE [
      Module.FinitePresentation R (M : Type w),
      ∀ (A : Type (max u v w)) (Q : A → ModuleCat.{max u z} R),
        Function.Bijective (productTensorMap M Q),
      ∀ (Q : ModuleCat.{max u z} R) (A : Type (max u v w)),
        Function.Bijective (productTensorMap M (fun _ : A => Q)),
      ∀ (A : Type (max u v w)),
        Function.Bijective (tensorModulePowerMap M (A := A))
    ] := by
  classical
  tfae_have 1 → 2 := by
    intro h A Q
    obtain ⟨n, m, p, g, hp, hgp⟩ :=
      Module.FinitePresentation.exists_fin' (fp := h) R (M : Type w)
    obtain ⟨s, hs, _⟩ := h.out
    have hfinite : Module.Finite R (M : Type w) :=
      ⟨hs ▸ Submodule.fg_span s.finite_toSet⟩
    have hfinite_criterion : Module.Finite R (M : Type w) ↔
        ∀ (A : Type (max u v w)) (Q : A → ModuleCat.{max u z} R),
          Function.Surjective (productTensorMap M Q) :=
      (finite_generation_tensor_iff.{u, max u v, w, z} M).out 0 1
    have hsurj : Function.Surjective (productTensorMap M Q) :=
      hfinite_criterion.mp hfinite A Q
    refine ⟨?_, hsurj⟩
    intro x y hxy
    apply sub_eq_zero.mp
    have hzero : productTensorMap M Q (x - y) = 0 := by
      rw [map_sub, hxy, sub_self]
    obtain ⟨t, ht⟩ := LinearMap.rTensor_surjective
      (∀ a, (Q a : Type (max u z))) hp (x - y)
    have hcomponent (a : A) :
        p.rTensor (Q a : Type (max u z))
          (productTensorMap (ModuleCat.of R (Fin n → R)) Q t a) = 0 := by
      have hz := congrFun hzero a
      rw [← ht] at hz
      exact (congrFun (productTensorMap_rTensor
        (P := ModuleCat.of R (Fin n → R)) (M := M) Q p t) a).symm.trans <|
        by simpa only [Pi.zero_apply] using hz
    have hexact (a : A) : Function.Exact
        (g.rTensor (Q a : Type (max u z)))
        (p.rTensor (Q a : Type (max u z))) :=
      rTensor_exact (Q a : Type (max u z)) hgp hp
    have hpre (a : A) : ∃ za,
        g.rTensor (Q a : Type (max u z)) za =
          productTensorMap (ModuleCat.of R (Fin n → R)) Q t a := by
      have hmem : productTensorMap (ModuleCat.of R (Fin n → R)) Q t a ∈
          LinearMap.ker (p.rTensor (Q a : Type (max u z))) :=
        LinearMap.mem_ker.mpr (hcomponent a)
      rw [LinearMap.exact_iff.mp (hexact a)] at hmem
      exact hmem
    choose z hz using hpre
    let z' : TensorProduct R (Fin m → R)
        (∀ a, (Q a : Type (max u z))) :=
      (finFreeProductTensorEquiv m Q).symm z
    have hprod : productTensorMap (ModuleCat.of R (Fin n → R)) Q
        (t - g.rTensor (∀ a, (Q a : Type (max u z))) z') = 0 := by
      funext a
      rw [map_sub]
      change productTensorMap (ModuleCat.of R (Fin n → R)) Q t a -
        productTensorMap (ModuleCat.of R (Fin n → R)) Q
          (g.rTensor (∀ a, (Q a : Type (max u z))) z') a = 0
      rw [congrFun (productTensorMap_rTensor
        (P := ModuleCat.of R (Fin m → R))
        (M := ModuleCat.of R (Fin n → R)) Q g z') a]
      rw [← finFreeProductTensorEquiv_apply n Q t,
        ← finFreeProductTensorEquiv_apply m Q z']
      change (finFreeProductTensorEquiv n Q) t a -
        g.rTensor (Q a : Type (max u z))
          ((finFreeProductTensorEquiv m Q) z' a) = 0
      rw [show (finFreeProductTensorEquiv m Q) z' = z by
        simp [z']]
      apply sub_eq_zero.mpr
      rw [finFreeProductTensorEquiv_apply]
      exact (hz a).symm
    have htzero : t - g.rTensor
        (∀ a, (Q a : Type (max u z))) z' = 0 :=
      (show Function.Injective
          (productTensorMap (ModuleCat.of R (Fin n → R)) Q) by
        intro a b hab
        apply (finFreeProductTensorEquiv n Q).injective
        rw [finFreeProductTensorEquiv_apply,
          finFreeProductTensorEquiv_apply]
        exact hab) hprod
    have ht' : t = g.rTensor (∀ a, (Q a : Type (max u z))) z' :=
      sub_eq_zero.mp htzero
    rw [← ht, ht']
    apply LinearMap.mem_ker.mp
    have hmem : g.rTensor (∀ a, (Q a : Type (max u z))) z' ∈
        LinearMap.range (g.rTensor (∀ a, (Q a : Type (max u z)))) :=
      LinearMap.mem_range_self _ z'
    rw [← LinearMap.exact_iff.mp
      (rTensor_exact (∀ a, (Q a : Type (max u z))) hgp hp)] at hmem
    exact hmem
  tfae_have 2 → 3 := by
    intro h Q A
    exact h A (fun _ => Q)
  tfae_have 3 → 4 := by
    intro h A
    -- This is the same universe-raising comparison used for finite generation.
    let U := ULift.{max u z} R
    let Q : ModuleCat.{max u z} R := ModuleCat.of R U
    let eU : TensorProduct R (M : Type w) U ≃ₗ[R] (M : Type w) :=
      (TensorProduct.congr (LinearEquiv.refl R (M : Type w))
        (ULift.moduleEquiv (R := R) (M := R))).trans
          (TensorProduct.rid R (M : Type w))
    let ePi : (A → U) ≃ₗ[R] (A → R) :=
      LinearEquiv.piCongrRight (fun _ => ULift.moduleEquiv)
    let eSource : TensorProduct R (M : Type w) (A → U) ≃ₗ[R]
        TensorProduct R (M : Type w) (A → R) :=
      TensorProduct.congr (LinearEquiv.refl R (M : Type w)) ePi
    let eTarget : (∀ _ : A, TensorProduct R (M : Type w) U) ≃ₗ[R]
        (A → (M : Type w)) :=
      LinearEquiv.piCongrRight (fun _ => eU)
    have hcomm (x : TensorProduct R (M : Type w) (A → U)) :
        tensorModulePowerMap M (eSource x) =
          eTarget (productTensorMap M (fun _ : A => Q) x) := by
      induction x using TensorProduct.induction_on with
      | zero => simp [eSource, eTarget]
      | tmul m q =>
          ext a
          simp [eSource, eTarget, eU, ePi, Q, U,
            tensorModulePowerMap_tmul, productTensorMap_tmul]
      | add x y hx hy => simp [map_add, hx, hy]
    have hb := h Q A
    constructor
    · intro x y hxy
      apply eSource.symm.injective
      apply hb.1
      apply eTarget.injective
      rw [← hcomm (eSource.symm x), ← hcomm (eSource.symm y)]
      simpa using hxy
    · intro y
      obtain ⟨x, hx⟩ := hb.2 (eTarget.symm y)
      exact ⟨eSource x, by rw [hcomm, hx, eTarget.apply_symm_apply]⟩
  tfae_have 4 → 1 := by
    intro h
    have hfinite_criterion : Module.Finite R (M : Type w) ↔
        ∀ (A : Type (max u v w)),
          Function.Surjective (tensorModulePowerMap M (A := A)) :=
      (finite_generation_tensor_iff.{u, max u v, w, z} M).out 0 3
    have hMfinite : Module.Finite R (M : Type w) :=
      hfinite_criterion.mpr fun A => (h A).2
    obtain ⟨n, p, hp⟩ :=
      @Module.Finite.exists_fin' R (M : Type w) _ _ _ hMfinite
    let F : ModuleCat.{u} R := ModuleCat.of R (Fin n → R)
    let K : ModuleCat.{u} R := ModuleCat.of R p.ker
    have hexact : Function.Exact p.ker.subtype p := by
      apply LinearMap.exact_iff.mpr
      ext x
      simp
    let A := ULift.{max v w} p.ker
    have hFfinite : Module.Finite R (F : Type u) := inferInstance
    have hFcriterion : Module.Finite R (F : Type u) ↔
        ∀ (A : Type (max u v w)),
          Function.Surjective (tensorModulePowerMap F (A := A)) :=
      (finite_generation_tensor_iff.{u, max v w, u, u} F).out 0 3
    obtain ⟨t, ht⟩ := hFcriterion.mp hFfinite A
      (fun a : A => ((a.down : p.ker) : Fin n → R))
    have hpt : p.rTensor (A → R) t = 0 := by
      apply (h A).1
      rw [map_zero, tensorModulePowerMap_rTensor
        (P := F) (M := M) p t]
      funext a
      rw [ht]
      exact a.down.property
    have hmem : t ∈ LinearMap.ker (p.rTensor (A → R)) :=
      LinearMap.mem_ker.mpr hpt
    rw [LinearMap.exact_iff.mp
      (rTensor_exact (A → R) hexact hp)] at hmem
    obtain ⟨y, hy⟩ := hmem
    have hrepr (y : TensorProduct R p.ker (A → R)) :
        ∃ k, ∃ (m : Fin k → p.ker), ∃ (q : Fin k → A → R),
          tensorModulePowerMap K y =
            fun a => ∑ i, q i a • m i := by
      induction y using TensorProduct.induction_on with
      | zero =>
          refine ⟨0, (fun i => Fin.elim0 i), (fun i => Fin.elim0 i), ?_⟩
          ext a
          simp
      | tmul m q =>
          refine ⟨1, (fun _ => m), (fun _ => q), ?_⟩
          rw [tensorModulePowerMap_tmul]
          funext a
          simp
      | add x y hx hy =>
          obtain ⟨k, m, q, hx⟩ := hx
          obtain ⟨l, m', q', hy⟩ := hy
          refine ⟨k + l, Fin.addCases m m', Fin.addCases q q', ?_⟩
          rw [map_add, hx, hy]
          ext a
          simp [Fin.sum_univ_add]
    obtain ⟨k, m, q, hq⟩ := hrepr y
    have hKfinite : Module.Finite R p.ker :=
      Module.Finite.of_surjective (Fintype.linearCombination R m) <| by
        intro x
        refine ⟨fun i => q i (ULift.up x), ?_⟩
        rw [Fintype.linearCombination_apply]
        apply Subtype.ext
        have hx := congrFun ht (ULift.up x)
        rw [← hy, tensorModulePowerMap_rTensor
          (P := K) (M := F) p.ker.subtype y] at hx
        change p.ker.subtype
          (tensorModulePowerMap K y (ULift.up x)) = (x : Fin n → R) at hx
        rw [congrFun hq (ULift.up x)] at hx
        simpa using hx
    apply Module.finitePresentation_of_surjective p hp
    exact Module.Finite.iff_fg.mp hKfinite
  tfae_finish

/-- Tensor-kernel elements for finitely presented source modules factor through
    a finitely presented intermediate module (Lemma 89.3). -/
theorem kernel_tensored_finitelyPresented
    {R : Type u} [CommRing R] (M P Q : ModuleCat.{max u w} R)
    (hP : Module.FinitePresentation R (P : Type (max u w)))
    (f : (P : Type (max u w)) →ₗ[R] (M : Type (max u w)))
    (x : TensorProduct R (P : Type (max u w)) (Q : Type (max u w)))
    (hx : x ∈ LinearMap.ker (f.rTensor (Q : Type (max u w)))) :
    ∃ P' : ModuleCat.{max u w} R,
      Module.FinitePresentation R (P' : Type (max u w)) ∧
        ∃ f' : (P : Type (max u w)) →ₗ[R] (P' : Type (max u w)),
          (∃ g : (P' : Type (max u w)) →ₗ[R] (M : Type (max u w)), f = g.comp f') ∧
            x ∈ LinearMap.ker (f'.rTensor (Q : Type (max u w))) := by
  /-
  Proof roadmap.  This declaration is the public Chapter 89 name for an
  interface already proved in Chapter 88.  Use
  `exists_finitelyPresented_kernel_factor M P Q hP f x hx` from
  `Formalization/Books/Algebra/Unit88/MittagLefflerModules.lean`.  Its ring,
  the three `ModuleCat.{max u w}` objects, the factorization orientation
  `f = g.comp f'`, and the final `rTensor Q` kernel membership are
  definitionally the goal here, so `exact` (not a `simpa` that re-infers the
  maximum universe) closes the proof.
  -/
  sorry

/-- The tensor-product characterization of Mittag--Leffler modules
    (Proposition 89.4). -/
theorem mittagLeffler_tensor_iff
    {R : Type u} [CommRing R] (M : ModuleCat.{w} R) :
    List.TFAE [
      IsMittagLefflerModule M,
      ∀ (A : Type (max v w)) (Q : A → ModuleCat.{max u z} R),
        Function.Injective (productTensorMap M Q)
    ] := by
  /-
  Proof roadmap (Stacks Project, Proposition 10.89.5).

  * First isolate universe transport.  Put all carriers in
    `Type (max u v w z)` with `ULift.moduleEquiv`, and prove local conjugacy
    formulas for `LinearMap.rTensor` and `productTensorMap` by
    `TensorProduct.induction_on`.  Transport `MLModuleCondition` across those
    linear equivalences by composing its test map and its two domination
    inclusions.  This is needed because the filtered-colimit API below uses
    `ModuleCat.{max u _}`, whereas the theorem deliberately accepts `M` in
    `ModuleCat.{w}` and the family in `ModuleCat.{max u z}`.
  * For `1 -> 2`, choose
    `exists_finitelyPresentedFilteredColimit` from
    `Formalization/Books/Algebra/Unit88/MittagLefflerModules.lean` for the
    (transported) `M`.  Represent `x - y` at one stage with
    `finitelyPresentedFilteredColimit_tensor_rep` (commute the two tensor
    factors with `TensorProduct.comm` before and after applying that lemma).
    Apply the ML condition to the finitely presented stage and its cocone
    map.  Factor the resulting finitely presented comparison object through
    a later stage using `finitelyPresentedFilteredColimit_map_factor`; after
    taking a common filtered successor, the transition map and the cocone
    map mutually dominate.  The coordinate vanishing supplied by the
    hypothesis therefore holds after that transition.  Both stage product
    maps are injective by `(finite_presentation_tensor_iff _).out 0 1` and
    the `finitelyPresented` field of the presentation, so the stage tensor is
    zero and hence `x = y`.  Use `productTensorMap_rTensor` for every square.
  * For `2 -> 1`, unfold `IsMittagLefflerModule`/`MLModuleCondition` and fix
    `P`, `hP`, and `f`.  Index a family by codes for finite presentations
    `(Fin m -> R) -> (Fin n -> R)` together with elements of the corresponding
    tensor kernel; use `ULift` so that the index is exactly
    `Type (max v w)` and the coded quotients are in
    `ModuleCat.{max u z}`.  Surjectivity of
    `productTensorMap P` follows from `(finite_presentation_tensor_iff P).out
    0 1`, so lift the tuple of all kernel elements to a single tensor `t`.
    Naturality (`productTensorMap_rTensor`) and the assumed injectivity for
    `M` show `t` lies in the kernel of `f.rTensor`.
  * Apply `kernel_tensored_finitelyPresented` to obtain `P'` and `f'`.
    Injectivity/bijectivity of the product maps for `P` and `P'` shows every
    coded kernel element for `f` is killed by `f'`.  Transport from the coded
    presentation to an arbitrary finitely presented test module, then use
    `dominates_iff_finitelyPresented` from Unit88 for `dominates f' f`.
    The factorization `f = g.comp f'` gives `dominates f f'` directly via
    `LinearMap.rTensor_comp_apply`.  Return `P'`, its finite-presentation
    proof, `f'`, and these two inclusions, then finish the two-entry TFAE with
    `tfae_finish`.
  -/
  sorry

/-! ## Permanence lemmas -/

/-- The predicate that an element of `F ⊗ M` comes from `F' ⊗ M`. -/
def tensorProductContains
    {R : Type u} {F : Type v} {M : Type w} [CommRing R]
    [AddCommGroup F] [AddCommGroup M] [Module R F] [Module R M]
    (F' : Submodule R F) (x : TensorProduct R F M) : Prop :=
  ∃ y : TensorProduct R (F' : Type v) M,
    F'.subtype.rTensor M y = x

/- The smallest submodule in Lemma 89.5 is expressed by `IsLeast` in the
   complete lattice of submodules. -/
theorem minimal_tensor_submodule
    {R : Type u} {F : Type v} {M : Type w} [CommRing R]
    [AddCommGroup F] [AddCommGroup M] [Module R F] [Module R M]
    (hflat : Module.Flat R M)
    (hML : IsMittagLefflerModule (ModuleCat.of R M))
    (x : TensorProduct R F M) :
    ∃ F' : Submodule R F,
      IsLeast {G : Submodule R F | tensorProductContains G x} F' ∧
        Module.Finite R (F' : Type v) := by
  /-
  Proof roadmap (Stacks Project, Lemma 10.89.6).

  * Let `S := {G : Submodule R F | tensorProductContains G x}` and
    `F' := sInf S`.  The family is nonempty because `top` contains `x`
    (use the inverse of `Submodule.topEquiv` on the first tensor factor), so
    `F'` is automatically the least member once containment is proved.
  * Bundle `q : F ->ₗ[R] (forall G : S, F / G.1)` with
    `LinearMap.pi (fun G => G.1.mkQ)`.  Show
    `LinearMap.ker q = F'` using `LinearMap.ker_pi`,
    `Submodule.ker_mkQ`, and membership in `sInf`.  For every coordinate,
    the witness in `tensorProductContains G.1 x` and
    `G.1.mkQ.comp G.1.subtype = 0` show
    `(G.1.mkQ.rTensor M) x = 0`.
  * Apply the injective half of `(mittagLeffler_tensor_iff
    (ModuleCat.of R M)).out 0 1` to the quotient family (raise the subtype
    index and quotient carriers with `ULift` at the theorem's explicit
    universes).  Use `TensorProduct.comm` and `productTensorMap_rTensor` to
    identify its source map with `q.rTensor M`; conclude
    `(q.rTensor M) x = 0`.
  * From `LinearMap.exact_subtype_ker_map q` and `hflat`, obtain
    `Function.Exact (F'.subtype.rTensor M) (q.rTensor M)` via
    `Module.Flat.rTensor_exact`.  Exactness supplies a tensor over `F'`
    mapping to `x`, hence `tensorProductContains F' x` and the required
    `IsLeast` pair.
  * Finally induct on that tensor witness with `TensorProduct.induction_on`
    to write it as a finite sum of pure tensors.  Let `G <= F'` be the span
    of the finitely many first components.  The same expression proves that
    `G` contains `x`; minimality gives `F' <= G`, while construction gives
    `G <= F'`.  Rewrite by equality and use `Submodule.fg_span` (or
    `Module.Finite.iff_fg`) to prove `Module.Finite R F'`.
  -/
  sorry

/-- In a universally exact sequence, Mittag--Lefflerness descends to the
    submodule and ascends from both ends (Lemma 89.6). -/
theorem pure_submodule_mittagLeffler
    {R : Type u} [CommRing R] {M₁ M₂ M₃ : ModuleCat.{w} R}
    (f₁ : (M₁ : Type w) →ₗ[R] (M₂ : Type w))
    (f₂ : (M₂ : Type w) →ₗ[R] (M₃ : Type w))
    (hseq : universallyExact f₁ f₂) :
    (IsMittagLefflerModule M₂ → IsMittagLefflerModule M₁) ∧
      ((IsMittagLefflerModule M₁ ∧ IsMittagLefflerModule M₃) →
        IsMittagLefflerModule M₂) := by
  /-
  Proof roadmap (Stacks Project, Lemma 10.89.7).  Use the injectivity
  criterion `(mittagLeffler_tensor_iff _).out 0 1` for all three modules and
  fix one family `Q`.  The naturality squares are exactly
  `productTensorMap_rTensor Q f₁` and `productTensorMap_rTensor Q f₂`.

  For the first implication, equality after `productTensorMap M₁ Q` maps,
  by the `f₁` square, to equality after `productTensorMap M₂ Q`; injectivity
  for `M₂`, followed by `hseq.2.2.2` instantiated at
  `forall a, (Q a : _)`, gives equality in the source.

  For the second implication, subtract the two candidate tensors.  Its image
  under `f₂.rTensor` has zero product coordinates, so injectivity for `M₃`
  makes that image zero.  Use
  `rTensor_exact (forall a, (Q a : _)) hseq.2.1 hseq.2.2.1` to write the
  difference as `f₁.rTensor` of a tensor over `M₁`.  The `f₁` naturality
  square and coordinatewise injectivity `hseq.2.2.2 (Q a : _)` make the
  latter tensor's product image zero; injectivity for `M₁` makes it zero.
  Restore equality with `sub_eq_zero.mp`.  Keep the components of
  `universallyExact` in the order displayed above: injective, exact,
  surjective, universally injective.
  -/
  sorry

/-- A quotient by a finitely generated submodule of a Mittag--Leffler module is
    Mittag--Leffler (Lemma 89.7). -/
theorem quotient_module_mittagLeffler
    {R : Type u} [CommRing R] {M₁ M₂ M₃ : ModuleCat.{w} R}
    (f₁ : (M₁ : Type w) →ₗ[R] (M₂ : Type w))
    (f₂ : (M₂ : Type w) →ₗ[R] (M₃ : Type w))
    (hexact : Function.Exact f₁ f₂)
    (hsurj : Function.Surjective f₂)
    (hfinite : Module.Finite R (M₁ : Type w))
    (hML : IsMittagLefflerModule M₂) :
    IsMittagLefflerModule M₃ := by
  /-
  Proof roadmap (Stacks Project, Lemma 10.89.8).  Apply the injectivity side
  of `mittagLeffler_tensor_iff` to `M₃` and fix `A`, `Q`, and a tensor `x`
  whose product image is zero.  Lift `x` to
  `y : M₂ tensor (forall a, Q a)` using
  `LinearMap.rTensor_surjective _ hsurj`.  For each coordinate, naturality
  (`productTensorMap_rTensor`) and the zero hypothesis put the coordinate of
  `productTensorMap M₂ Q y` in the kernel of `f₂.rTensor (Q a)`.

  Use `rTensor_exact (Q a) hexact hsurj` to choose coordinate preimages in
  `M₁ tensor Q a`.  Assemble them as a dependent function.  The surjective
  half of `(finite_generation_tensor_iff M₁).out 0 1`, instantiated with
  `hfinite`, lifts that function to
  `z : M₁ tensor (forall a, Q a)`.  Subtract
  `f₁.rTensor _ z` from `y`; its `M₂` product image is zero by the two
  naturality squares, hence the ML injectivity for `M₂` makes the difference
  zero.  Apply `f₂.rTensor` and use exactness (`hexact.comp_eq_zero`, or the
  corresponding consequence of `rTensor_exact`) to conclude `x = 0`.
  Prove injectivity by applying this kernel argument to `x - y`.
  -/
  sorry

/-- A directed colimit of Mittag--Leffler modules with universally injective
    transition maps is Mittag--Leffler (Lemma 89.8). -/
theorem colimit_mittagLeffler_of_universallyInjective
    {R : Type u} [CommRing R] {I : Type v} [Preorder I]
    [Nonempty I] [IsDirectedOrder I] {M : ModuleCat.{w} R}
    (P : ColimitPresentation I M)
    (hstage : ∀ i, IsMittagLefflerModule (P.diag.obj i))
    (htrans : ∀ {i j : I} (hij : i ≤ j),
      universallyInjective ((P.diag.map (homOfLE hij)).hom)) :
    IsMittagLefflerModule M := by
  /-
  Proof roadmap (Stacks Project, Lemma 10.89.9).

  * Establish first that every cocone component `(P.ι.app i).hom` is
    universally injective.  After tensoring by an arbitrary `N`, use
    `isColimitOfPreserves` for the module tensor-right functor (the
    construction `moduleTensorRightFunctor` in Unit88 is the model) and then
    `Types.FilteredColimit.isColimit_eq_iff'` after the two forgetful
    functors.  Equality in the colimit becomes equality after a morphism
    `i -> j`.  Rewrite that preorder morphism as `homOfLE (leOfHom h)` and
    cancel it using `htrans (leOfHom h) N`.  When the ring or tensor carrier
    is above `w`, first conjugate by the same `ULift.moduleEquiv` transport
    used in `mittagLeffler_tensor_iff`.
  * Apply `(mittagLeffler_tensor_iff M).out 0 1`.  For a fixed family `Q`,
    represent the difference of two source tensors at some stage.  This can
    be proved by `TensorProduct.induction_on`, using joint surjectivity of the
    colimit cocone and `directed_of` to combine the finitely many stages; it
    is the generic-`ColimitPresentation` analogue of
    `finitelyPresentedFilteredColimit_tensor_rep` in Unit88.
  * The `productTensorMap_rTensor` square says that every coordinate of the
    stage product tensor maps to zero under the corresponding cocone
    component.  Cancel those maps with the universal injectivity established
    in the first step.  Now `(mittagLeffler_tensor_iff (P.diag.obj i)).out
    0 1` and `hstage i` make the represented stage tensor zero.  Its image is
    the original difference, so finish with `sub_eq_zero.mp`.
  -/
  sorry

/-- A direct sum is Mittag--Leffler exactly when each summand is
    Mittag--Leffler (Lemma 89.9). -/
theorem directSum_mittagLeffler_iff
    {R : Type u} [CommRing R] {I : Type v}
    (M : I → ModuleCat.{w} R) :
    IsMittagLefflerModule
        (ModuleCat.of R (⨁ i, (M i : Type w))) ↔
      ∀ i, IsMittagLefflerModule (M i) := by
  /-
  Proof roadmap (Stacks Project, Lemma 10.89.10).

  For `->`, each summand inclusion `DirectSum.lof R I (fun i => (M i :
  Type w)) i` has the coordinate projection as a left inverse (build it with
  `DirectSum.toModule` from
  `Mathlib/Algebra/DirectSum/Module.lean`, using a `dite` family which is the
  identity at `i` and zero elsewhere).  Either apply the first
  half of `pure_submodule_mittagLeffler` to the resulting split short exact
  sequence (`universallyExact_of_split` in Unit82), or make the shorter
  retract diagram for `productTensorMap`; injectivity of the direct-sum map
  then implies injectivity for the summand.  The latter route handles the
  `w` versus `max v w` carrier levels by conjugating with `ULift.moduleEquiv`.

  For `<-`, use `MLModuleCondition` directly.  A map from a finitely
  presented `P` has finite image support: obtain finite generators from
  `Module.Finite.exists_fin'`, take the union of the `DFinsupp.support`s of
  their images, and use linearity to show the map factors through the
  submodule `D_s` of the direct sum supported on that `Finset I`.  Prove
  `D_s` is Mittag--Leffler by induction on `s`, identifying the successor
  with a binary direct sum and applying the second half of
  `pure_submodule_mittagLeffler` to its split exact sequence.  Apply its ML
  condition to the factored map to obtain the finitely presented comparison
  map.  Finally compose with `D_s.subtype`; this inclusion has a linear left
  inverse (coordinate truncation), hence is universally injective by
  `universallyInjective_of_left_inverse`.  Its tensor kernels are zero, so
  composing it does not change either domination inclusion.  Return the
  same comparison object for the original map.

  Universe discipline: bundle `D_s` in `ModuleCat.{max v w}` and transport
  the finite direct sum of the `M i` to that carrier before invoking the
  induction; do not try to treat `Type w` and `Type (max v w)` as
  definitionally equal.
  -/
  sorry

/-- Flat Mittag--Leffler modules over a Mittag--Leffler ring module remain
    Mittag--Leffler after restriction of scalars (Lemma 89.10). -/
theorem flat_mittagLeffler_of_mittagLeffler_restrictScalars
    {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    (f : R →+* S) (M : ModuleCat.{w} S)
    (hS : IsMittagLefflerModule
      ((ModuleCat.restrictScalars f).obj (ModuleCat.of S S)))
    (hflat : Module.Flat S (M : Type w))
    (hM : IsMittagLefflerModule M) :
    IsMittagLefflerModule ((ModuleCat.restrictScalars f).obj M) := by
  /-
  Proof roadmap (Stacks Project, Lemma 10.89.11).

  * Install `letI : Algebra R S := f.toAlgebra`, the restricted
    `Module R (M : Type w) := Module.compHom _ f`, and
    `IsScalarTower R S M := IsScalarTower.of_compHom R S M`.  Apply the
    injectivity criterion `mittagLeffler_tensor_iff` to the restricted
    module and fix an R-module family `Q`.
  * Apply the R-criterion to `hS` to get injectivity of
    `S tensor[R] (forall a, Q a) -> forall a, S tensor[R] Q a`.  Bundle the
    same function as an S-linear map (prove `map_smul'` on pure tensors using
    `TensorProduct.smul_tmul'`).  Tensor it on the left by `M`; its
    injectivity follows from `hflat` via
    `Module.Flat.lTensor_preserves_injective_linearMap`.
  * Put `SQ a := ModuleCat.of S (S tensor[R] (Q a : _))`.  The S-criterion
    applied to `hM` makes `productTensorMap M SQ` injective.  Thus the
    composite
      `M tensor[S] (S tensor[R] product Q)`
      ` -> M tensor[S] product (S tensor[R] Q a)`
      ` -> product (M tensor[S] (S tensor[R] Q a))`
    is injective.
  * Conjugate its source and every target coordinate with
    `TensorProduct.AlgebraTensorModule.cancelBaseChange R S S M _`, restricted
    to R-scalars.  These give respectively
    `M tensor[R] product Q` and `M tensor[R] Q a`.  Prove on pure tensors,
    using `cancelBaseChange_tmul`/`cancelBaseChange_symm_tmul` and
    `productTensorMap_tmul`, that the conjugated composite is exactly the
    R-linear `productTensorMap` for `((ModuleCat.restrictScalars f).obj M)`.
    Its injectivity is the required criterion.  Raise `Q`, `SQ`, and `M`
    together with `ULift.moduleEquiv` when applying the three criterion
    instances so that their explicit universes agree.
  -/
  sorry

end

end Formalization.Books.Algebra.Unit89
