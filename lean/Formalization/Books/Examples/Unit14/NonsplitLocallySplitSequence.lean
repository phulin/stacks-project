import Mathlib.Algebra.Algebra.Hom
import Mathlib.Algebra.DirectSum.Module
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.Algebra.Category.ModuleCat.Localization
import Mathlib.Algebra.Module.Submodule.Ker
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Prime.Int
import Mathlib.Data.Nat.Prime.Infinite
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.Filtration
import Mathlib.RingTheory.Localization.Submodule

/-!
# Examples, Chapter 14: Nonsplit locally split sequence

This file formalizes the sequence
`0 → M → ⨁ p, ℤ_(p) → ℚ → 0`, where `p` ranges over the prime
integers and `M` is the kernel of the map induced by the inclusions into
`ℚ`.  The sequence, its localization on a principal open, and the general
Zariski-local splitting interface are recorded as theorem statements.
-/

noncomputable section

open scoped DirectSum

namespace Formalization.Books.Examples.Unit14

universe u

/-! ## The prime-indexed sequence -/

/-- The type of positive prime integers indexing the direct sum. -/
abbrev PrimeIndex := Nat.Primes

/- The prime ideal `(p)` of the integers. -/
def primeIdeal (p : PrimeIndex) : Ideal ℤ :=
  Ideal.span ({(p.1 : ℤ)} : Set ℤ)

instance primeIdeal_isPrime (p : PrimeIndex) : (primeIdeal p).IsPrime := by
  simpa [primeIdeal] using
    (Ideal.isPrime_span_singleton_of_prime (Nat.prime_iff_prime_int.mp p.2))

/- The localization `ℤ_(p)` of the integers at the prime ideal `(p)`. -/
abbrev primeLocalizedInteger (p : PrimeIndex) : Type :=
  Localization.AtPrime (primeIdeal p)

/-- The canonical inclusion `ℤ_(p) → ℚ`. -/
noncomputable def primeLocalizedIntegerToRat (p : PrimeIndex) :
    primeLocalizedInteger p →+* ℚ :=
  IsLocalization.lift (M := (primeIdeal p).primeCompl)
    (S := primeLocalizedInteger p) (g := algebraMap ℤ ℚ) (by
      intro s
      have hs : (s : ℤ) ≠ 0 := by
        intro hs
        exact s.2 (hs ▸ (primeIdeal p).zero_mem)
      exact isUnit_iff_ne_zero.mpr (by
        simpa using (Int.cast_ne_zero.mpr hs : ((s : ℤ) : ℚ) ≠ 0)))

/-- The preceding inclusion, viewed as a `ℤ`-linear map. -/
def primeLocalizedIntegerToRatLinearMap (p : PrimeIndex) :
    primeLocalizedInteger p →ₗ[ℤ] ℚ :=
  { toFun := primeLocalizedIntegerToRat p
    map_add' := (primeLocalizedIntegerToRat p).map_add
    map_smul' := by
      intro n x
      simp [Algebra.smul_def, primeLocalizedIntegerToRat] }

/-- The middle term `⨁ₚ ℤ_(p)` in the source sequence. -/
abbrev primeLocalizedIntegerDirectSum : Type :=
  ⨁ p : PrimeIndex, primeLocalizedInteger p

/-- The map from the middle term to `ℚ`, induced componentwise by inclusion. -/
def primeLocalizedIntegerSumToRat :
    primeLocalizedIntegerDirectSum →ₗ[ℤ] ℚ :=
  DirectSum.toModule ℤ PrimeIndex ℚ
    (fun p => primeLocalizedIntegerToRatLinearMap p)

/-- The kernel `M` of the map on the right. -/
abbrev primeLocalizedIntegerKernel : Type :=
  LinearMap.ker primeLocalizedIntegerSumToRat

/-- The inclusion of `M` into the direct sum. -/
def primeLocalizedIntegerKernelInclusion :
    primeLocalizedIntegerKernel →ₗ[ℤ] primeLocalizedIntegerDirectSum :=
  (LinearMap.ker primeLocalizedIntegerSumToRat).subtype

/-- The displayed sequence, as a short complex of `ℤ`-modules. -/
noncomputable def primeLocalizedIntegerShortComplex :
    CategoryTheory.ShortComplex (ModuleCat.{0} ℤ) :=
  primeLocalizedIntegerSumToRat.shortComplexKer

/-- The source's short-exactness assertion for the displayed sequence. -/
theorem primeLocalizedIntegerShortComplex_shortExact :
    (primeLocalizedIntegerShortComplex).ShortExact := by
  apply LinearMap.shortExact_shortComplexKer
  intro q
  rcases Nat.exists_infinite_primes (q.den + 1) with ⟨p, hp, hprime⟩
  have hpd : ¬p ∣ q.den := by
    intro h
    have hle : p ≤ q.den := Nat.le_of_dvd (Nat.pos_of_ne_zero q.den_nz) h
    omega
  let pp : PrimeIndex := ⟨p, hprime⟩
  have hpd' : ¬(p : ℤ) ∣ (q.den : ℤ) := by
    exact fun h => hpd (Int.natCast_dvd_natCast.mp h)
  have hs : (q.den : ℤ) ∈ (primeIdeal pp).primeCompl := by
    change (q.den : ℤ) ∉ Ideal.span {(p : ℤ)}
    simpa [Ideal.mem_span_singleton] using hpd'
  let x := IsLocalization.mk' (primeLocalizedInteger pp) q.num ⟨q.den, hs⟩
  refine ⟨DirectSum.lof ℤ PrimeIndex (fun p => primeLocalizedInteger p) pp x, ?_⟩
  rw [primeLocalizedIntegerSumToRat, DirectSum.toModule_lof]
  change primeLocalizedIntegerToRat pp x = q
  dsimp [x]
  rw [primeLocalizedIntegerToRat, IsLocalization.lift_mk'_spec]
  change (q.num : ℚ) = (q.den : ℚ) * q
  have hden : (q.den : ℚ) ≠ 0 := by exact_mod_cast q.den_nz
  have hq : q = (q.num : ℚ) / q.den := by
    simpa [Rat.divInt_eq_div] using q.num_divInt_den.symm
  calc
    (q.num : ℚ) = (q.num : ℚ) / q.den * q.den :=
      (div_mul_cancel₀ _ hden).symm
    _ = q.den * ((q.num : ℚ) / q.den) := by ring
    _ = q.den * q :=
      (congrArg (fun z : ℚ => (q.den : ℚ) * z) hq).symm

/-! ## Nonsplitting and localization -/

/-- There are no nonzero `ℤ`-linear maps `ℚ → ℤ_(p)`. -/
theorem primeLocalizedInteger_no_nonzero_hom (p : PrimeIndex)
    (φ : ℚ →ₗ[ℤ] primeLocalizedInteger p) :
    φ = 0 := by
  let I : Ideal (primeLocalizedInteger p) :=
    Ideal.map (algebraMap ℤ (primeLocalizedInteger p)) (primeIdeal p)
  have hI : I ≠ ⊤ := by
    rw [show I = Ideal.map (algebraMap ℤ (primeLocalizedInteger p)) (primeIdeal p) by rfl,
      IsLocalization.AtPrime.map_eq_maximalIdeal]
    exact (IsLocalRing.maximalIdeal.isMaximal _).ne_top
  apply LinearMap.ext
  intro q
  have hmem : φ q ∈ ⨅ n : ℕ, I ^ n := by
    rw [Ideal.mem_iInf]
    intro n
    have hpn : (p.1 : ℚ) ^ n ≠ 0 := by
      exact pow_ne_zero _ (by exact_mod_cast p.2.ne_zero)
    have hq : q = (p.1 : ℤ) ^ n • (q / (p.1 : ℚ) ^ n) := by
      calc
        q = q / (p.1 : ℚ) ^ n * (p.1 : ℚ) ^ n :=
          (div_mul_cancel₀ q hpn).symm
        _ = (p.1 : ℚ) ^ n * (q / (p.1 : ℚ) ^ n) := by ring
        _ = (p.1 : ℤ) ^ n • (q / (p.1 : ℚ) ^ n) := by
          simp [Algebra.smul_def]
    rw [hq, map_smul]
    have hp : algebraMap ℤ (primeLocalizedInteger p) (p.1 : ℤ) ∈ I :=
      Ideal.mem_map_of_mem _ (by
      simp [primeIdeal])
    have hpow : algebraMap ℤ (primeLocalizedInteger p) ((p.1 : ℤ) ^ n) ∈ I ^ n := by
      rw [map_pow]
      exact Ideal.pow_mem_pow hp n
    simpa [Algebra.smul_def, smul_eq_mul] using
      (Ideal.mul_mem_right (φ (q / (p.1 : ℚ) ^ n)) (I ^ n) hpow)
  have hz : φ q ∈ (⊥ : Ideal (primeLocalizedInteger p)) := by
    rw [← Ideal.iInf_pow_eq_bot_of_isLocalRing I hI]
    exact hmem
  simpa using hz

/-- The displayed short-exact sequence is nonsplit. -/
theorem primeLocalizedIntegerShortComplex_not_split :
    ¬ Nonempty primeLocalizedIntegerShortComplex.Splitting := by
  rintro ⟨s⟩
  have hs (p : PrimeIndex) :
      (DirectSum.component ℤ PrimeIndex (fun p => primeLocalizedInteger p) p).comp
          s.s.hom = 0 := by
    exact primeLocalizedInteger_no_nonzero_hom p _
  have hs' : s.s.hom = 0 := by
    apply LinearMap.ext
    intro q
    apply DirectSum.ext_component ℤ
    intro p
    exact LinearMap.congr_fun (hs p) q
  have hid := congrArg ModuleCat.Hom.hom s.s_g
  rw [ModuleCat.hom_comp, hs'] at hid
  simp at hid
  change (0 : ℚ →ₗ[ℤ] ℚ) = LinearMap.id at hid
  have hzero : (0 : ℚ) = 1 := LinearMap.congr_fun hid 1
  norm_num at hzero

/- The localization of the displayed sequence on the principal open `D(p)`,
   obtained by inverting `p`. -/
def primeLocalizedIntegerShortComplexAt (p : PrimeIndex) :
    CategoryTheory.ShortComplex
      (ModuleCat.{0} (Localization (Submonoid.powers (p.1 : ℤ)))) :=
  primeLocalizedIntegerShortComplex.map
    (ModuleCat.localizedModuleFunctor
      (Submonoid.powers (p.1 : ℤ)))

/-- Localization preserves the short-exactness of the displayed sequence. -/
theorem primeLocalizedIntegerShortComplexAt_shortExact (p : PrimeIndex) :
  (primeLocalizedIntegerShortComplexAt p).ShortExact := by
  exact primeLocalizedIntegerShortComplex_shortExact.map_of_exact
    (ModuleCat.localizedModuleFunctor (Submonoid.powers (p.1 : ℤ)))

private theorem primeLocalizedIntegerToRatLinearMap_isLocalizedModule (p : PrimeIndex) :
    IsLocalizedModule (Submonoid.powers (p.1 : ℤ))
      (primeLocalizedIntegerToRatLinearMap p) := by
  refine { map_units := ?_, surj := ?_, exists_of_eq := ?_ }
  · intro s
    rw [Module.End.isUnit_iff]
    have hs : (s : ℤ) ≠ 0 := by
      rcases (Submonoid.mem_powers_iff _ _).mp s.2 with ⟨n, hn⟩
      rw [← hn]
      exact pow_ne_zero _ (by exact_mod_cast p.2.ne_zero)
    have hbij : Function.Bijective (fun x : ℚ => (s : ℤ) • x) := by
      constructor
      · intro a b h
        apply mul_left_cancel₀ (Int.cast_ne_zero.mpr hs)
        simpa [Algebra.smul_def] using h
      · intro a
        refine ⟨(s : ℚ)⁻¹ * a, ?_⟩
        simp [Algebra.smul_def, Int.cast_ne_zero.mpr hs]
    change Function.Bijective (fun x : ℚ => (s : ℤ) • x)
    exact hbij
  · intro q
    rcases Nat.exists_eq_pow_mul_and_not_dvd q.den_nz p.1 p.2.ne_one with ⟨e, m, hm, hden⟩
    have hmd : ¬(p.1 : ℤ) ∣ (m : ℤ) := by
      exact fun h => hm (Int.natCast_dvd_natCast.mp h)
    have hm' : (m : ℤ) ∈ (primeIdeal p).primeCompl := by
      change (m : ℤ) ∉ Ideal.span {(p.1 : ℤ)}
      simpa [Ideal.mem_span_singleton] using hmd
    let x := IsLocalization.mk' (primeLocalizedInteger p) q.num ⟨(m : ℤ), hm'⟩
    let s : Submonoid.powers (p.1 : ℤ) :=
      ⟨(p.1 : ℤ) ^ e, (Submonoid.mem_powers_iff _ _).2 ⟨e, rfl⟩⟩
    refine ⟨⟨x, s⟩, ?_⟩
    change (p.1 : ℤ) ^ e • q = primeLocalizedIntegerToRatLinearMap p x
    change (p.1 : ℤ) ^ e • q = primeLocalizedIntegerToRat p x
    dsimp [x, primeLocalizedIntegerToRat]
    symm
    rw [IsLocalization.lift_mk'_spec]
    change (q.num : ℚ) = (m : ℚ) * ((algebraMap ℤ ℚ) ((p.1 : ℤ) ^ e) * q)
    have hq : q = (q.num : ℚ) / q.den := by
      simpa [Rat.divInt_eq_div] using q.num_divInt_den.symm
    have hdenQ : (q.den : ℚ) = (p.1 : ℚ) ^ e * (m : ℚ) := by
      exact_mod_cast hden
    have hdenQ' : (q.den : ℚ) = (algebraMap ℤ ℚ) ((p.1 : ℤ) ^ e) * (m : ℚ) := by
      rw [map_pow]
      norm_num
      exact_mod_cast hden
    have hden_ne : (q.den : ℚ) ≠ 0 := by
      exact_mod_cast q.den_nz
    have hnum : (q.num : ℚ) = q * (q.den : ℚ) := by
      calc
        (q.num : ℚ) = (q.num : ℚ) / q.den * q.den :=
          (div_mul_cancel₀ _ hden_ne).symm
        _ = q * q.den := by rw [← hq]
    calc
      (q.num : ℚ) = q * (q.den : ℚ) := hnum
      _ = q * ((algebraMap ℤ ℚ) ((p.1 : ℤ) ^ e) * (m : ℚ)) := by rw [hdenQ']
      _ = (m : ℚ) * ((algebraMap ℤ ℚ) ((p.1 : ℤ) ^ e) * q) := by ring
  · intro x y hxy
    have hinj : Function.Injective (primeLocalizedIntegerToRat p) := by
      rw [primeLocalizedIntegerToRat, IsLocalization.lift_injective_iff]
      intro a b
      constructor
      · intro h
        exact_mod_cast h
      · intro h
        exact_mod_cast h
    exact ⟨1, by simpa [hinj hxy]⟩

/-- After inverting every prime `p`, the localized sequence is split. -/
theorem primeLocalizedIntegerShortComplexAt_split (p : PrimeIndex) :
    Nonempty (primeLocalizedIntegerShortComplexAt p).Splitting := by
  let S := Submonoid.powers (p.1 : ℤ)
  letI : Module ℤ (LocalizedModule S (primeLocalizedInteger p)) :=
    OreLocalization.instModuleOfIsScalarTower
  letI : Module ℤ (LocalizedModule S ℚ) :=
    OreLocalization.instModuleOfIsScalarTower
  letI : SMul ℤ (LocalizedModule S ℚ) :=
    (inferInstance : Module ℤ (LocalizedModule S ℚ)).toDistribMulAction.toDistribSMul.toSMul
  letI : MulAction ℤ (LocalizedModule S ℚ) :=
    (inferInstance : Module ℤ (LocalizedModule S ℚ)).toDistribMulAction.toMulAction
  let fA : primeLocalizedInteger p →ₗ[ℤ] LocalizedModule S (primeLocalizedInteger p) :=
    LocalizedModule.mkLinearMap S (primeLocalizedInteger p)
  let fQ : ℚ →ₗ[ℤ] LocalizedModule S ℚ :=
    LocalizedModule.mkLinearMap S ℚ
  let l := primeLocalizedIntegerToRatLinearMap p
  letI : IsLocalizedModule S l :=
    primeLocalizedIntegerToRatLinearMap_isLocalizedModule p
  have hcomp : IsLocalizedModule S (fQ.comp l) := by
    refine { map_units := IsLocalizedModule.map_units fQ, surj := ?_, exists_of_eq := ?_ }
    · intro y
      obtain ⟨⟨q, s⟩, hy⟩ := IsLocalizedModule.surj S fQ y
      obtain ⟨⟨a, t⟩, hq⟩ := IsLocalizedModule.surj S l q
      have hy' : s • y = fQ q := by simpa using hy
      have hq' : t • q = l a := by simpa using hq
      refine ⟨⟨a, t * s⟩, ?_⟩
      have hmain : (t * s : S) • y = fQ (l a) := by
        calc
          (t * s : S) • y = t • (s • y) := by
            simpa only [Submonoid.smul_def, Submonoid.coe_mul] using
              (mul_smul (↑t : ℤ) (↑s : ℤ) y)
          _ = t • fQ q := by rw [hy']
          _ = fQ (t • q) := (fQ.map_smul_of_tower t q).symm
          _ = fQ (l a) := by rw [hq']
      simpa only [LinearMap.comp_apply] using hmain
    · intro x y hxy
      obtain ⟨c, hc⟩ := (IsLocalizedModule.eq_iff_exists S fQ).mp hxy
      have hxy' : l x = l y := (IsLocalizedModule.smul_injective l c) hc
      exact (IsLocalizedModule.eq_iff_exists S l).mp hxy'
  let e₀ :=
    IsLocalizedModule.linearEquiv S fA (fQ.comp l)
  let e : LocalizedModule S (primeLocalizedInteger p) ≃ₗ[Localization S]
      LocalizedModule S ℚ :=
    e₀.extendScalarsOfIsLocalization S (Localization S)
  let e' : (ModuleCat.of ℤ (primeLocalizedInteger p)).localizedModule S ≃ₗ[Localization S]
      (ModuleCat.of ℤ ℚ).localizedModule S :=
    (Shrink.linearEquiv (Localization S) (LocalizedModule S (primeLocalizedInteger p))).trans
      (e.trans (Shrink.linearEquiv (Localization S) (LocalizedModule S ℚ)).symm)
  let gLoc := IsLocalizedModule.map S fA fQ l
  letI : IsLocalizedModule S (fQ.comp l) := hcomp
  have he₀ : e₀.toLinearMap = gLoc := by
    apply IsLocalizedModule.linearMap_ext (S := S) (f := fA) (f' := fQ.comp l)
    ext a
    simp [e₀, gLoc]
  have he : e.toLinearMap =
      gLoc.extendScalarsOfIsLocalization S (Localization S) := by
    dsimp [e]
    ext a
    exact LinearMap.congr_fun he₀ a
  have hgLoc : IsLocalizedModule S gLoc := by
    refine { map_units := IsLocalizedModule.map_units fQ, surj := ?_, exists_of_eq := ?_ }
    · intro y
      refine ⟨⟨e₀.symm y, 1⟩, ?_⟩
      change 1 • y = gLoc (e₀.symm y)
      rw [one_smul, ← he₀]
      simp
    · intro x y hxy
      refine ⟨1, ?_⟩
      rw [← he₀] at hxy
      have hxy' : x = y := e₀.injective hxy
      simpa [hxy']
  letI : IsLocalizedModule S gLoc := hgLoc
  let j : (ModuleCat.of ℤ (primeLocalizedInteger p)).localizedModule S ⟶
      (ModuleCat.of ℤ ℚ).localizedModule S :=
    e'.toModuleIso.hom
  letI : CategoryTheory.IsIso j := by
    dsimp [j]
    infer_instance
  let i : (ModuleCat.of ℤ (primeLocalizedInteger p)).localizedModule S ⟶
      (ModuleCat.of ℤ primeLocalizedIntegerDirectSum).localizedModule S :=
    (ModuleCat.localizedModuleFunctor S).map
      (ModuleCat.ofHom (DirectSum.lof ℤ PrimeIndex
        (fun p => primeLocalizedInteger p) p))
  let sec : (ModuleCat.of ℤ ℚ).localizedModule S ⟶
      (ModuleCat.of ℤ primeLocalizedIntegerDirectSum).localizedModule S :=
    CategoryTheory.CategoryStruct.comp (CategoryTheory.asIso j).inv i
  have hmap :
      CategoryTheory.CategoryStruct.comp i
          (primeLocalizedIntegerShortComplexAt p).g = j := by
    dsimp [i, primeLocalizedIntegerShortComplexAt]
    change CategoryTheory.CategoryStruct.comp
        ((ModuleCat.localizedModuleFunctor S).map
          (ModuleCat.ofHom (DirectSum.lof ℤ PrimeIndex
            (fun p => primeLocalizedInteger p) p)))
        ((ModuleCat.localizedModuleFunctor S).map
          (ModuleCat.ofHom primeLocalizedIntegerSumToRat)) = j
    rw [← (ModuleCat.localizedModuleFunctor S).map_comp]
    apply ModuleCat.hom_ext
    ext x
    letI : Module ℤ ((ModuleCat.of ℤ (primeLocalizedInteger p)).localizedModule S) :=
      (ModuleCat.of ℤ (primeLocalizedInteger p)).instModuleCarrierLocalizationLocalizedModule S
    letI : Module ℤ ((ModuleCat.of ℤ ℚ).localizedModule S) :=
      (ModuleCat.of ℤ ℚ).instModuleCarrierLocalizationLocalizedModule S
    let fA' := (ModuleCat.of ℤ (primeLocalizedInteger p)).localizedModuleMkLinearMap S
    let fQ' := (ModuleCat.of ℤ ℚ).localizedModuleMkLinearMap S
    let eAℤ : LocalizedModule S (primeLocalizedInteger p) ≃ₗ[ℤ]
        (ModuleCat.of ℤ (primeLocalizedInteger p)).localizedModule S :=
      (Shrink.linearEquiv ℤ (LocalizedModule S (primeLocalizedInteger p))).symm
    let eQℤ : LocalizedModule S ℚ ≃ₗ[ℤ] (ModuleCat.of ℤ ℚ).localizedModule S :=
      (Shrink.linearEquiv ℤ (LocalizedModule S ℚ)).symm
    letI : IsLocalizedModule S fA' := by
      dsimp [fA']
      exact ModuleCat.localizedModule_isLocalizedModule
        (ModuleCat.of ℤ (primeLocalizedInteger p)) S
    letI : IsLocalizedModule S fQ' := by
      dsimp [fQ']
      exact ModuleCat.localizedModule_isLocalizedModule (ModuleCat.of ℤ ℚ) S
    have hIsoA (z : LocalizedModule S (primeLocalizedInteger p)) :
        IsLocalizedModule.iso S fA' z =
          eAℤ z := by
      have hIsoA' :
          (IsLocalizedModule.iso S fA').toLinearMap = eAℤ.toLinearMap := by
        apply IsLocalizedModule.linearMap_ext
          (S := S) (f := LocalizedModule.mkLinearMap S (primeLocalizedInteger p)) fA'
        ext a
        change IsLocalizedModule.iso S fA' (LocalizedModule.mk a 1) =
          eAℤ (LocalizedModule.mk a 1)
        rw [IsLocalizedModule.iso_mk_one]
        rfl
      exact LinearMap.congr_fun hIsoA' z
    have hIsoQ (z : LocalizedModule S ℚ) :
        IsLocalizedModule.iso S fQ' z =
          eQℤ z := by
      have hIsoQ' :
          (IsLocalizedModule.iso S fQ').toLinearMap = eQℤ.toLinearMap := by
        apply IsLocalizedModule.linearMap_ext
          (S := S) (f := LocalizedModule.mkLinearMap S ℚ) fQ'
        ext a
        change IsLocalizedModule.iso S fQ' (LocalizedModule.mk a 1) =
          eQℤ (LocalizedModule.mk a 1)
        rw [IsLocalizedModule.iso_mk_one]
        rfl
      exact LinearMap.congr_fun hIsoQ' z
    have hlcomp :
        primeLocalizedIntegerSumToRat.comp
            (DirectSum.lof ℤ PrimeIndex
              (fun p => primeLocalizedInteger p) p) = l := by
      ext a
      simp only [LinearMap.comp_apply, primeLocalizedIntegerSumToRat,
        DirectSum.toModule_lof]
      rfl
    have hcomm :
        IsLocalizedModule.map S fA' fQ'
            (primeLocalizedIntegerSumToRat.comp
              (DirectSum.lof ℤ PrimeIndex
                (fun p => primeLocalizedInteger p) p)) ∘ₗ
            IsLocalizedModule.iso S fA' =
          IsLocalizedModule.iso S fQ' ∘ₗ
            IsLocalizedModule.map S (LocalizedModule.mkLinearMap S
              (primeLocalizedInteger p)) (LocalizedModule.mkLinearMap S ℚ)
              (primeLocalizedIntegerSumToRat.comp
                (DirectSum.lof ℤ PrimeIndex
                  (fun p => primeLocalizedInteger p) p)) := by
      exact IsLocalizedModule.map_iso_commute
        (S := S) (f₀ := fA') (f₁ := fQ')
        (primeLocalizedIntegerSumToRat.comp
          (DirectSum.lof ℤ PrimeIndex
            (fun p => primeLocalizedInteger p) p))
    change IsLocalizedModule.mapExtendScalars S fA' fQ' (Localization S)
        (primeLocalizedIntegerSumToRat.comp
          (DirectSum.lof ℤ PrimeIndex
            (fun p => primeLocalizedInteger p) p)) x =
      e' x
    let y := eAℤ.symm x
    have hy : IsLocalizedModule.iso S fA' y = x := by
      rw [hIsoA]
      simpa [y] using eAℤ.apply_symm_apply x
    have he_fun (z : LocalizedModule S (primeLocalizedInteger p)) :
        e z = gLoc z :=
      LinearMap.congr_fun he z
    calc
      IsLocalizedModule.mapExtendScalars S fA' fQ' (Localization S)
          (primeLocalizedIntegerSumToRat.comp
            (DirectSum.lof ℤ PrimeIndex
              (fun p => primeLocalizedInteger p) p)) x =
          IsLocalizedModule.mapExtendScalars S fA' fQ' (Localization S)
            (primeLocalizedIntegerSumToRat.comp
              (DirectSum.lof ℤ PrimeIndex
                (fun p => primeLocalizedInteger p) p))
            (IsLocalizedModule.iso S fA' y) := by rw [hy]
      _ = IsLocalizedModule.map S fA' fQ'
            (primeLocalizedIntegerSumToRat.comp
              (DirectSum.lof ℤ PrimeIndex
                (fun p => primeLocalizedInteger p) p))
            (IsLocalizedModule.iso S fA' y) := by rfl
      _ = IsLocalizedModule.iso S fQ'
            (IsLocalizedModule.map S (LocalizedModule.mkLinearMap S
              (primeLocalizedInteger p)) (LocalizedModule.mkLinearMap S ℚ)
              (primeLocalizedIntegerSumToRat.comp
                (DirectSum.lof ℤ PrimeIndex
              (fun p => primeLocalizedInteger p) p)) y) := by
        change
          ((IsLocalizedModule.map S fA' fQ'
              (primeLocalizedIntegerSumToRat.comp
                (DirectSum.lof ℤ PrimeIndex
                  (fun p => primeLocalizedInteger p) p))).comp
            (IsLocalizedModule.iso S fA').toLinearMap) y =
          ((IsLocalizedModule.iso S fQ').toLinearMap.comp
            (IsLocalizedModule.map S (LocalizedModule.mkLinearMap S
              (primeLocalizedInteger p)) (LocalizedModule.mkLinearMap S ℚ)
              (primeLocalizedIntegerSumToRat.comp
                (DirectSum.lof ℤ PrimeIndex
                  (fun p => primeLocalizedInteger p) p)))) y
        exact LinearMap.congr_fun hcomm y
      _ = eQℤ (gLoc y) := by
        rw [hIsoQ, hlcomp]
      _ = eQℤ (e y) := by
        rw [he_fun]
      _ = e' x := by
        change
          (Shrink.linearEquiv ℤ (LocalizedModule S ℚ)).symm
              (e ((Shrink.linearEquiv ℤ
                (LocalizedModule S (primeLocalizedInteger p))) x)) =
            (Shrink.linearEquiv (Localization S)
              (LocalizedModule S ℚ)).symm
              (e ((Shrink.linearEquiv (Localization S)
                (LocalizedModule S (primeLocalizedInteger p))) x))
        rfl
  have hsec : CategoryTheory.CategoryStruct.comp sec (primeLocalizedIntegerShortComplexAt p).g =
      CategoryTheory.CategoryStruct.id _ := by
    let g' := (primeLocalizedIntegerShortComplexAt p).g
    have hmap' : CategoryTheory.CategoryStruct.comp i g' = j := by
      exact hmap
    apply (CategoryTheory.cancel_epi j).1
    dsimp [sec]
    change CategoryTheory.CategoryStruct.comp j
        (CategoryTheory.CategoryStruct.comp
          (CategoryTheory.CategoryStruct.comp (CategoryTheory.inv j) i) g') =
      CategoryTheory.CategoryStruct.comp j (CategoryTheory.CategoryStruct.id _)
    rw [CategoryTheory.Category.assoc (CategoryTheory.inv j) i g']
    rw [hmap']
    exact CategoryTheory.IsIso.hom_inv_id_assoc j j
  exact ⟨CategoryTheory.ShortComplex.Splitting.ofExactOfSection
    (primeLocalizedIntegerShortComplexAt p)
    (primeLocalizedIntegerShortComplexAt_shortExact p).exact sec hsec
    (primeLocalizedIntegerShortComplexAt_shortExact p).mono_f⟩

/-! ## The general Zariski-local formulation -/

/-- A short complex becomes split on a principal-open Zariski cover. -/
def IsZariskiLocallySplit {R : Type u} [CommRing R]
    (S : CategoryTheory.ShortComplex (ModuleCat.{u} R)) : Prop :=
  ∃ U : Set R, Ideal.span U = ⊤ ∧
    ∀ f ∈ U,
      Nonempty
        (S.map (ModuleCat.localizedModuleFunctor
          (Submonoid.powers f))).Splitting

/-- A nonsplit short-exact sequence which becomes split on a Zariski cover. -/
structure NonsplitZariskiLocallySplitSequence where
  R : Type
  [commRingR : CommRing R]
  S : CategoryTheory.ShortComplex (ModuleCat R)
  shortExact : S.ShortExact
  nonsplit : ¬ Nonempty S.Splitting
  locallySplit : IsZariskiLocallySplit S

/-- There exists a nonsplit short-exact sequence that is split Zariski locally. -/
theorem exists_nonsplit_zariski_locally_split_sequence :
    Nonempty NonsplitZariskiLocallySplitSequence := by
  let U : Set ℤ := Set.range (fun p : PrimeIndex => (p.1 : ℤ))
  have hU : Ideal.span U = ⊤ := by
    rw [Ideal.eq_top_iff_one]
    have h2 : (2 : ℤ) ∈ U := by
      exact ⟨⟨2, by decide⟩, rfl⟩
    have h3 : (3 : ℤ) ∈ U := by
      exact ⟨⟨3, by decide⟩, rfl⟩
    have h2' : (2 : ℤ) ∈ Ideal.span U := Ideal.subset_span h2
    have h3' : (3 : ℤ) ∈ Ideal.span U := Ideal.subset_span h3
    have hcomb : (-1 : ℤ) * 2 + 1 * 3 ∈ Ideal.span U :=
      (Ideal.span U).add_mem
        ((Ideal.span U).mul_mem_left (-1) h2')
        ((Ideal.span U).mul_mem_left 1 h3')
    norm_num at hcomb
    exact hcomb
  refine ⟨{
    R := ℤ
    S := primeLocalizedIntegerShortComplex
    shortExact := primeLocalizedIntegerShortComplex_shortExact
    nonsplit := primeLocalizedIntegerShortComplex_not_split
    locallySplit := ?_ }⟩
  refine ⟨U, hU, ?_⟩
  intro f hf
  rcases (show f ∈ Set.range (fun p : PrimeIndex => (p.1 : ℤ)) by
    simpa [U] using hf) with ⟨p, rfl⟩
  simpa [primeLocalizedIntegerShortComplexAt] using
    primeLocalizedIntegerShortComplexAt_split p

end Formalization.Books.Examples.Unit14
