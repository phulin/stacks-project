import Formalization.Books.Algebra.Unit71.ExtGroups
import Mathlib.Data.Rat.Defs
import Mathlib.Data.ZMod.Basic

/-!
# Exercises, Chapter 11: Ext groups of abelian groups

The source asks for four computations in `Mod_ℤ`.  The canonical Ext group is
the `ExtGroup` interface from Algebra, Chapter 71.  Finite cyclic groups are
represented by `ZMod`, and `ℚ/ℤ` is represented by the canonical additive-group
quotient by the integer multiples of `1`.
-/

namespace Formalization.Books.Exercises.Unit11

open Formalization.Books.Algebra.Unit71

/-! ## The four modules in the source exercise -/

abbrev integerModule : ModuleCat ℤ := ModuleCat.of ℤ ℤ

abbrev integerModFourModule : ModuleCat ℤ := ModuleCat.of ℤ (ZMod 4)

abbrev integerModEightModule : ModuleCat ℤ := ModuleCat.of ℤ (ZMod 8)

abbrev rationalModule : ModuleCat ℤ := ModuleCat.of ℤ ℚ

abbrev modTwoModule : ModuleCat ℤ := ModuleCat.of ℤ (ZMod 2)

/-- The additive group `ℚ/ℤ` used in the fourth case. -/
abbrev rationalModInteger : Type := ℚ ⧸ AddSubgroup.zmultiples (1 : ℚ)

abbrev rationalModIntegerModule : ModuleCat ℤ :=
  ModuleCat.of ℤ rationalModInteger

/-! ## The Ext computations -/

/-- `Ext^0_ℤ(ℤ, ℤ)` is `ℤ`, while all positive Ext groups vanish. -/
theorem ext_integer_integer_degree_zero :
    Nonempty (ExtGroup integerModule integerModule 0 ≃+ ℤ) := by
  let evalOne : (ℤ →ₗ[ℤ] ℤ) →+ ℤ :=
    { toFun := fun f => f 1
      map_zero' := by simp
      map_add' := by intro f g; simp }
  have heval : Function.Bijective evalOne := by
    constructor
    · intro f g h
      apply LinearMap.ext
      intro x
      have h' : f 1 = g 1 := by simpa [evalOne] using h
      calc
        f x = f (x • (1 : ℤ)) := by simp
        _ = x • f 1 := by rw [map_smul]
        _ = x • g 1 := by rw [h']
        _ = g (x • (1 : ℤ)) := by rw [map_smul]
        _ = g x := by simp
    · intro z
      refine ⟨LinearMap.lsmul ℤ ℤ z, ?_⟩
      change (LinearMap.lsmul ℤ ℤ z) 1 = z
      simp [LinearMap.lsmul_apply]
  let eLin : (ℤ →ₗ[ℤ] ℤ) ≃+ ℤ := AddEquiv.ofBijective evalOne heval
  exact ⟨CategoryTheory.Abelian.Ext.addEquiv₀.trans
    (ModuleCat.homAddEquiv.trans eLin)⟩

theorem ext_integer_integer_positive_vanishes {i : ℕ} (hi : 0 < i) :
    Nonempty (ExtGroup integerModule integerModule i ≃+ (Fin 0 → ℤ)) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hi)
  letI : Subsingleton (ExtGroup integerModule integerModule (n + 1)) :=
    CategoryTheory.Abelian.Ext.subsingleton_of_projective integerModule integerModule n
  letI : Unique (ExtGroup integerModule integerModule (n + 1)) :=
    { default := 0
      uniq := fun _ => Subsingleton.elim _ _ }
  exact ⟨AddEquiv.ofUnique⟩

/-- For the pair `(ℤ/4, ℤ/8)`, both `Ext^0` and `Ext^1` are `ℤ/4`, and
all higher Ext groups vanish. -/
theorem ext_mod_four_mod_eight_degree_zero :
    Nonempty (ExtGroup integerModFourModule integerModEightModule 0 ≃+ ZMod 4) := by
  let fbase : ℤ →+ ZMod 8 :=
    (AddMonoidHom.mulRight (2 : ZMod 8)).comp (Int.castAddHom (ZMod 8))
  have hfbase : fbase 4 = 0 := by
    change ((4 : ZMod 8) * 2) = 0
    calc
      (4 : ZMod 8) * 2 = (8 : ZMod 8) := by norm_num
      _ = 0 := ZMod.natCast_self 8
  let u : ZMod 4 →+ ZMod 8 := ZMod.lift 4 ⟨fbase, hfbase⟩
  have hu : Function.Injective u := by
    apply (ZMod.lift_injective (f := ⟨fbase, hfbase⟩)).2
    intro m hm
    have hm' : (8 : ℤ) ∣ m * 2 := by
      apply (ZMod.intCast_zmod_eq_zero_iff_dvd (m * 2) 8).mp
      simpa [fbase, AddMonoidHom.mulRight_apply] using hm
    rcases hm' with ⟨k, hk⟩
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd m 4).2
    refine ⟨k, ?_⟩
    ring_nf at hk ⊢
    omega
  have hu4 : (4 : ℤ) • u = 0 := by
    ext x
    obtain ⟨m, rfl⟩ := ZMod.intCast_surjective x
    change (4 : ℤ) • u (m : ZMod 4) = 0
    rw [show u (m : ZMod 4) = fbase m by simp [u, ZMod.lift_coe]]
    change (4 : ℤ) • ((m : ZMod 8) * 2) = 0
    rw [← Int.cast_smul_eq_zsmul (ZMod 8), smul_eq_mul]
    calc
      (4 : ZMod 8) * ((m : ZMod 8) * 2) =
          ((4 : ZMod 8) * 2) * (m : ZMod 8) := by ring
      _ = 0 := by
        rw [show (4 : ZMod 8) * 2 = 0 by
          calc
            (4 : ZMod 8) * 2 = (8 : ZMod 8) := by norm_num
            _ = 0 := ZMod.natCast_self 8]
        simp
  let f : ℤ →+ (ZMod 4 →+ ZMod 8) :=
    { toFun := fun m => m • u
      map_zero' := by simp
      map_add' := by intro m n; simp [add_smul] }
  have hf : f 4 = 0 := by simpa [f] using hu4
  let v : ZMod 4 →+ (ZMod 4 →+ ZMod 8) := ZMod.lift 4 ⟨f, hf⟩
  have hv_one (a : ZMod 4) : v a 1 = u a := by
    obtain ⟨m, rfl⟩ := ZMod.intCast_surjective a
    simp only [v, ZMod.lift_coe, f]
    simpa using (u.map_zsmul m (1 : ZMod 4)).symm
  have hv : Function.Bijective v := by
    constructor
    · intro a b hab
      apply hu
      rw [← hv_one a, ← hv_one b]
      exact congrArg (fun q : ZMod 4 →+ ZMod 8 => q 1) hab
    · intro h
      obtain ⟨n, hn⟩ := ZMod.intCast_surjective (h 1)
      have h4 : (4 : ℤ) • (n : ZMod 8) = 0 := by
        calc
          (4 : ℤ) • (n : ZMod 8) = (4 : ℤ) • h 1 := by rw [hn]
          _ = h ((4 : ℤ) • (1 : ZMod 4)) := (h.map_zsmul 4 1).symm
          _ = 0 := by
            have hfour : (4 : ℤ) • (1 : ZMod 4) = 0 := by
              rw [← Int.cast_smul_eq_zsmul (ZMod 4), smul_eq_mul, mul_one,
                (ZMod.intCast_zmod_eq_zero_iff_dvd (4 : ℤ) 4).2]
              exact ⟨1, by norm_num⟩
            rw [hfour, h.map_zero]
      have hn8 : (8 : ℤ) ∣ 4 * n := by
        apply (ZMod.intCast_zmod_eq_zero_iff_dvd (4 * n) 8).mp
        simpa [smul_eq_mul] using h4
      rcases hn8 with ⟨k, hk⟩
      refine ⟨(k : ZMod 4), ?_⟩
      have hkn : n = 2 * k := by
        ring_nf at hk
        omega
      have hvk : v (k : ZMod 4) 1 = h 1 := by
        rw [hv_one]
        rw [← hn]
        simpa [u, fbase, AddMonoidHom.mulRight_apply, hkn, mul_comm]
      apply AddMonoidHom.ext
      intro x
      obtain ⟨m, rfl⟩ := ZMod.intCast_surjective x
      calc
        v (k : ZMod 4) (m : ZMod 4) = m • v (k : ZMod 4) 1 := by
          simpa using (v (k : ZMod 4)).map_zsmul m (1 : ZMod 4)
        _ = m • h 1 := by rw [hvk]
        _ = h (m : ZMod 4) := by
          simpa using (h.map_zsmul m (1 : ZMod 4)).symm
  let eHom : (ZMod 4 →+ ZMod 8) ≃+ ZMod 4 :=
    (AddEquiv.ofBijective v hv).symm
  exact ⟨CategoryTheory.Abelian.Ext.addEquiv₀.trans
    ((ModuleCat.homAddEquiv.trans
      (addMonoidHomLequivInt ℤ).symm.toAddEquiv).trans eHom)⟩

theorem ext_mod_four_mod_eight_degree_one :
    Nonempty (ExtGroup integerModFourModule integerModEightModule 1 ≃+ ZMod 4) := by
  let f : ℤ →ₗ[ℤ] ℤ := LinearMap.lsmul ℤ ℤ 4
  let g : ℤ →ₗ[ℤ] ZMod 4 :=
    { toFun := fun x => (x : ZMod 4)
      map_add' := by intro x y; simp
      map_smul' := by intro c x; simp [smul_eq_mul] }
  let S : CategoryTheory.ShortComplex (ModuleCat ℤ) :=
    ModuleCat.shortComplexOfCompEqZero f g (by
      apply LinearMap.ext
      intro x
      change ((4 * x : ℤ) : ZMod 4) = 0
      rw [Int.cast_mul]
      rw [show ((4 : ℤ) : ZMod 4) = 0 by
        apply (ZMod.intCast_zmod_eq_zero_iff_dvd (4 : ℤ) 4).2
        exact ⟨1, by norm_num⟩]
      simp)
  have hex : Function.Exact f g := by
    intro y
    constructor
    · intro hy
      have hy' : (4 : ℤ) ∣ y := by
        apply (ZMod.intCast_zmod_eq_zero_iff_dvd y 4).mp
        simpa [g] using hy
      rcases hy' with ⟨x, rfl⟩
      refine ⟨x, ?_⟩
      simp [f]
    · rintro ⟨x, rfl⟩
      change ((4 * x : ℤ) : ZMod 4) = 0
      rw [Int.cast_mul]
      rw [show ((4 : ℤ) : ZMod 4) = 0 by
        apply (ZMod.intCast_zmod_eq_zero_iff_dvd (4 : ℤ) 4).2
        exact ⟨1, by norm_num⟩]
      simp
  have hinj : Function.Injective f := by
    intro x y hxy
    have : (4 : ℤ) * x = 4 * y := by simpa [f] using hxy
    omega
  have hsurj : Function.Surjective g := by
    intro z
    obtain ⟨n, rfl⟩ := ZMod.intCast_surjective z
    exact ⟨n, by simp [g]⟩
  have hS : S.ShortExact := ModuleCat.shortComplex_shortExact S hex hinj hsurj
  let evalEight : (ℤ →ₗ[ℤ] ZMod 8) →+ ZMod 8 :=
    { toFun := fun h => h 1
      map_zero' := by simp
      map_add' := by intro h k; simp }
  have hevalEight : Function.Bijective evalEight := by
    constructor
    · intro h k heq
      apply LinearMap.ext
      intro x
      have heq' : h 1 = k 1 := by simpa [evalEight] using heq
      calc
        h x = h (x • (1 : ℤ)) := by simp
        _ = x • h 1 := by rw [map_smul]
        _ = x • k 1 := by rw [heq']
        _ = k (x • (1 : ℤ)) := by rw [map_smul]
        _ = k x := by simp
    · intro z
      let h : ℤ →ₗ[ℤ] ZMod 8 :=
        { toFun := fun x => x • z
          map_add' := by intro x y; simp [add_smul]
          map_smul' := by intro x y; simp [smul_eq_mul, mul_assoc] }
      refine ⟨h, ?_⟩
      change (1 : ℤ) • z = z
      simp [LinearMap.lsmul_apply]
  let e0 : ExtGroup integerModule integerModEightModule 0 ≃+ ZMod 8 :=
    CategoryTheory.Abelian.Ext.addEquiv₀.trans
      (ModuleCat.homAddEquiv.trans (AddEquiv.ofBijective evalEight hevalEight))
  let d : ZMod 8 →+* ZMod 4 := ZMod.castHom (show 4 ∣ 8 by norm_num) (ZMod 4)
  let c : ZMod 8 →+ ZMod 4 := d.toAddMonoidHom
  let q : ExtGroup integerModule integerModEightModule 0 →+ ZMod 4 :=
    c.comp e0.toAddMonoidHom
  have hqsurj : Function.Surjective q := by
    intro z
    obtain ⟨z, rfl⟩ := ZMod.intCast_surjective z
    refine ⟨e0.symm (z : ZMod 8), ?_⟩
    simp [q, c]
  let α : ExtGroup S.X₁ integerModEightModule 0 →+
      ExtGroup S.X₃ integerModEightModule 1 :=
    hS.extClass.precomp integerModEightModule (by simp)
  let β : ExtGroup S.X₂ integerModEightModule 0 →+
      ExtGroup S.X₁ integerModEightModule 0 :=
    (CategoryTheory.Abelian.Ext.mk₀ S.f).precomp integerModEightModule (by simp)
  have hαsurj : Function.Surjective α := by
    intro x
    have hx :
        (CategoryTheory.Abelian.Ext.mk₀ S.g).comp x (Nat.zero_add 1) = 0 := by
      exact CategoryTheory.Abelian.Ext.eq_zero_of_projective _
    obtain ⟨y, hy⟩ :=
      CategoryTheory.Abelian.Ext.contravariant_sequence_exact₃ hS
        (n₀ := 0) integerModEightModule x hx (by simp)
    exact ⟨y, by simpa [α] using hy⟩
  have hβ (z : ExtGroup S.X₂ integerModEightModule 0) :
      e0 (β z) = (4 : ZMod 8) * e0 z := by
    have hpre (w : ExtGroup S.X₂ integerModEightModule 0) :
        ((CategoryTheory.Abelian.Ext.mk₀ S.f).precomp integerModEightModule (by simp)) w =
          (CategoryTheory.Abelian.Ext.mk₀ S.f).comp w (Nat.zero_add 0) := by
      rfl
    dsimp [β]
    rw [hpre]
    rw [← CategoryTheory.Abelian.Ext.mk₀_addEquiv₀_apply z,
      CategoryTheory.Abelian.Ext.mk₀_comp_mk₀]
    dsimp [e0]
    have hright (w : S.X₁ ⟶ integerModEightModule) :
        CategoryTheory.Abelian.Ext.addEquiv₀
            (CategoryTheory.Abelian.Ext.mk₀ w) = w :=
      (CategoryTheory.Abelian.Ext.addEquiv₀).right_inv w
    rw [hright]
    simp [S, β, e0, CategoryTheory.Abelian.Ext.addEquiv₀, f, evalEight,
      ModuleCat.homEquiv, ModuleCat.homAddEquiv, ModuleCat.hom_comp,
      ModuleCat.hom_ofHom, LinearMap.coe_comp, LinearMap.lsmul_apply]
    change (CategoryTheory.Abelian.Ext.homEquiv₀ z) 4 = _
    rw [show (4 : ℤ) = (4 : ℤ) • (1 : ℤ) by simp, map_smul]
    simp [smul_eq_mul]
  let qS : ExtGroup S.X₁ integerModEightModule 0 →+ ZMod 4 := q
  have hqβ (z : ExtGroup S.X₂ integerModEightModule 0) : qS (β z) = 0 := by
    rw [show qS (β z) = c (e0 (β z)) by rfl, hβ]
    change d ((4 : ZMod 8) * e0 z) = 0
    rw [map_mul]
    have hd4 : d (4 : ZMod 8) = 0 := by
      change ((4 : ℤ) : ZMod 4) = 0
      apply (ZMod.intCast_zmod_eq_zero_iff_dvd (4 : ℤ) 4).2
      exact ⟨1, by norm_num⟩
    rw [hd4, zero_mul]
  have hker : AddCon.ker α = AddCon.ker qS := by
    ext x y
    change α x = α y ↔ qS x = qS y
    constructor
    · intro hxy
      have hsub : α (x - y) = 0 := by
        rw [map_sub, sub_eq_zero.mpr hxy]
      obtain ⟨z, hz⟩ :=
        CategoryTheory.Abelian.Ext.contravariant_sequence_exact₁ hS
          (n₀ := 0) (n₁ := 1) integerModEightModule (x - y) (by simp)
            (by simpa [α] using hsub)
      rw [← sub_eq_zero, ← map_sub]
      rw [show x - y = β z by simpa [β] using hz.symm]
      exact hqβ z
    · intro hxy
      have hsub : qS (x - y) = 0 := by
        rw [map_sub, sub_eq_zero.mpr hxy]
      obtain ⟨n, hn⟩ := ZMod.intCast_surjective (e0 (x - y))
      have hcast : d (e0 (x - y)) = 0 := by
        simpa [qS, q, c] using hsub
      have hcastn : d (n : ZMod 8) = 0 := by
        rw [hn]
        exact hcast
      have hn4 : (4 : ℤ) ∣ n := by
        apply (ZMod.intCast_zmod_eq_zero_iff_dvd n 4).mp
        simpa [d] using hcastn
      rcases hn4 with ⟨k, hk⟩
      let z : ExtGroup S.X₂ integerModEightModule 0 := e0.symm (k : ZMod 8)
      have hdiff : x - y = β z := by
        apply e0.injective
        rw [hβ]
        calc
          e0 (x - y) = (n : ZMod 8) := hn.symm
          _ = (4 : ZMod 8) * (k : ZMod 8) := by
            rw [hk, Int.cast_mul]
            norm_num
          _ = 4 * e0 z := by simp [z]
      have hz0 : α (β z) = 0 := by
        simpa [α, β] using
          (CategoryTheory.Abelian.Ext.extClass_comp_assoc hS z (by simp))
      rw [← sub_eq_zero, ← map_sub]
      rw [hdiff]
      exact hz0
  have hqSsurj : Function.Surjective qS := hqsurj
  let eQ : (AddCon.ker α).Quotient ≃+ ZMod 4 :=
    hker ▸ AddCon.quotientKerEquivOfSurjective qS hqSsurj
  let eB : ExtGroup S.X₃ integerModEightModule 1 ≃+ ZMod 4 :=
    (AddCon.quotientKerEquivOfSurjective α hαsurj).symm.trans eQ
  change Nonempty (ExtGroup S.X₃ integerModEightModule 1 ≃+ ZMod 4)
  exact ⟨eB⟩

theorem ext_mod_four_mod_eight_higher_vanishes {i : ℕ} (hi : 2 ≤ i) :
    Nonempty
      (ExtGroup integerModFourModule integerModEightModule i ≃+ (Fin 0 → ZMod 4)) := by
  sorry

/-- All Ext groups from `ℚ` to `ℤ/2` vanish. -/
theorem ext_rational_mod_two_vanishes (i : ℕ) :
    Nonempty (ExtGroup rationalModule modTwoModule i ≃+ (Fin 0 → ZMod 2)) := by
  sorry

/-- For the pair `(ℤ/2, ℚ/ℤ)`, degree zero is `ℤ/2` and all positive
degrees vanish. -/
theorem ext_mod_two_rational_mod_integer_degree_zero :
    Nonempty (ExtGroup modTwoModule rationalModIntegerModule 0 ≃+ ZMod 2) := by
  sorry

theorem ext_mod_two_rational_mod_integer_positive_vanishes {i : ℕ} (hi : 0 < i) :
    Nonempty
      (ExtGroup modTwoModule rationalModIntegerModule i ≃+ (Fin 0 → ZMod 2)) := by
  sorry

end Formalization.Books.Exercises.Unit11
