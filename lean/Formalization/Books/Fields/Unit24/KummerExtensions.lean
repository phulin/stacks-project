import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.FieldTheory.KummerExtension
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.NumberTheory.Cyclotomic.PrimitiveRoots
import Mathlib.NumberTheory.Cyclotomic.Gal
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots

/-!
# Fields, Chapter 24: Kummer extensions

The source's simple extension `K(α)` is Mathlib's canonical
`IntermediateField.adjoin K ({α} : Set L)`.  Roots of unity, primitive roots,
and Galois groups likewise use Mathlib's `rootsOfUnity`, `IsPrimitiveRoot`,
and `Gal` interfaces.
-/

namespace Formalization.Books.Fields.Unit24

noncomputable section

open Polynomial

/-! ## Kummer extensions -/

/- The source's phrase “obtained by adjoining a root” is represented by the
   equality `IntermediateField.adjoin K {b} = ⊤`.  The nonzero hypothesis is
   needed for the displayed quotient `σ(b) / b`; see the source issue recorded
   in the chapter report. -/
/-- Adjoining a nonzero root of `Xⁿ - a` over a field containing a primitive
    `n`th root of unity gives a Galois extension, and its automorphism group
    embeds in the `n`th roots of unity of the base field. -/
theorem kummer_extension_is_galois_and_aut_embedding
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    {n : ℕ} (hn : 2 ≤ n) {ζ : K} (hζ : IsPrimitiveRoot ζ n)
    (a : K) (ha : a ≠ 0) (b : L)
    (hb : b ^ n = algebraMap K L a)
    (hgen : IntermediateField.adjoin K ({b} : Set L) = ⊤) :
    IsGalois K L ∧
      ∃ f : Gal(L / K) →* rootsOfUnity n K,
        Function.Injective f ∧
          (∀ σ : Gal(L / K),
            algebraMap K L (((f σ : rootsOfUnity n K) : Kˣ) : K) = σ b / b) ∧
          IsCyclic (Gal(L / K)) ∧
            Nat.card (Gal(L / K)) ∣ n := by
  classical
  have hneN : NeZero n := ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide) hn)⟩
  have hneK : NeZero (n : K) := hζ.neZero'
  have hn0 : n ≠ 0 := NeZero.ne n
  have hn0' : 0 ≠ n := fun h => hn0 h.symm
  let f : Polynomial K := X ^ n - C a
  have hζL : IsPrimitiveRoot (algebraMap K L ζ) n :=
    hζ.map_of_injective (algebraMap K L).injective
  have hsplit : (Polynomial.map (algebraMap K L) f).Splits := by
    rw [show Polynomial.map (algebraMap K L) f =
        X ^ n - C (algebraMap K L a) by simp [f]]
    exact X_pow_sub_C_splits_of_isPrimitiveRoot hζL hb
  have hf0 : f ≠ 0 := by
    intro hf
    have hcoeff := congrArg (fun g : Polynomial K => g.coeff 0) hf
    simp [f, ha, hn0'] at hcoeff
  have hbroot : b ∈ f.rootSet L := by
    rw [Polynomial.mem_rootSet_of_ne hf0]
    simp [f, hb]
  have hle : IntermediateField.adjoin K ({b} : Set L) ≤
      IntermediateField.adjoin K (f.rootSet L) := by
    apply IntermediateField.adjoin_le_iff.mpr
    exact Set.singleton_subset_iff.mpr
      ((IntermediateField.subset_adjoin K (f.rootSet L)) hbroot)
  have htop : IntermediateField.adjoin K (f.rootSet L) = ⊤ := by
    apply top_unique
    simpa [hgen] using hle
  have hsplitField : Polynomial.IsSplittingField K L f :=
    (isSplittingField_iff_intermediateField).mpr ⟨hsplit, by simpa [f] using htop⟩
  have hfsep : f.Separable := by
    simpa [f] using Polynomial.separable_X_pow_sub_C a (NeZero.ne (n : K)) ha
  have hG : IsGalois K L := IsGalois.of_separable_splitting_field hfsep
  have hratioPow (σ : Gal(L / K)) : (σ b / b) ^ n = 1 := by
    rw [div_pow, ← map_pow, hb, AlgEquiv.commutes]
    exact div_self (by
      intro hb0
      apply ha
      apply (algebraMap K L).injective
      simpa [hb] using congrArg σ hb0)
  have hprim : (primitiveRoots n K).Nonempty :=
    ⟨ζ, (mem_primitiveRoots (NeZero.pos n)).mpr hζ⟩
  let rEquiv : rootsOfUnity n K ≃* rootsOfUnity n L :=
    rootsOfUnityEquivOfPrimitiveRoots (algebraMap K L).injective hprim
  let η : Gal(L / K) → rootsOfUnity n L := fun σ =>
    rootsOfUnity.mkOfPowEq (σ b / b) (hratioPow σ)
  let g : Gal(L / K) → rootsOfUnity n K := fun σ => rEquiv.symm (η σ)
  have hgembed (σ : Gal(L / K)) :
      algebraMap K L (((g σ : rootsOfUnity n K) : Kˣ) : K) = σ b / b := by
    have h := rootsOfUnityEquivOfPrimitiveRoots_symm_apply
      (algebraMap K L).injective hprim (η σ)
    exact h
  have hb0 : b ≠ 0 := by
    intro hb0
    apply ha
    exact (algebraMap K L).injective (by
      rw [← hb]
      simp [hb0, NeZero.ne n])
  have hratioMul (σ τ : Gal(L / K)) :
      (σ * τ) b / b = (σ b / b) * (τ b / b) := by
    have hτ : τ b =
        algebraMap K L (((g τ : rootsOfUnity n K) : Kˣ) : K) * b := by
      calc
        τ b = (τ b / b) * b := (div_mul_cancel₀ _ hb0).symm
        _ = algebraMap K L (((g τ : rootsOfUnity n K) : Kˣ) : K) * b := by
          rw [hgembed τ]
    rw [show (σ * τ) b = σ (τ b) by rfl, hτ, map_mul, AlgEquiv.commutes]
    field_simp
  let f : Gal(L / K) →* rootsOfUnity n K :=
    { toFun := g
      map_one' := by
        apply rEquiv.injective
        apply rootsOfUnity.coe_injective
        simp [g, η, hb0]
      map_mul' := by
        intro σ τ
        apply rEquiv.injective
        apply rootsOfUnity.coe_injective
        simp only [g, MulEquiv.apply_symm_apply, map_mul, η,
          rootsOfUnity.coe_mkOfPowEq]
        exact hratioMul σ τ }
  have hσeqτ {σ τ : Gal(L / K)} (hσb : σ b = τ b) : σ = τ := by
    apply AlgEquiv.ext
    intro x
    have hx : x ∈ IntermediateField.adjoin K ({b} : Set L) := by
      rw [hgen]
      trivial
    refine IntermediateField.adjoin_induction K
      (p := fun y _ => σ y = τ y) (mem := ?_) (algebraMap := ?_)
      (add := ?_) (inv := ?_) (mul := ?_) hx
    · intro y hy
      simpa [Set.mem_singleton_iff.mp hy] using hσb
    · intro k
      simp
    · intro y z hy hz iy iz
      simp only [map_add, iy, iz]
    · intro y hy iy
      simp only [map_inv₀, iy]
    · intro y z hy hz iy iz
      simp only [map_mul, iy, iz]
  have hf_inj : Function.Injective f := by
    intro σ τ hστ
    apply hσeqτ
    apply mul_right_cancel₀ hb0
    apply (div_eq_div_iff hb0 hb0).mp
    rw [← hgembed σ, ← hgembed τ]
    exact congrArg
      (fun x : rootsOfUnity n K => algebraMap K L (((x : rootsOfUnity n K) : Kˣ) : K)) hστ
  have hfembed (σ : Gal(L / K)) :
      algebraMap K L (((f σ : rootsOfUnity n K) : Kˣ) : K) = σ b / b := by
    simpa [f] using hgembed σ
  have hcycRoots : IsCyclic (rootsOfUnity n K) := rootsOfUnity.isCyclic K n
  have hcyc : IsCyclic (Gal(L / K)) := isCyclic_of_injective f hf_inj
  let H : Subgroup (rootsOfUnity n K) := Subgroup.map f ⊤
  let ψ : Gal(L / K) → H := fun σ =>
    ⟨f σ, by
      change f σ ∈ Subgroup.map f (⊤ : Subgroup (Gal(L / K)))
      exact ⟨σ, trivial, rfl⟩⟩
  have hψ : Function.Bijective ψ := by
    constructor
    · intro σ τ hστ
      apply hf_inj
      exact congrArg Subtype.val hστ
    · rintro ⟨x, ⟨σ, -, rfl⟩⟩
      exact ⟨σ, rfl⟩
  have hcard : Nat.card (Gal(L / K)) ∣ Nat.card (rootsOfUnity n K) := by
    have hH : Nat.card H ∣ Nat.card (rootsOfUnity n K) :=
      Subgroup.card_subgroup_dvd_card H
    rw [Nat.card_congr (Equiv.ofBijective ψ hψ)]
    exact hH
  have hdiv : Nat.card (Gal(L / K)) ∣ n := by
    rw [hζ.card_rootsOfUnity] at hcard
    exact hcard
  refine ⟨hG, ?_⟩
  exact ⟨f, hf_inj, hfembed, hcyc, hdiv⟩

/- Mathlib's `autEquivRootsOfUnity` is the canonical version of the source's
   displayed map in the exact splitting-field presentation; the preceding
   declaration records the source's more general injective form. -/

/- The source's converse assumes that the Galois group is the cyclic group
   `ℤ/nℤ`.  `Multiplicative (ZMod n)` is Mathlib's multiplicative presentation
   of that group.  Membership in `K` is expressed by the range of the
   canonical algebra map, and `K[z] = L` by `IntermediateField.adjoin = ⊤`. -/
/-- A finite cyclic Galois extension of order `n` over a field containing a
    primitive `n`th root of unity is generated by an element whose `n`th power
    lies in the base field. -/
theorem exists_kummer_generator_of_cyclic_galois
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    {n : ℕ} (hn : 2 ≤ n) {ζ : K} (hζ : IsPrimitiveRoot ζ n)
    (_hchar : ringChar K = 0 ∨ Nat.Coprime (ringChar K) n)
    (hG : Nonempty (Gal(L / K) ≃* Multiplicative (ZMod n))) :
    ∃ z : L,
      z ^ n ∈ Set.range (algebraMap K L) ∧
        IntermediateField.adjoin K ({z} : Set L) = ⊤ := by
  classical
  have hneN : NeZero n := ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide) hn)⟩
  let e : Gal(L / K) ≃* Multiplicative (ZMod n) := Classical.choice hG
  have hcycGal : IsCyclic (Gal(L / K)) :=
    isCyclic_of_surjective e.symm e.symm.surjective
  have hcard : Nat.card (Gal(L / K)) = n := by
    rw [Nat.card_congr e.toEquiv]
    rw [Nat.card_congr Multiplicative.toAdd]
    simpa only [Nat.card_eq_fintype_card] using ZMod.card n
  have hfin : Module.finrank K L = n := by
    rw [← IsGalois.card_aut_eq_finrank]
    exact hcard
  have hζ' : IsPrimitiveRoot ζ (Module.finrank K L) := by
    rw [hfin]
    exact hζ
  have hK : (primitiveRoots (Module.finrank K L) K).Nonempty :=
    ⟨ζ, (mem_primitiveRoots Module.finrank_pos).mpr hζ'⟩
  obtain ⟨z, hz, hzgen⟩ := exists_root_adjoin_eq_top_of_isCyclic K L hK
  exact ⟨z, by simpa [hfin] using hz, hzgen⟩

/- The prime-root-of-unity lemma uses an arbitrary algebraic closure through
   Mathlib's `IsAlgClosure` class. -/
/-- Adjoining a primitive `p`th root of unity in an algebraic closure gives a
    Galois extension of degree dividing `p - 1`. -/
theorem adjoin_primitive_prime_root_of_unity_is_galois
    {K Kbar : Type*} [Field K] [Field Kbar] [Algebra K Kbar]
    [IsAlgClosure K Kbar]
    {p : ℕ} (hp : p.Prime) (hchar : ringChar K ≠ p)
    {ζ : Kbar} (hζ : IsPrimitiveRoot ζ p) :
    IsGalois K (IntermediateField.adjoin K ({ζ} : Set Kbar)) ∧
      Module.finrank K (IntermediateField.adjoin K ({ζ} : Set Kbar)) ∣ p - 1 := by
  classical
  have hneP : NeZero p := ⟨hp.ne_zero⟩
  have hfactP : Fact p.Prime := ⟨hp⟩
  have hpcast : (p : K) ≠ 0 := by
    intro hp0
    have hdiv : ringChar K ∣ p := (ringChar.spec K p).mp hp0
    rcases CharP.char_is_prime_or_zero K (ringChar K) with hprime | hzero
    · rw [Nat.dvd_prime hp] at hdiv
      rcases hdiv with h | h
      · exact (CharP.ringChar_ne_one : ringChar K ≠ 1) h
      · exact hchar h
    · simp [hzero, hp.ne_zero] at hdiv
  have hnePK : NeZero (p : K) := ⟨hpcast⟩
  have hnePKbar : NeZero (p : Kbar) := ⟨by
    intro hp0
    apply hpcast
    apply (algebraMap K Kbar).injective
    simpa using hp0⟩
  have hcyclotomic : IsCyclotomicExtension {p} K
      (IntermediateField.adjoin K ({ζ} : Set Kbar)) :=
    hζ.intermediateField_adjoin_isCyclotomicExtension K
  let Kζ := IntermediateField.adjoin K ({ζ} : Set Kbar)
  let ζ' : Kζ :=
    ⟨ζ, (IntermediateField.subset_adjoin K ({ζ} : Set Kbar)) (Set.mem_singleton ζ)⟩
  have hζ' : IsPrimitiveRoot ζ' p := by
    rw [IsPrimitiveRoot.iff_def]
    have hζdef := (IsPrimitiveRoot.iff_def ζ p).mp hζ
    constructor
    · apply Subtype.ext
      exact hζdef.1
    · intro l hl
      exact hζdef.2 l (congrArg Subtype.val hl)
  let φ : Gal(Kζ / K) →* (ZMod p)ˣ := hζ'.autToPow K
  have hφ : Function.Injective φ := hζ'.autToPow_injective K
  let H : Subgroup ((ZMod p)ˣ) := Subgroup.map φ ⊤
  let ψ : Gal(Kζ / K) → H := fun σ =>
    ⟨φ σ, by
      change φ σ ∈ Subgroup.map φ (⊤ : Subgroup (Gal(Kζ / K)))
      exact ⟨σ, trivial, rfl⟩⟩
  have hψ : Function.Bijective ψ := by
    constructor
    · intro σ τ h
      apply hφ
      exact congrArg Subtype.val h
    · rintro ⟨x, ⟨σ, -, rfl⟩⟩
      exact ⟨σ, rfl⟩
  have hcard : Nat.card (Gal(Kζ / K)) ∣ Nat.card ((ZMod p)ˣ) := by
    have hH : Nat.card H ∣ Nat.card ((ZMod p)ˣ) := Subgroup.card_subgroup_dvd_card H
    rw [Nat.card_congr (Equiv.ofBijective ψ hψ)]
    exact hH
  have hfinite : FiniteDimensional K Kζ := by
    dsimp [Kζ]
    exact IntermediateField.adjoin.finiteDimensional
      (Algebra.IsIntegral.isIntegral ζ)
  have hgalois : IsGalois K Kζ := IsCyclotomicExtension.isGalois {p} K Kζ
  refine ⟨inferInstance, ?_⟩
  rw [← IsGalois.card_aut_eq_finrank]
  calc
    Nat.card (Gal(Kζ / K)) ∣ Nat.card ((ZMod p)ˣ) := hcard
    _ = p - 1 := by
      rw [Nat.card_units (ZMod p)]
      simp only [Nat.card_eq_fintype_card, ZMod.card]

/- The final lemma is stated for an arbitrary intermediate field `L'`; this is
   Mathlib's canonical representation of a subextension `L/L'/K`. -/
/-- Every intermediate field of a finite simple extension generated by an
    `e`th root is generated by a power `α^d` with `d ∣ e`, provided all
    `e`th roots of unity in the extension already lie in the base field. -/
theorem subextension_of_kummer_is_generated_by_power
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] {e : ℕ}
    (he : Module.finrank K L = e) (α : L)
    (hgen : IntermediateField.adjoin K ({α} : Set L) = ⊤)
    (hα : ∃ a : K, α ^ e = algebraMap K L a)
    (hroots : ∀ ζ : L, ζ ^ e = 1 → ζ ∈ Set.range (algebraMap K L)) :
    ∀ L' : IntermediateField K L,
      ∃ d : ℕ, d ∣ e ∧ IntermediateField.adjoin K ({α ^ d} : Set L) = L' := by
  intro L'
  obtain ⟨a, ha⟩ := hα
  have hepos : 0 < e := by
    rw [← he]
    exact Module.finrank_pos
  by_cases hα0 : α = 0
  · subst α
    have htopbot : (⊤ : IntermediateField K L) = ⊥ := by
      rw [← hgen]
      simp
    have hL'top : L' = ⊤ := by
      apply le_antisymm le_top
      rw [htopbot]
      exact bot_le
    refine ⟨e, dvd_rfl, ?_⟩
    rw [hL'top]
    simpa [zero_pow hepos.ne'] using hgen
  · let d : ℕ := Module.finrank L' L
    have hde : d ∣ e := by
      change Module.finrank L' L ∣ e
      rw [← he, ← Module.finrank_mul_finrank K L' L]
      exact dvd_mul_left _ _
    let c : L' := Algebra.norm L' α
    have hnormpow :
        (algebraMap L' L c) ^ e = (algebraMap K L a) ^ d := by
      dsimp [c]
      calc
        (algebraMap L' L (Algebra.norm L' α)) ^ e =
            algebraMap L' L ((Algebra.norm L' α) ^ e) := by
              rw [map_pow]
        _ = algebraMap L' L (Algebra.norm L' (α ^ e)) := by
              congr 1
              exact (map_pow (Algebra.norm L') α e).symm
        _ = algebraMap L' L (Algebra.norm L' (algebraMap K L a)) := by
              rw [ha]
        _ = algebraMap L' L ((algebraMap K L' a) ^ d) := by
              have hscalar : algebraMap K L a =
                  algebraMap L' L (algebraMap K L' a) :=
                (IsScalarTower.algebraMap_apply K L' L a).symm
              rw [hscalar, Algebra.norm_algebraMap]
        _ = (algebraMap K L a) ^ d := by
              have hscalar : algebraMap K L a =
                  algebraMap L' L (algebraMap K L' a) :=
                (IsScalarTower.algebraMap_apply K L' L a).symm
              rw [map_pow, hscalar]
    have hαpow0 : α ^ e ≠ 0 := pow_ne_zero _ hα0
    have hmapa0 : algebraMap K L a ≠ 0 := by
      rw [← ha]
      exact hαpow0
    have hratio :
        (algebraMap L' L c / α ^ d) ^ e = 1 := by
      calc
        (algebraMap L' L c / α ^ d) ^ e =
            (algebraMap L' L c) ^ e / (α ^ d) ^ e := by rw [div_pow]
        _ = (algebraMap K L a) ^ d / (α ^ e) ^ d := by
              rw [hnormpow]
              congr 1
              rw [← pow_mul, ← pow_mul, Nat.mul_comm]
        _ = ((algebraMap K L a) / α ^ e) ^ d := by rw [div_pow]
        _ = 1 := by rw [ha, div_self hmapa0, one_pow]
    obtain ⟨k, hk⟩ := hroots (algebraMap L' L c / α ^ d) hratio
    have hratio0 : algebraMap L' L c / α ^ d ≠ 0 := by
      intro hzero
      rw [hzero, zero_pow hepos.ne'] at hratio
      exact zero_ne_one hratio
    have hk0 : k ≠ 0 := by
      intro hk0
      apply hratio0
      rw [← hk, hk0, map_zero]
    have hprod : algebraMap K L k * α ^ d = algebraMap L' L c := by
      rw [hk, div_mul_cancel₀ _ (pow_ne_zero _ hα0)]
    have hpower_mem : α ^ d ∈ (L' : Set L) := by
      let x : L' := (algebraMap K L' k)⁻¹ * c
      have hx : algebraMap L' L x = α ^ d := by
        dsimp [x]
        change (algebraMap K L k)⁻¹ * algebraMap L' L c = α ^ d
        rw [← hprod]
        have hmapk0 : algebraMap K L k ≠ 0 := by
          intro hzero
          apply hk0
          apply (algebraMap K L).injective
          simpa using hzero
        rw [← mul_assoc, inv_mul_cancel₀ hmapk0, one_mul]
      rw [← hx]
      exact x.property
    sorry

end

end Formalization.Books.Fields.Unit24
