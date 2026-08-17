import Mathlib.GroupTheory.Exponent
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.RingTheory.RootsOfUnity.Basic
import Mathlib.RingTheory.ZMod.UnitsCyclic
import Mathlib.SetTheory.Cardinal.Finite

/-!
# Fields, Chapter 17: Roots of unity

The source's `μₙ(F)` is Mathlib's canonical `rootsOfUnity n F`: a subgroup of
the unit group `Fˣ`.  Its coercion image in `F` is exactly the set of field
elements satisfying `x ^ n = 1`, while the subgroup representation supplies
the multiplication, identity, inclusion, and cyclic-group interfaces.
-/

namespace Formalization.Books.Fields.Unit17

noncomputable section

open Polynomial

universe u

/-! ## The group of roots of unity -/

/- The source's set-valued definition is the coercion image of Mathlib's
   canonical subgroup; no parallel root predicate is introduced. -/
/-- The field-element form of the source's `μₙ(F)` definition. -/
theorem rootsOfUnity_coe_set_eq_pow_eq_one
    (F : Type u) [Field F] (n : ℕ) [NeZero n] :
    ((↑) : Fˣ → F) '' (rootsOfUnity n F) = {x : F | x ^ n = 1} :=
  Units.val_set_image_rootsOfUnity

/-- A polynomial over a field has at most its natural degree many distinct
    roots in that field. -/
theorem polynomial_rootSet_ncard_le_natDegree
    (F : Type u) [Field F] (P : F[X]) :
    Set.ncard (P.rootSet F) ≤ P.natDegree :=
  Polynomial.ncard_rootSet_le P F

/- `rootsOfUnity n F` is a subgroup of `Fˣ`; for a field, `Fˣ` is a
   commutative group, so the source's abelian-group and neutral-element
   assertions are carried by inherited instances. -/

/-- The number of `n`th roots of unity in a field is at most `n`. -/
theorem rootsOfUnity_card_le
    (F : Type u) [Field F] (n : ℕ) [NeZero n] :
    Nat.card (rootsOfUnity n F) ≤ n :=
  card_rootsOfUnity F n

/-- Every element of `μₙ(F)` has order dividing `n`. -/
theorem orderOf_mem_rootsOfUnity_dvd
    (F : Type u) [Field F] (n : ℕ) [NeZero n]
    (ζ : rootsOfUnity n F) :
    orderOf ζ ∣ n :=
  orderOf_dvd_of_pow_eq_one (by
    apply Subtype.ext
    exact (mem_rootsOfUnity n ζ.1).mp ζ.2)

/-- If `d ∣ n`, then the `d`th roots of unity form a subgroup of the `n`th
    roots of unity. -/
theorem rootsOfUnity_le_of_dvd
    (F : Type u) [Field F] {d n : ℕ} (hdn : d ∣ n) :
    rootsOfUnity d F ≤ rootsOfUnity n F :=
  _root_.rootsOfUnity_le_of_dvd hdn

/-- Each subgroup `μ_d(F)` with `d ∣ n` has at most `d` elements. -/
theorem rootsOfUnity_card_le_of_dvd
    (F : Type u) [Field F] {d n : ℕ} [NeZero n] (hdn : d ∣ n) :
    Nat.card (rootsOfUnity d F) ≤ d := by
  have hd : 0 < d := Nat.pos_of_dvd_of_pos hdn (NeZero.pos n)
  let _ : NeZero d := ⟨hd.ne'⟩
  exact rootsOfUnity_card_le F d

/- Mathlib proves the field case directly, using the canonical cyclicity
   theorem for roots of unity. -/
/-- The group `μₙ(F)` of roots of unity in a field is cyclic. -/
theorem rootsOfUnity_is_cyclic
    (F : Type u) [Field F] (n : ℕ) [NeZero n] :
    IsCyclic (rootsOfUnity n F) :=
  rootsOfUnity.isCyclic F n

/-! ## The finite abelian-group lemma -/

/- The source writes the annihilator condition additively.  `Cardinal.mk` is
   used in the hypothesis rather than `Nat.card`, because “at most `d`” must
   also rule out an infinite annihilator. -/
/-- An abelian group with bounded annihilators and exponent dividing `n` is
    cyclic, with order dividing `n`. -/
theorem isAddCyclic_of_exponent_dvd_of_card_nsmul_eq_zero_le
    (A : Type u) [AddCommGroup A] (n : ℕ) (hn : 0 < n)
    (hexp : AddMonoid.exponent A ∣ n)
    (hcard : ∀ d : ℕ, d ∣ n →
      Cardinal.mk {x : A // d • x = 0} ≤ d) :
    IsAddCyclic A ∧ Nat.card A ∣ n := by
  classical
  have hzero : ∀ x : A, n • x = 0 :=
    (AddMonoid.exponent_dvd_iff_forall_nsmul_eq_zero.mp hexp)
  have hgcd_zero (d : ℕ) (x : A) (hdx : d • x = 0) (hnx : n • x = 0) :
      Nat.gcd d n • x = 0 := by
    have hBez := Int.gcd_eq_gcd_ab (d : ℤ) (n : ℤ)
    apply_fun (fun k : ℤ => k • x) at hBez
    simp [add_zsmul, mul_zsmul, hdx, hnx] at hBez ⊢
  have hfinite_sub : Finite {x : A // n • x = 0} := by
    exact Cardinal.mk_lt_aleph0_iff.mp
      ((hcard n dvd_rfl).trans_lt Cardinal.natCast_lt_aleph0)
  let _ : Finite A := Finite.of_injective (fun x : A => (⟨x, hzero x⟩ :
      {x : A // n • x = 0})) (fun x y h => Subtype.ext_iff.mp h)
  let _ : Fintype A := Fintype.ofFinite A
  have hbound : ∀ d : ℕ, 0 < d →
      (Finset.univ.filter (fun x : A => d • x = 0)).card ≤ d := by
    intro d hd
    have hsub : {x : A | d • x = 0} ⊆ {x : A | Nat.gcd d n • x = 0} := by
      intro x hx
      exact hgcd_zero d x hx (hzero x)
    have hcg : (Set.ncard {x : A | Nat.gcd d n • x = 0} : Cardinal) ≤ Nat.gcd d n := by
      rw [Set.cast_ncard (Set.toFinite _)]
      exact hcard (Nat.gcd d n) (Nat.gcd_dvd_right d n)
    have hcg' : Set.ncard {x : A | Nat.gcd d n • x = 0} ≤ Nat.gcd d n := by
      exact_mod_cast hcg
    have hle' : Set.ncard {x : A | d • x = 0} ≤ d := by
      have hle_min : Set.ncard {x : A | d • x = 0} ≤ min d n := by
        apply le_min
        · exact le_trans (Set.ncard_le_ncard hsub)
            (le_trans hcg' (Nat.gcd_le_left n hd))
        · exact le_trans (Set.ncard_le_ncard hsub)
            (le_trans hcg' (Nat.gcd_le_right d hn))
      exact le_trans hle_min (min_le_left _ _)
    have hle'' : Fintype.card ({x : A | d • x = 0} : Set A) ≤ d := by
      rw [Set.fintypeCard_eq_ncard]
      exact hle'
    have hfilter :
        Fintype.card ({x : A | d • x = 0} : Set A) =
          (Finset.univ.filter (fun x : A => d • x = 0)).card :=
      Fintype.card_of_finset' (p := {x : A | d • x = 0}) _ (by
        intro x
        simp)
    exact hfilter ▸ hle''
  have hcyc : IsAddCyclic A :=
    isAddCyclic_of_card_nsmul_eq_zero_le hbound
  have hcard_exp : AddMonoid.exponent A = Nat.card A :=
    @IsAddCyclic.exponent_eq_card A _ hcyc
  exact ⟨hcyc, hcard_exp ▸ hexp⟩

/-! ## Prime finite fields and positive characteristic -/

/- The finite-field application is already a named Mathlib theorem for the
   canonical model `ZMod p`. -/
/-- The multiplicative group of the prime field `ZMod p` is cyclic. -/
theorem zmod_prime_units_is_cyclic {p : ℕ} (hp : Nat.Prime p) :
    IsCyclic (ZMod p)ˣ :=
  ZMod.isCyclic_units_prime hp

/- This is the field-element form of the Frobenius-injectivity observation
   used for the final assertion of the source section. -/
/-- In characteristic `p > 0`, the only `pⁿ`th root of unity in a field is
    `1`. -/
theorem pow_char_pow_eq_one_iff_eq_one
    (F : Type u) [Field F] (p n : ℕ) (hp : 0 < p) [CharP F p] (x : F) :
    x ^ (p ^ n) = 1 ↔ x = 1 := by
  let _ : Fact p.Prime := ⟨CharP.char_prime_of_ne_zero F (Nat.ne_of_gt hp)⟩
  simpa using (ExpChar.pow_prime_pow_mul_eq_one_iff p n 1 x)

/-- The characteristic-`p` roots of unity reduce to the singleton subgroup. -/
theorem rootsOfUnity_char_pow_eq_bot
    (F : Type u) [Field F] (p n : ℕ) (hp : 0 < p) [CharP F p] :
    rootsOfUnity (p ^ n) F = (⊥ : Subgroup Fˣ) := by
  ext ζ
  rw [mem_rootsOfUnity', Subgroup.mem_bot, Units.ext_iff, Units.val_one]
  exact pow_char_pow_eq_one_iff_eq_one F p n hp (ζ : F)

/-- In the field-element representation, the characteristic-`p` roots of
    unity are exactly `{1}`. -/
theorem rootsOfUnity_char_pow_coe_set_eq_singleton
    (F : Type u) [Field F] (p n : ℕ) (hp : 0 < p) [CharP F p] :
    ((↑) : Fˣ → F) '' (rootsOfUnity (p ^ n) F) = ({1} : Set F) := by
  rw [rootsOfUnity_char_pow_eq_bot F p n hp]
  simpa only [← rootsOfUnity_one F] using
    (Units.val_set_image_rootsOfUnity_one (R := F))

end

end Formalization.Books.Fields.Unit17
