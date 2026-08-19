import Mathlib.Algebra.Category.Grp.EnoughInjectives

/-!
# More on Algebra, Chapter 54: Injective abelian groups

The source uses the positive natural numbers in its definition of a
divisible abelian group.  `IsDivisible` records that predicate directly;
Mathlib's `DivisibleBy` is a constructive typeclass and is therefore not a
drop-in replacement for the source's proposition.
-/

noncomputable section

open CategoryTheory

universe u

namespace Formalization.Books.MoreAlgebra.Unit54

/-! ## Divisible abelian groups -/

/-- An abelian group is divisible when every element has an `n`-th additive
multiple preimage for every positive natural number `n`. -/
def IsDivisible (M : Type u) [AddCommGroup M] : Prop :=
  ∀ x : M, ∀ n : ℕ, 0 < n → ∃ y : M, n • y = x

/- The source proof uses the defining extension property of injective
   objects, the map `m ↦ m • x` from `ℤ`, and a one-element subgroup
   extension.  These are already represented by Mathlib's `Injective`,
   `AddCommGrpCat.asHom`, and `Injective.factors`; the two cases in the
   one-element extension are proof details of the theorem below, not
   additional chapter-facing interfaces. -/

/-- An abelian group is injective in the category of abelian groups exactly
when it is divisible. -/
theorem injective_iff_divisible (J : Type u) [AddCommGroup J] :
    Injective (C := AddCommGrpCat) (AddCommGrpCat.of J) ↔ IsDivisible J := by
  constructor
  case mp =>
    intro hJ x n hn
    let hJ' : Injective (C := AddCommGrpCat) (AddCommGrpCat.of J) := hJ
    let f : AddCommGrpCat.of (ULift.{u} ℤ) ⟶ AddCommGrpCat.of (ULift.{u} ℤ) :=
      AddCommGrpCat.ofHom
        { toFun := fun z => ULift.up (z.down * (n : ℤ))
          map_zero' := by
            apply ULift.ext
            simp
          map_add' := by
            intro z w
            apply ULift.ext
            simp [add_mul] }
    let g : AddCommGrpCat.of (ULift.{u} ℤ) ⟶ AddCommGrpCat.of J :=
      AddCommGrpCat.ofHom
        { toFun := fun z => z.down • x
          map_zero' := by simp
          map_add' := by
            intro z w
            simp [add_zsmul] }
    have hf : Function.Injective f := by
      intro z w hzw
      apply ULift.ext
      have hzw' := congrArg ULift.down hzw
      change z.down * (n : ℤ) = w.down * (n : ℤ) at hzw'
      have hn' : (n : ℤ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
      exact Int.eq_of_mul_eq_mul_right hn' hzw'
    let hf_mono : Mono f := (AddCommGrpCat.mono_iff_injective f).mpr hf
    obtain ⟨h, hfac⟩ := @Injective.factors _ _ _ hJ' _ _ g f hf_mono
    have hfac' := congrArg (fun k => k (ULift.up 1)) hfac
    have hmul : ∀ m : ℕ, h (ULift.up (m : ℤ)) = m • h (ULift.up 1) := by
      intro m
      induction m with
      | zero =>
          simp only [zero_nsmul]
          have hz : ULift.up ((0 : ℕ) : ℤ) = (0 : ULift.{u} ℤ) := by
            apply ULift.ext
            simp
          rw [hz, map_zero]
      | succ m ih =>
          have heq : ULift.up (((m + 1 : ℕ) : ℤ)) =
              ULift.up (m : ℤ) + ULift.up 1 := by
            apply ULift.ext
            simp
          rw [heq, map_add, ih, succ_nsmul]
    refine ⟨h (ULift.up 1), ?_⟩
    calc
      n • h (ULift.up 1) = h (ULift.up (n : ℤ)) := (hmul n).symm
      _ = x := by simpa [f, g, AddCommGrpCat.comp_apply] using hfac'
  case mpr =>
    intro hdiv
    let hdiv' : DivisibleBy J ℤ :=
      divisibleByOfSMulRightSurj (A := J) (α := ℤ) (fun {n} hn => by
        intro x
        cases n with
        | ofNat n =>
            have hn' : n ≠ 0 := by
              intro hn0
              apply hn
              simp [hn0]
            obtain ⟨y, hy⟩ := hdiv x n (Nat.pos_of_ne_zero hn')
            refine ⟨y, ?_⟩
            simpa using hy
        | negSucc n =>
            obtain ⟨y, hy⟩ := hdiv x (n + 1) (Nat.zero_lt_succ n)
            refine ⟨-y, ?_⟩
            simpa using hy)
    exact @AddCommGrpCat.injective_of_divisible J _ hdiv'

/- The closing assertion of the source is the canonical
   `EnoughInjectives AddCommGrpCat` presentation: every abelian group admits
   a monomorphism into an injective abelian group. -/

/-- Every abelian group embeds as a monomorphism into an injective abelian
group. -/
theorem exists_mono_to_injective (A : AddCommGrpCat) :
    ∃ (J : AddCommGrpCat) (f : A ⟶ J), Mono f ∧ Injective J := by
  obtain ⟨p⟩ := EnoughInjectives.presentation A
  exact ⟨p.J, p.f, p.mono, p.injective⟩

end Formalization.Books.MoreAlgebra.Unit54
