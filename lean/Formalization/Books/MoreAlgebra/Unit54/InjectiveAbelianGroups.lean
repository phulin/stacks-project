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
  sorry

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
