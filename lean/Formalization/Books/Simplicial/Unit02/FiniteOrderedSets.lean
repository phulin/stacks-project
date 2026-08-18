import Mathlib.AlgebraicTopology.SimplexCategory.GeneratorsRelations.Basic
import Mathlib.AlgebraicTopology.SimplexCategory.GeneratorsRelations.NormalForms
import Mathlib.AlgebraicTopology.SimplexCategory.ToMkOne
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Order.Interval.Finset.Fin
import Mathlib.SetTheory.Cardinal.NatCard


/-!
# Simplicial Methods, Chapter 2: The category of finite ordered sets

The canonical model of the simplex category is already provided by Mathlib.
This file records the source-facing assertions which are not single existing
declarations, while referring directly to Mathlib's objects, morphisms, face
maps, degeneracy maps, and simplicial identities.
-/

namespace Formalization.Books.Simplicial.Unit02

open CategoryTheory

/-!
The source's category `Δ`, its objects `[n]`, and its nondecreasing maps are
Mathlib's `SimplexCategory`, `⦋n⦌`, and `SimplexCategory.Hom`.  The underlying
hom equivalence is `SimplexCategory.homEquivOrderHom`.  The assertion that
this is equivalent to the category of nonempty finite linearly ordered sets
is provided by `SimplexCategory.skeletalEquivalence`.

The source's face and degeneracy maps are exactly
`SimplexCategory.δ` and `SimplexCategory.σ`; both have real definitions in
Mathlib.  Their index types `Fin (n + 2)` and `Fin (n + 1)` express the bounds
on the source indices.
-/

/-! ### The small hom-set cardinalities -/

theorem hom_card_zero_to (n : ℕ) :
    Nat.card (SimplexCategory.mk 0 ⟶ SimplexCategory.mk n) = n + 1 := by
  let e : Fin (n + 1) ≃ (SimplexCategory.mk 0 ⟶ SimplexCategory.mk n) :=
    Equiv.ofBijective (SimplexCategory.const (SimplexCategory.mk 0) (SimplexCategory.mk n)) (by
      constructor
      · intro i j h
        have h' := congrArg (fun f => f.toOrderHom 0) h
        simpa [SimplexCategory.const_apply] using h'
      · intro f
        obtain ⟨i, hi⟩ := SimplexCategory.exists_eq_const_of_zero f
        exact ⟨i, hi.symm⟩)
  simpa using (Nat.card_congr e).symm

theorem hom_card_to_zero (n : ℕ) :
    Nat.card (SimplexCategory.mk n ⟶ SimplexCategory.mk 0) = 1 := by
  let e : Fin 1 ≃ (SimplexCategory.mk n ⟶ SimplexCategory.mk 0) :=
    Equiv.ofBijective (SimplexCategory.const (SimplexCategory.mk n) (SimplexCategory.mk 0)) (by
      constructor
      · intro i j h
        exact Subsingleton.elim i j
      · intro f
        refine ⟨0, ?_⟩
        exact (SimplexCategory.eq_const_to_zero f).symm)
  exact (Nat.card_congr e).symm.trans (Nat.card_fin 1)

theorem hom_card_one_to (n : ℕ) :
    Nat.card (SimplexCategory.mk 1 ⟶ SimplexCategory.mk n) = (n + 1) * (n + 2) / 2 := by
  let P := {p : Fin (n + 1) × Fin (n + 1) // p.1 ≤ p.2}
  let e : (SimplexCategory.mk 1 ⟶ SimplexCategory.mk n) ≃ P :=
    { toFun := fun f =>
        ⟨(f.toOrderHom 0, f.toOrderHom 1),
          f.toOrderHom.monotone (by decide : (0 : Fin 2) ≤ 1)⟩
      invFun := fun p => SimplexCategory.mkOfLe p.1.1 p.1.2 p.2
      left_inv := by
        intro f
        apply SimplexCategory.Hom.ext_one_left
        · rfl
        · rfl
      right_inv := by
        rintro ⟨⟨i, j⟩, h⟩
        rfl }
  let e2 : P ≃ Σ i : Fin (n + 1), {j : Fin (n + 1) // i ≤ j} :=
    { toFun := fun p => ⟨p.1.1, ⟨p.1.2, p.2⟩⟩
      invFun := fun q => ⟨(q.1, q.2.1), q.2.2⟩
      left_inv := by rintro ⟨⟨i, j⟩, h⟩; rfl
      right_inv := by rintro ⟨i, ⟨j, h⟩⟩; rfl }
  have hp : Fintype.card P =
      (Finset.univ.sum fun i : Fin (n + 1) =>
        Fintype.card {j : Fin (n + 1) // i ≤ j}) := by
    rw [Fintype.card_congr e2, Fintype.card_sigma]
  have hi (i : Fin (n + 1)) :
      Fintype.card {j : Fin (n + 1) // i ≤ j} = n + 1 - i := by
    rw [Fintype.card_subtype]
    have hfin : (Finset.univ.filter (fun x : Fin (n + 1) => i ≤ x)) = Finset.Ici i := by
      ext j
      simp
    rw [hfin]
    exact Fin.card_Ici i
  have hsum :
      (Finset.univ.sum (fun i : Fin (n + 1) => n + 1 - i.val)) =
        (n + 1) * (n + 2) / 2 := by
    rw [Fin.sum_univ_eq_sum_range]
    rw [show (Finset.range (n + 1)).sum (fun i => n + 1 - i) =
        (Finset.range (n + 1)).sum (fun i => (n - i) + 1) by
          apply Finset.sum_congr rfl
          intro i hi
          have hi' : i < n + 1 := Finset.mem_range.mp hi
          omega]
    rw [Finset.sum_add_distrib]
    have hreflect :
        (Finset.range (n + 1)).sum (fun i => n - i) =
          (Finset.range (n + 1)).sum (fun i => i) := by
      simpa using (Finset.sum_range_reflect (fun i => i) (n + 1))
    rw [hreflect, Finset.sum_range_id]
    simp only [Finset.sum_const, Finset.card_range, Nat.nsmul_eq_mul, Nat.mul_one]
    calc
      (n + 1) * n / 2 + (n + 1) =
          ((n + 1) * n + 2 * (n + 1)) / 2 := by
            rw [Nat.add_div_of_dvd_left (dvd_mul_right 2 (n + 1))]
            simp
      _ = (n + 1) * (n + 2) / 2 := by
        apply congrArg (fun x : ℕ => x / 2)
        conv_rhs => rw [Nat.mul_add]
        simp [Nat.mul_comm]
  calc
    Nat.card (SimplexCategory.mk 1 ⟶ SimplexCategory.mk n) = Fintype.card P := by
      simpa only [Nat.card_eq_fintype_card] using (Nat.card_congr e)
    _ = Finset.univ.sum (fun i : Fin (n + 1) =>
        Fintype.card {j : Fin (n + 1) // i ≤ j}) := hp
    _ = Finset.univ.sum (fun i : Fin (n + 1) => n + 1 - i.val) := by
      apply Finset.sum_congr rfl
      intro i hi'
      exact hi i
    _ = (n + 1) * (n + 2) / 2 := hsum

theorem hom_card_to_one (n : ℕ) :
    Nat.card (SimplexCategory.mk n ⟶ SimplexCategory.mk 1) = n + 2 := by
  let e := SimplexCategory.toMk₁Equiv (n := n)
  exact (Nat.card_congr e).symm.trans (Nat.card_fin (n + 2))

/-!
The factorization assertion in the source is represented using Mathlib's
canonical generators-and-relations presentation.  Its
`generators.multiplicativeClosure` is precisely the predicate that a
morphism is an identity or a composition of face and degeneracy generators.
-/

theorem every_simplex_morphism_is_generated
    {n m : ℕ} (f : SimplexCategory.mk n ⟶ SimplexCategory.mk m) :
    ∃ g : SimplexCategoryGenRel.mk n ⟶ SimplexCategoryGenRel.mk m,
      SimplexCategoryGenRel.toSimplexCategory.map g = f ∧
        SimplexCategoryGenRel.generators.multiplicativeClosure g := by
  let P : ℕ → Prop := fun k =>
    ∀ n m, k = n + m → ∀ f : SimplexCategory.mk n ⟶ SimplexCategory.mk m,
      ∃ g : SimplexCategoryGenRel.mk n ⟶ SimplexCategoryGenRel.mk m,
        SimplexCategoryGenRel.toSimplexCategory.map g = f ∧
          SimplexCategoryGenRel.generators.multiplicativeClosure g
  have H : ∀ k, P k := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro n m hnm f
      by_cases hni : Function.Injective f.toOrderHom
      · by_cases hns : Function.Surjective f.toOrderHom
        · have hcard : n + 1 = m + 1 := by
            simpa using Nat.card_congr
              (Equiv.ofBijective f.toOrderHom.toFun ⟨hni, hns⟩)
          have hnm' : n = m := by omega
          subst m
          have hmono : Mono f := (SimplexCategory.mono_iff_injective).mpr hni
          refine ⟨𝟙 _, ?_, ?_⟩
          · simp [SimplexCategory.eq_id_of_mono f]
          · rw [SimplexCategoryGenRel.multiplicativeClosure_isGenerator_eq_top]
            exact MorphismProperty.top_apply (𝟙 _)
        · cases m with
          | zero =>
            exfalso
            apply hns
            intro y
            exact ⟨0, (Fin.eq_zero _).trans (Fin.eq_zero y).symm⟩
          | succ m =>
            obtain ⟨i, f', hf⟩ :=
              SimplexCategory.eq_comp_δ_of_not_surjective f hns
            obtain ⟨g, hg, hgc⟩ := ih (n + m) (by omega) n m rfl f'
            refine ⟨g ≫ SimplexCategoryGenRel.δ i, ?_, ?_⟩
            · rw [Functor.map_comp, SimplexCategoryGenRel.toSimplexCategory_map_δ, hg]
              exact hf.symm
            · exact SimplexCategoryGenRel.generators.multiplicativeClosure.comp_mem _ _
                hgc (MorphismProperty.multiplicativeClosure.of _
                  (SimplexCategoryGenRel.generators.δ i))
      · cases n with
        | zero =>
          exfalso
          apply hni
          intro a b hab
          exact (Fin.eq_zero a).trans (Fin.eq_zero b).symm
        | succ n =>
          obtain ⟨i, f', hf⟩ :=
            SimplexCategory.eq_σ_comp_of_not_injective f hni
          obtain ⟨g, hg, hgc⟩ := ih (n + m) (by omega) n m rfl f'
          refine ⟨SimplexCategoryGenRel.σ i ≫ g, ?_, ?_⟩
          · rw [Functor.map_comp, SimplexCategoryGenRel.toSimplexCategory_map_σ, hg]
            exact hf.symm
          · exact SimplexCategoryGenRel.generators.multiplicativeClosure.comp_mem _ _
              (MorphismProperty.multiplicativeClosure.of _
                (SimplexCategoryGenRel.generators.σ i)) hgc
  simpa only [P] using H (n + m) n m rfl f

/-!
The five displayed source diagrams are already covered by the stronger,
source-faithful Mathlib identities:

* source (1): `SimplexCategory.δ_comp_δ`;
* source (2): `SimplexCategory.δ_comp_σ_of_le`;
* source (3): `SimplexCategory.δ_comp_σ_self` and
  `SimplexCategory.δ_comp_σ_succ`;
* source (4): `SimplexCategory.δ_comp_σ_of_gt`;
* source (5): `SimplexCategory.σ_comp_σ`.

The `Fin.castSucc` and `Fin.succ` indices in those declarations are the
canonical typed form of the source's integer index bounds, so no parallel
face/degeneracy identities are introduced here.
-/

/-!
The presentation category and its canonical functor are also existing
definitions: `SimplexCategoryGenRel` is generated by the six typed families
of relation constructors, and
`SimplexCategoryGenRel.multiplicativeClosure_isGenerator_eq_top` records that
all of its morphisms are generated by faces and degeneracies.  The remaining
universal-category assertion from the source is the equivalence statement
below; its proof is left for the proof stage.
-/

theorem toSimplexCategory_is_equivalence :
    Functor.IsEquivalence SimplexCategoryGenRel.toSimplexCategory := by
  sorry

end Formalization.Books.Simplicial.Unit02
