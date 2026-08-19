import Mathlib.AlgebraicTopology.SimplexCategory.GeneratorsRelations.Basic
import Mathlib.AlgebraicTopology.SimplexCategory.GeneratorsRelations.EpiMono
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

private def standardδ (L : List ℕ) {m₁ m₂ : ℕ} (h : m₁ + L.length = m₂) :
    SimplexCategoryGenRel.mk m₁ ⟶ SimplexCategoryGenRel.mk m₂ :=
  match L with
  | [] => eqToHom (by grind)
  | a :: L =>
    SimplexCategoryGenRel.δ (Fin.ofNat _ a) ≫ standardδ L (by grind)

private lemma standardδ_simplicialInsert
    {n : ℕ} (L : List ℕ)
    (hL : SimplexCategoryGenRel.IsAdmissible (n + 2) L)
    (j : ℕ) (hj : j ≤ n + 1) :
    standardδ (SimplexCategoryGenRel.simplicialInsert j L)
        (m₁ := n) (m₂ := n + 1 + L.length) (by
          rw [SimplexCategoryGenRel.simplicialInsert_length]
          omega) =
      SimplexCategoryGenRel.δ (n := n) (Fin.ofNat (n + 2) j) ≫
        standardδ L (m₁ := n + 1) (m₂ := n + 1 + L.length) (by omega) := by
  /- Prior attempt:
  induction L generalizing j n with
  | nil => simp [SimplexCategoryGenRel.simplicialInsert, standardδ]
  | cons a L ih =>
    simp only [SimplexCategoryGenRel.simplicialInsert]
    split_ifs with h
    · simp only [standardδ]
    · have ha : a ≤ j := by omega
      have hL' : SimplexCategoryGenRel.IsAdmissible (n + 3) L := hL.of_cons
      have hj' : j + 1 ≤ n + 2 := by omega
      have hih := ih (n := n + 1) (j := j + 1) hL' hj'
      have hδ :
          SimplexCategoryGenRel.δ (n := n) (Fin.ofNat (n + 2) a) ≫
              SimplexCategoryGenRel.δ (Fin.ofNat (n + 3) (j + 1)) =
              SimplexCategoryGenRel.δ (n := n) (Fin.ofNat (n + 2) j) ≫
              SimplexCategoryGenRel.δ (Fin.ofNat (n + 3) a) := by
        have ha' : Fin.ofNat (n + 2) a =
            (⟨a, show a < n + 2 by omega⟩ : Fin (n + 2)) := by
          apply Fin.ext
          simp [Fin.ofNat, Nat.mod_eq_of_lt (by omega)]
        have hj' : Fin.ofNat (n + 2) j =
            (⟨j, show j < n + 2 by omega⟩ : Fin (n + 2)) := by
          apply Fin.ext
          simp [Fin.ofNat, Nat.mod_eq_of_lt (by omega)]
        have hj₁ : Fin.ofNat (n + 3) (j + 1) =
            (⟨j + 1, show j + 1 < n + 3 by omega⟩ : Fin (n + 3)) := by
          apply Fin.ext
          simp [Fin.ofNat, Nat.mod_eq_of_lt (by omega)]
        have ha₁ : Fin.ofNat (n + 3) a =
            (⟨a, show a < n + 3 by omega⟩ : Fin (n + 3)) := by
          apply Fin.ext
          simp [Fin.ofNat, Nat.mod_eq_of_lt (by omega)]
        simpa only [ha', hj', hj₁, ha₁] using
          (SimplexCategoryGenRel.δ_comp_δ_nat (n := n) a j (by omega)
            (by omega) (by omega))
      simp only [standardδ]
      rw [hih, hδ]
      simp only [Category.assoc]
  -/
  induction L generalizing n j with
  | nil => simp [standardδ, SimplexCategoryGenRel.simplicialInsert]
  | cons a L ih =>
    simp only [SimplexCategoryGenRel.simplicialInsert]
    split_ifs
    · simp [standardδ]
    · have : ∀ (j k : ℕ) (h : j < k + 1), Fin.ofNat (k + 1) j = j := by simp
      have : a < n + 2 := by grind
      have :
          SimplexCategoryGenRel.δ (Fin.ofNat (n + 2) a) ≫
              SimplexCategoryGenRel.δ (Fin.ofNat (n + 3) (j + 1)) =
            SimplexCategoryGenRel.δ (Fin.ofNat (n + 2) j) ≫
              SimplexCategoryGenRel.δ (Fin.ofNat (n + 3) a) := by
        convert! SimplexCategoryGenRel.δ_comp_δ_nat (n := n) a j
          (by grind) (by grind) (by grind) <;> grind
      grind [standardδ]

private lemma exists_normal_form_P_δ
    {x y : SimplexCategoryGenRel} (f : x ⟶ y)
    (hf : SimplexCategoryGenRel.faces.multiplicativeClosure' f) :
    ∃ L : List ℕ, ∃ m : ℕ, ∃ r : ℕ,
      ∃ h₁ : SimplexCategoryGenRel.mk r = y,
      ∃ h₂ : x = SimplexCategoryGenRel.mk m,
      ∃ h : m + L.length = r,
      SimplexCategoryGenRel.IsAdmissible (m + 1) L ∧
        f = eqToHom h₂ ≫ standardδ L (m₁ := m) (m₂ := r) h ≫
          eqToHom h₁ := by
  induction hf with
  | id x =>
    refine ⟨[], x.len, x.len, SimplexCategoryGenRel.ext (by simp),
      (SimplexCategoryGenRel.ext (by simp)).symm, rfl, ?_⟩
    refine ⟨SimplexCategoryGenRel.IsAdmissible.nil _, ?_⟩
    simp [standardδ]
  | of f hf =>
    cases hf with
    | @δ n i =>
      refine ⟨[i.val], n, n + 1, rfl, rfl, by simp, ?_⟩
      refine ⟨SimplexCategoryGenRel.IsAdmissible.singleton (by omega), ?_⟩
      have hi : Fin.ofNat _ i.val = i := by
        apply Fin.ext
        simp [Fin.ofNat, Nat.mod_eq_of_lt i.isLt]
      simp [standardδ, hi]
  | of_comp f g hf hg ih =>
    cases hf with
    | @δ n i =>
      obtain ⟨L, m, r, h₁, h₂, h, hL, e⟩ := ih
      have hm : m = n + 1 := by
        simpa only [SimplexCategoryGenRel.mk_len] using
          (congrArg SimplexCategoryGenRel.len h₂).symm
      subst m
      subst r
      refine ⟨SimplexCategoryGenRel.simplicialInsert i.val L, n,
        n + 1 + L.length, h₁, rfl, by
          rw [SimplexCategoryGenRel.simplicialInsert_length]
          omega, ?_⟩
      refine ⟨SimplexCategoryGenRel.simplicialInsert_isAdmissible _ L hL i.val
        (by omega), ?_⟩
      rw [e]
      simp only [Category.assoc, eqToHom_refl, Category.id_comp]
      have hi : Fin.ofNat _ i.val = i := by
        apply Fin.ext
        simp [Fin.ofNat, Nat.mod_eq_of_lt i.isLt]
      have hδ : SimplexCategoryGenRel.δ i =
          SimplexCategoryGenRel.δ (Fin.ofNat _ i.val) := by rw [hi]
      rw [hδ]
      have hs := congrArg (fun q => q ≫ eqToHom h₁)
        (standardδ_simplicialInsert L hL i.val (by omega)).symm
      simpa only [Category.assoc] using hs

set_option backward.isDefEq.respectTransparency false in
private lemma standardδ_map_of_lt_all
    {n : ℕ} (L : List ℕ)
    (hL : SimplexCategoryGenRel.IsAdmissible (n + 1) L)
    {r : ℕ} (h : n + L.length = r)
    (a : Fin (n + 1)) (ha : ∀ b ∈ L, a.val < b) :
    ((SimplexCategoryGenRel.toSimplexCategory.map
      (standardδ L (m₁ := n) (m₂ := r) h)).toOrderHom a).val =
        a.val := by
  induction L generalizing n r with
  | nil =>
    have hr : n = r := by simpa using h
    subst r
    simp [standardδ, SimplexCategoryGenRel.toSimplexCategory_obj_mk,
      SimplexCategory.len_mk]
  | cons b L ih =>
    simp only [List.length_cons] at h
    have hab : a.val < b := ha b (by simp)
    have haL : ∀ c ∈ L, a.val < c := by
      intro c hc
      exact hab.trans (hL.head_lt c hc)
    have hb : b ≤ n + 1 := by
      simpa using hL.le 0 (by simp)
    have hb' : b < n + 2 := by omega
    have hia : Fin.ofNat (n + 2) a.val =
        (⟨a.val, by omega⟩ : Fin (n + 2)) := by
      apply Fin.ext
      simp [Fin.ofNat, Nat.mod_eq_of_lt (by omega)]
    have hbfin : Fin.ofNat (n + 2) b =
        (⟨b, hb'⟩ : Fin (n + 2)) := by
      apply Fin.ext
      simp [Fin.ofNat, Nat.mod_eq_of_lt (by omega)]
    have hsucc : (Fin.ofNat (n + 2) b).succAbove a = a.castSucc := by
      rw [hbfin]
      exact Fin.succAbove_of_castSucc_lt _ _
        (by simpa only [Fin.lt_def, Fin.val_castSucc] using hab)
    have hcast : a.castSucc = (⟨a.val, by omega⟩ : Fin (n + 2)) := by
      apply Fin.ext
      rfl
    have hih := ih (n := n + 1) (r := r) (h := by omega) (hL := hL.of_cons)
      (a := (⟨a.val, by omega⟩ : Fin (n + 2))) haL
    simp only [SimplexCategoryGenRel.toSimplexCategory_obj_mk, SimplexCategory.len_mk,
      standardδ, Functor.map_comp,
      SimplexCategoryGenRel.toSimplexCategory_map_δ,
      SimplexCategory.comp_toOrderHom, Function.comp_apply,
      SimplexCategory.δ, SimplexCategory.mkHom,
      SimplexCategory.Hom.toOrderHom_mk, OrderHom.comp_coe,
      Fin.succAboveOrderEmb_apply, OrderEmbedding.toOrderHom_coe, hsucc, hia, hcast]
    simp only [SimplexCategoryGenRel.toSimplexCategory_obj_mk, SimplexCategory.len_mk] at hih ⊢
    simpa using hih

private lemma standardδ_P_δ
    {n r : ℕ} (L : List ℕ)
    (hL : SimplexCategoryGenRel.IsAdmissible (n + 1) L)
    (h : n + L.length = r) :
    SimplexCategoryGenRel.P_δ
      (standardδ L (m₁ := n) (m₂ := r) h) := by
  induction L generalizing n r with
  | nil =>
    have hr : n = r := by simpa using h
    subst r
    exact SimplexCategoryGenRel.P_δ.id_mem _
  | cons b L ih =>
    simp only [List.length_cons] at h
    exact SimplexCategoryGenRel.P_δ.comp_mem _ _
      (SimplexCategoryGenRel.P_δ.δ _) (ih (n := n + 1) (r := r)
        (hL := hL.of_cons) (h := by omega))

set_option backward.isDefEq.respectTransparency false in
private lemma standardδ_range_iff
    {n r : ℕ} (L : List ℕ)
    (hL : SimplexCategoryGenRel.IsAdmissible (n + 1) L)
    (h : n + L.length = r) (j : Fin (r + 1)) :
    (∃ i : Fin (n + 1),
      ((SimplexCategoryGenRel.toSimplexCategory.map
        (standardδ L (m₁ := n) (m₂ := r) h)).toOrderHom i) = j) ↔
      j.val ∉ L := by
  induction L generalizing n r with
  | nil =>
    have hr : n = r := by simpa using h
    subst r
    simp [standardδ, SimplexCategoryGenRel.toSimplexCategory_obj_mk,
      SimplexCategory.len_mk]
  | cons b L ih =>
    simp only [List.length_cons] at h
    have hb : b ≤ n + 1 := by
      simpa using hL.le 0 (by simp)
    have hb' : b < n + 2 := by omega
    have hbfin : Fin.ofNat (n + 2) b =
        (⟨b, hb'⟩ : Fin (n + 2)) := by
      apply Fin.ext
      simp [Fin.ofNat, Nat.mod_eq_of_lt hb']
    have htail : (n + 1) + L.length = r := by omega
    have htailL : SimplexCategoryGenRel.IsAdmissible (n + 2) L := hL.of_cons
    have htailb : ∀ c ∈ L, b < c := by
      intro c hc
      exact hL.head_lt c hc
    have htailb' := standardδ_map_of_lt_all L htailL htail
      (a := (⟨b, hb'⟩ : Fin (n + 2))) htailb
    have htailP := standardδ_P_δ L htailL htail
    let tail := SimplexCategoryGenRel.toSimplexCategory.map
      (standardδ L (m₁ := n + 1) (m₂ := r) htail)
    letI : IsSplitMono tail := by
      dsimp [tail]
      exact SimplexCategoryGenRel.isSplitMono_toSimplexCategory_map_of_P_δ htailP
    haveI : Mono tail := inferInstance
    have hinj : Function.Injective tail.toOrderHom :=
      (SimplexCategory.mono_iff_injective).mp inferInstance
    have hcomp (i : Fin (n + 1)) :
        (SimplexCategoryGenRel.toSimplexCategory.map
          (standardδ (b :: L) (m₁ := n) (m₂ := r) h)).toOrderHom i =
          tail.toOrderHom ((Fin.ofNat (n + 2) b).succAbove i) := by
      simp only [tail, standardδ, Functor.map_comp,
        SimplexCategoryGenRel.toSimplexCategory_map_δ,
        SimplexCategoryGenRel.toSimplexCategory_obj_mk, SimplexCategory.len_mk,
        SimplexCategory.comp_toOrderHom, Function.comp_apply,
        SimplexCategory.δ, SimplexCategory.mkHom,
        SimplexCategory.Hom.toOrderHom_mk, OrderHom.comp_coe,
        Fin.succAboveOrderEmb_apply, OrderEmbedding.toOrderHom_coe]
    constructor
    · rintro ⟨i, hi⟩ hj
      rcases List.mem_cons.mp hj with hjb | hjL
      · have hjb' : j = (⟨b, by omega⟩ : Fin (r + 1)) := by
          apply Fin.ext
          simpa [hjb] using congrArg Fin.val hi
        have heq : tail.toOrderHom ((Fin.ofNat (n + 2) b).succAbove i) =
            tail.toOrderHom (⟨b, by omega⟩ : Fin (n + 2)) := by
          rw [← hcomp i, hi, hjb']
          apply Fin.ext
          simpa [tail] using htailb'.symm
        have heq' := hinj heq
        have heq'' : (Fin.ofNat (n + 2) b).succAbove i =
            Fin.ofNat (n + 2) b := heq'.trans hbfin.symm
        exact (Fin.succAbove_ne (Fin.ofNat (n + 2) b) i) heq''
      · have hj' : j.val ∉ L := by
          apply (ih (n := n + 1) (r := r) (hL := htailL) (h := htail) j).mp
          refine ⟨(Fin.ofNat (n + 2) b).succAbove i, ?_⟩
          exact (hcomp i).symm.trans hi
        exact hj' hjL
    · intro hj
      have hjL : j.val ∉ L := by
        intro hjL
        exact hj (List.mem_cons.mpr (Or.inr hjL))
      obtain ⟨t, ht⟩ :=
        (ih (n := n + 1) (r := r) (hL := htailL) (h := htail) j).mpr hjL
      have htne : t ≠ (⟨b, by omega⟩ : Fin (n + 2)) := by
        intro htb
        have hv := congrArg Fin.val ht
        rw [htb, htailb'] at hv
        exact hj (List.mem_cons.mpr (Or.inl hv.symm))
      obtain ⟨i, hi⟩ := (Fin.exists_succAbove_eq_iff).mpr htne
      refine ⟨i, ?_⟩
      change tail.toOrderHom t = j at ht
      have ht' := ht
      rw [← hi] at ht'
      have hc := hcomp i
      rw [hbfin] at hc
      exact hc.trans ht'

private lemma standardδ_list_eq_of_map_eq
    {n r : ℕ} {L K : List ℕ}
    (hL : SimplexCategoryGenRel.IsAdmissible (n + 1) L)
    (hK : SimplexCategoryGenRel.IsAdmissible (n + 1) K)
    (hL' : n + L.length = r) (hK' : n + K.length = r)
    (hmap : SimplexCategoryGenRel.toSimplexCategory.map
        (standardδ L (m₁ := n) (m₂ := r) hL') =
      SimplexCategoryGenRel.toSimplexCategory.map
        (standardδ K (m₁ := n) (m₂ := r) hK')) :
    L = K := by
  apply hL.sortedLT.eq_of_mem_iff hK.sortedLT
  intro j
  constructor
  · intro hjL
    have hjbound : j < r + 1 := by
      obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.mp hjL
      have := hL.getElem_lt (k := k) (hk := by simpa using hk)
      omega
    let jf : Fin (r + 1) := ⟨j, hjbound⟩
    have hnot : ¬ ∃ i : Fin (n + 1),
        (SimplexCategoryGenRel.toSimplexCategory.map
          (standardδ L (m₁ := n) (m₂ := r) hL')).toOrderHom i = jf := by
      intro hrange
      exact (standardδ_range_iff L hL hL' jf).mp hrange hjL
    by_contra hjK
    apply hnot
    obtain ⟨i, hi⟩ := (standardδ_range_iff K hK hK' jf).mpr hjK
    refine ⟨i, ?_⟩
    simpa [hmap] using hi
  · intro hjK
    have hjbound : j < r + 1 := by
      obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.mp hjK
      have := hK.getElem_lt (k := k) (hk := by simpa using hk)
      omega
    let jf : Fin (r + 1) := ⟨j, hjbound⟩
    have hnot : ¬ ∃ i : Fin (n + 1),
        (SimplexCategoryGenRel.toSimplexCategory.map
          (standardδ K (m₁ := n) (m₂ := r) hK')).toOrderHom i = jf := by
      intro hrange
      exact (standardδ_range_iff K hK hK' jf).mp hrange hjK
    by_contra hjL
    apply hnot
    obtain ⟨i, hi⟩ := (standardδ_range_iff L hL hL' jf).mpr hjL
    refine ⟨i, ?_⟩
    simpa [hmap] using hi

private lemma standardσ_list_eq_of_map_eq
    {n r : ℕ} {L K : List ℕ}
    (hL : SimplexCategoryGenRel.IsAdmissible n L)
    (hK : SimplexCategoryGenRel.IsAdmissible n K)
    (hL' : n + L.length = r) (hK' : n + K.length = r)
    (hmap : SimplexCategoryGenRel.toSimplexCategory.map
        (SimplexCategoryGenRel.standardσ L (m₁ := r) (m₂ := n) hL') =
      SimplexCategoryGenRel.toSimplexCategory.map
        (SimplexCategoryGenRel.standardσ K (m₁ := r) (m₂ := n) hK')) :
    L = K := by
  have hev (j : ℕ) (hj : j < r + 1) :
      SimplexCategoryGenRel.simplicialEvalσ L j =
        SimplexCategoryGenRel.simplicialEvalσ K j := by
    calc
      SimplexCategoryGenRel.simplicialEvalσ L j =
          (SimplexCategoryGenRel.toSimplexCategory.map
            (SimplexCategoryGenRel.standardσ L (m₁ := r) (m₂ := n) hL')).toOrderHom
              ⟨j, hj⟩ :=
        (SimplexCategoryGenRel.simplicialEvalσ_of_isAdmissible L r n hL hL' j hj).symm
      _ = (SimplexCategoryGenRel.toSimplexCategory.map
            (SimplexCategoryGenRel.standardσ K (m₁ := r) (m₂ := n) hK')).toOrderHom
              ⟨j, hj⟩ := by rw [hmap]
      _ = SimplexCategoryGenRel.simplicialEvalσ K j :=
        SimplexCategoryGenRel.simplicialEvalσ_of_isAdmissible K r n hK hK' j hj
  apply hL.sortedLT.eq_of_mem_iff hK.sortedLT
  intro j
  by_cases hj : j < r + 1
  · by_cases hjr : j < r
    · rw [SimplexCategoryGenRel.mem_isAdmissible_iff L hL j,
        SimplexCategoryGenRel.mem_isAdmissible_iff K hK j]
      have hjr' : j < n + L.length := by omega
      have hjr'' : j < n + K.length := by omega
      constructor <;> intro hval
      · exact ⟨hjr'', by rw [← hev j hj, ← hev (j + 1) (by omega), hval.2]⟩
      · exact ⟨hjr', by rw [hev j hj, hev (j + 1) (by omega), hval.2]⟩
    · have hj_eq : j = r := by omega
      have hjL : j ∉ L := by
        intro hjL
        obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.mp hjL
        have := hL.getElem_lt (k := k) (hk := by simpa using hk)
        omega
      have hjK : j ∉ K := by
        intro hjK
        obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.mp hjK
        have := hK.getElem_lt (k := k) (hk := by simpa using hk)
        omega
      exact iff_of_false hjL hjK
  · have hjL : j ∉ L := by
      intro hjL
      obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.mp hjL
      have := hL.getElem_lt (k := k) (hk := by simpa using hk)
      omega
    have hjK : j ∉ K := by
      intro hjK
      obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.mp hjK
      have := hK.getElem_lt (k := k) (hk := by simpa using hk)
      omega
    exact iff_of_false hjL hjK

private lemma eq_of_P_σ_map_eq
    {x y : SimplexCategoryGenRel} {f g : x ⟶ y}
    (hf : SimplexCategoryGenRel.P_σ f)
    (hg : SimplexCategoryGenRel.P_σ g)
    (hmap : SimplexCategoryGenRel.toSimplexCategory.map f =
      SimplexCategoryGenRel.toSimplexCategory.map g) :
    f = g := by
  obtain ⟨L, m, b, h₁, h₂, h, hL, hf⟩ :=
    SimplexCategoryGenRel.exists_normal_form_P_σ f hf
  subst y
  subst x
  obtain ⟨K, m', b', h₁', h₂', h', hK, hg⟩ :=
    SimplexCategoryGenRel.exists_normal_form_P_σ g hg
  have hm : m = m' := by
    have := congrArg SimplexCategoryGenRel.len h₁'
    simpa using this.symm
  have hmb : m + b = m' + b' := by
    have := congrArg SimplexCategoryGenRel.len h₂'
    simpa using this
  have hb : b = b' := by omega
  subst m'
  subst b'
  rw [hf, hg] at hmap
  have hL' : m + L.length = m + b := by omega
  have hK' : m + K.length = m + b := by omega
  have hmap' : SimplexCategoryGenRel.toSimplexCategory.map
        (SimplexCategoryGenRel.standardσ L hL') =
      SimplexCategoryGenRel.toSimplexCategory.map
        (SimplexCategoryGenRel.standardσ K hK') := by
    convert hmap using 1 <;> rfl
  have hLK : L = K :=
    standardσ_list_eq_of_map_eq hL hK hL' hK' hmap'
  cases hLK
  exact hf.trans hg.symm

private lemma eq_of_P_δ_map_eq
    {x y : SimplexCategoryGenRel} {f g : x ⟶ y}
    (hf : SimplexCategoryGenRel.P_δ f)
    (hg : SimplexCategoryGenRel.P_δ g)
    (hmap : SimplexCategoryGenRel.toSimplexCategory.map f =
      SimplexCategoryGenRel.toSimplexCategory.map g) :
    f = g := by
  have hf' : SimplexCategoryGenRel.faces.multiplicativeClosure' f := by
    rw [← MorphismProperty.multiplicativeClosure_eq_multiplicativeClosure']
    exact hf
  obtain ⟨L, m, r, h₁, h₂, h, hL, hf⟩ :=
    exists_normal_form_P_δ f hf'
  subst y
  subst x
  have hg' : SimplexCategoryGenRel.faces.multiplicativeClosure' g := by
    rw [← MorphismProperty.multiplicativeClosure_eq_multiplicativeClosure']
    exact hg
  obtain ⟨K, m', r', h₁', h₂', h', hK, hg⟩ :=
    exists_normal_form_P_δ g hg'
  have hr : r = r' := by
    have := congrArg SimplexCategoryGenRel.len h₁'
    simpa using this.symm
  have hm : m = m' := by
    have := congrArg SimplexCategoryGenRel.len h₂'
    simpa using this
  have hK₀ : m + K.length = r := by
    omega
  subst r'
  subst m'
  cases hr
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id] at hf hg
  have hL' : m + L.length = m + K.length := h
  have hK' : m + K.length = m + K.length := rfl
  rw [hf, hg] at hmap
  have hmap' : SimplexCategoryGenRel.toSimplexCategory.map
        (standardδ L (m₁ := m) (m₂ := m + K.length) hL') =
      SimplexCategoryGenRel.toSimplexCategory.map
        (standardδ K (m₁ := m) (m₂ := m + K.length) hK') := by
    convert hmap using 1 <;> rfl
  have hLK : L = K :=
    standardδ_list_eq_of_map_eq hL hK hL' hK' hmap'
  cases hLK
  exact hf.trans hg.symm

theorem toSimplexCategory_is_equivalence :
    Functor.IsEquivalence SimplexCategoryGenRel.toSimplexCategory := by
  refine { faithful := ?_, full := ?_, essSurj := ?_ }
  · constructor
    intro X Y f g h
    obtain ⟨z, e, m, he, hm, hfac⟩ :=
      SimplexCategoryGenRel.exists_P_σ_P_δ_factorization f
    obtain ⟨z', e', m', he', hm', hfac'⟩ :=
      SimplexCategoryGenRel.exists_P_σ_P_δ_factorization g
    letI : IsSplitEpi
        (SimplexCategoryGenRel.toSimplexCategory.map e) :=
      SimplexCategoryGenRel.isSplitEpi_toSimplexCategory_map_of_P_σ he
    letI : Epi (SimplexCategoryGenRel.toSimplexCategory.map e) := inferInstance
    letI : IsSplitMono
        (SimplexCategoryGenRel.toSimplexCategory.map m) :=
      SimplexCategoryGenRel.isSplitMono_toSimplexCategory_map_of_P_δ hm
    letI : Mono (SimplexCategoryGenRel.toSimplexCategory.map m) := inferInstance
    letI : IsSplitEpi
        (SimplexCategoryGenRel.toSimplexCategory.map e') :=
      SimplexCategoryGenRel.isSplitEpi_toSimplexCategory_map_of_P_σ he'
    letI : Epi (SimplexCategoryGenRel.toSimplexCategory.map e') := inferInstance
    letI : IsSplitMono
        (SimplexCategoryGenRel.toSimplexCategory.map m') :=
      SimplexCategoryGenRel.isSplitMono_toSimplexCategory_map_of_P_δ hm'
    letI : Mono (SimplexCategoryGenRel.toSimplexCategory.map m') := inferInstance
    have hfac_map :
        SimplexCategoryGenRel.toSimplexCategory.map e ≫
            SimplexCategoryGenRel.toSimplexCategory.map m =
          SimplexCategoryGenRel.toSimplexCategory.map f := by
      rw [← SimplexCategoryGenRel.toSimplexCategory.map_comp, hfac]
    have hfac_map' :
        SimplexCategoryGenRel.toSimplexCategory.map e' ≫
            SimplexCategoryGenRel.toSimplexCategory.map m' =
          SimplexCategoryGenRel.toSimplexCategory.map g := by
      rw [← SimplexCategoryGenRel.toSimplexCategory.map_comp, hfac']
    have himg : Limits.image
        (SimplexCategoryGenRel.toSimplexCategory.map f) =
      SimplexCategoryGenRel.toSimplexCategory.obj z :=
      SimplexCategory.image_eq hfac_map
    have himg' : Limits.image
        (SimplexCategoryGenRel.toSimplexCategory.map g) =
      SimplexCategoryGenRel.toSimplexCategory.obj z' :=
      SimplexCategory.image_eq hfac_map'
    have hz : z = z' := by
      apply SimplexCategoryGenRel.ext
      have hz_obj : SimplexCategoryGenRel.toSimplexCategory.obj z =
          SimplexCategoryGenRel.toSimplexCategory.obj z' := by
        calc
          SimplexCategoryGenRel.toSimplexCategory.obj z =
              Limits.image
                (SimplexCategoryGenRel.toSimplexCategory.map f) := himg.symm
          _ = Limits.image
                (SimplexCategoryGenRel.toSimplexCategory.map g) := by rw [h]
          _ = SimplexCategoryGenRel.toSimplexCategory.obj z' := himg'
      have := congrArg SimplexCategory.len hz_obj
      simpa only [SimplexCategoryGenRel.toSimplexCategory_len] using this
    subst z'
    let eI := SimplexCategoryGenRel.toSimplexCategory.map e ≫ eqToHom himg.symm
    let eI' := SimplexCategoryGenRel.toSimplexCategory.map e' ≫
      eqToHom himg'.symm ≫ Limits.image.eqToHom h.symm
    let iI := eqToHom himg ≫ SimplexCategoryGenRel.toSimplexCategory.map m
    let iI' := Limits.image.eqToHom h ≫ eqToHom himg' ≫
      SimplexCategoryGenRel.toSimplexCategory.map m'
    letI : Epi eI := by
      dsimp [eI]
      infer_instance
    letI : Mono iI := by
      dsimp [iI]
      infer_instance
    letI : Epi eI' := by
      dsimp [eI']
      infer_instance
    letI : Mono iI' := by
      dsimp [iI']
      infer_instance
    have hfacI : eI ≫ iI =
        SimplexCategoryGenRel.toSimplexCategory.map f := by
      simpa [eI, iI, Category.assoc] using hfac_map
    have hfacI' : eI' ≫ iI' =
        SimplexCategoryGenRel.toSimplexCategory.map f := by
      have ht : eqToHom himg'.symm ≫ Limits.image.eqToHom h.symm ≫
          Limits.image.eqToHom h ≫ eqToHom himg' = 𝟙 _ := by
        apply SimplexCategory.eq_id_of_isIso
      have htm : eqToHom himg'.symm ≫ Limits.image.eqToHom h.symm ≫
          Limits.image.eqToHom h ≫ eqToHom himg' ≫
            SimplexCategoryGenRel.toSimplexCategory.map m' =
          SimplexCategoryGenRel.toSimplexCategory.map m' := by
        calc
          eqToHom himg'.symm ≫ Limits.image.eqToHom h.symm ≫
                Limits.image.eqToHom h ≫ eqToHom himg' ≫
              SimplexCategoryGenRel.toSimplexCategory.map m' =
            (eqToHom himg'.symm ≫ Limits.image.eqToHom h.symm ≫
              Limits.image.eqToHom h ≫ eqToHom himg') ≫
                SimplexCategoryGenRel.toSimplexCategory.map m' := by
              simp only [Category.assoc]
          _ = SimplexCategoryGenRel.toSimplexCategory.map m' := by
            rw [ht, Category.id_comp]
      have hcomp : eI' ≫ iI' =
          SimplexCategoryGenRel.toSimplexCategory.map g := by
        dsimp [eI', iI']
        simp only [Category.assoc]
        rw [htm]
        exact hfac_map'
      exact hcomp.trans h.symm
    have he_factor := SimplexCategory.factorThruImage_eq hfacI
    have he_factor' := SimplexCategory.factorThruImage_eq hfacI'
    have heI_eq : eI = eI' := he_factor.symm.trans he_factor'
    have he_map : SimplexCategoryGenRel.toSimplexCategory.map e =
        SimplexCategoryGenRel.toSimplexCategory.map e' := by
      have ht : eqToHom himg'.symm ≫ Limits.image.eqToHom h.symm ≫
          eqToHom himg = 𝟙 _ := by
        apply SimplexCategory.eq_id_of_isIso
      have h' := congrArg (fun q => q ≫ eqToHom himg) heI_eq
      simpa [eI, eI', Category.assoc, ht] using h'
    have hm_factor := SimplexCategory.image_ι_eq hfacI
    have hm_factor' := SimplexCategory.image_ι_eq hfacI'
    have hmI_eq : iI = iI' := hm_factor.symm.trans hm_factor'
    have hm_map : SimplexCategoryGenRel.toSimplexCategory.map m =
        SimplexCategoryGenRel.toSimplexCategory.map m' := by
      have ht : eqToHom himg.symm ≫ Limits.image.eqToHom h ≫
          eqToHom himg' = 𝟙 _ := by
        apply SimplexCategory.eq_id_of_isIso
      have h' := congrArg (fun q => eqToHom himg.symm ≫ q) hmI_eq
      have htm : eqToHom himg.symm ≫ Limits.image.eqToHom h ≫
          eqToHom himg' ≫ SimplexCategoryGenRel.toSimplexCategory.map m' =
        SimplexCategoryGenRel.toSimplexCategory.map m' := by
        calc
          eqToHom himg.symm ≫ Limits.image.eqToHom h ≫
                eqToHom himg' ≫ SimplexCategoryGenRel.toSimplexCategory.map m' =
            (eqToHom himg.symm ≫ Limits.image.eqToHom h ≫
              eqToHom himg') ≫
                SimplexCategoryGenRel.toSimplexCategory.map m' := by
              simp only [Category.assoc]
          _ = SimplexCategoryGenRel.toSimplexCategory.map m' := by
            rw [ht, Category.id_comp]
      dsimp [iI, iI'] at h'
      rw [htm] at h'
      have ht0 : eqToHom himg.symm ≫ eqToHom himg = 𝟙 _ := by
        apply SimplexCategory.eq_id_of_isIso
      have ht0m : eqToHom himg.symm ≫ eqToHom himg ≫
          SimplexCategoryGenRel.toSimplexCategory.map m =
        SimplexCategoryGenRel.toSimplexCategory.map m := by
        calc
          eqToHom himg.symm ≫ eqToHom himg ≫
                SimplexCategoryGenRel.toSimplexCategory.map m =
            (eqToHom himg.symm ≫ eqToHom himg) ≫
                SimplexCategoryGenRel.toSimplexCategory.map m := by
              simp only [Category.assoc]
          _ = SimplexCategoryGenRel.toSimplexCategory.map m := by
            rw [ht0, Category.id_comp]
      rw [ht0m] at h'
      exact h'
    have he_eq := eq_of_P_σ_map_eq he he' he_map
    have hm_eq := eq_of_P_δ_map_eq hm hm' hm_map
    rw [hfac, hfac', he_eq, hm_eq]
  · constructor
    rintro ⟨n⟩ ⟨m⟩ f
    change (SimplexCategory.mk n ⟶ SimplexCategory.mk m) at f
    obtain ⟨g, hg, _⟩ := every_simplex_morphism_is_generated f
    exact ⟨g, hg⟩
  · constructor
    intro Y
    refine ⟨SimplexCategoryGenRel.mk Y.len, ?_⟩
    exact ⟨eqToIso (by simp)⟩

end Formalization.Books.Simplicial.Unit02
