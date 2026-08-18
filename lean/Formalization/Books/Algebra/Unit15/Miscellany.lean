import Formalization.Books.Algebra.Unit03.BasicNotions
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# Commutative Algebra, Chapter 15: Miscellany

The source section consists of elementary consequences of the basic theory of
commutative rings.  The finite lists in the source are represented by finite
types, and finite free modules are represented by functions on `Fin`.
-/

namespace Formalization.Books.Algebra.Unit15

open Set
open scoped BigOperators

universe u

/-! ## Ideals -/

/- The earlier chapter's equivalence is stronger than the one-sided source
   assertion, so this source-facing form is a direct specialization. -/
theorem product_ideals_in_prime
    {R : Type u} [CommRing R] {I J p : Ideal R} (hp : p.IsPrime)
    (hIJ : I * J ≤ p) : I ≤ p ∨ J ≤ p := by
  exact (Unit03.prime_mul_le_iff hp).mp hIJ

/- The source says that all but two of a finite list of ideals are prime.  A
   finite set of at most two exceptional indices is the uniform encoding,
   including the cases of lists of length zero or one. -/
theorem prime_avoidance
    {R : Type u} [CommRing R] {r : ℕ} (I : Fin r → Ideal R) (J : Ideal R)
    (hJ : ∀ i, ¬ J ≤ I i)
    (hprime : ∃ s : Finset (Fin r), s.card ≤ 2 ∧
      ∀ i, i ∉ s → (I i).IsPrime) :
    ∃ x : R, x ∈ J ∧ ∀ i, x ∉ I i := by
  classical
  rcases hprime with ⟨s, hs, hsp⟩
  by_cases hr : r = 0
  · subst r
    refine ⟨0, J.zero_mem, ?_⟩
    intro i
    exact Fin.elim0 i
  · obtain ⟨a₀⟩ : Nonempty (Fin r) := Fin.pos_iff_nonempty.mp (Nat.pos_of_ne_zero hr)
    have hex : ∃ a b : Fin r, s ⊆ {a, b} := by
      by_cases hse : s = ∅
      · exact ⟨a₀, a₀, by simp [hse]⟩
      · obtain ⟨a, ha⟩ := s.nonempty_iff_ne_empty.mpr hse
        have hcard : (s.erase a).card ≤ 1 := by
          rw [Finset.card_erase_of_mem ha]
          omega
        by_cases he : s.erase a = ∅
        · refine ⟨a, a, ?_⟩
          intro z hz
          by_cases hza : z = a
          · exact Finset.mem_insert.mpr (Or.inl hza)
          · have hz' : z ∈ s.erase a := Finset.mem_erase.mpr ⟨hza, hz⟩
            rw [he] at hz'
            exact False.elim (by simpa using hz')
        · obtain ⟨b, hb⟩ := s.erase a |>.nonempty_iff_ne_empty.mpr he
          refine ⟨a, b, ?_⟩
          intro z hz
          by_cases hza : z = a
          · exact Finset.mem_insert.mpr (Or.inl hza)
          · have hz' : z ∈ s.erase a := Finset.mem_erase.mpr ⟨hza, hz⟩
            have hzb : z = b := (Finset.card_le_one.mp hcard) z hz' b hb
            exact Finset.mem_insert.mpr (Or.inr (by simpa using hzb))
    obtain ⟨a, b, hab⟩ := hex
    by_contra h
    push_neg at h
    have hsub : (J : Set R) ⊆ ⋃ i : Fin r, (I i : Set R) := by
      intro y hy
      obtain ⟨i, hi⟩ := h y hy
      exact Set.mem_iUnion.mpr ⟨i, hi⟩
    have hsub' : (J : Set R) ⊆
        ⋃ i ∈ ((Finset.univ : Finset (Fin r)) : Set (Fin r)), (I i : Set R) := by
      have heq : (⋃ i ∈ ((Finset.univ : Finset (Fin r)) : Set (Fin r)),
          (I i : Set R)) = ⋃ i : Fin r, (I i : Set R) := by
        ext y
        simp
      rw [heq]
      exact hsub
    have hprime' : ∀ i ∈ (Finset.univ : Finset (Fin r)), i ≠ a → i ≠ b →
        (I i).IsPrime := by
      intro i hi hia hib
      apply hsp i
      intro his
      have hiab : i = a ∨ i = b := by
        simpa only [Finset.mem_insert, Finset.mem_singleton] using hab his
      exact hiab.elim hia hib
    rcases (Ideal.subset_union_prime a b hprime').mp hsub' with ⟨i, hi, hJi⟩
    exact hJ i hJi

theorem prime_coset_avoidance
    {R : Type u} [CommRing R] {r : ℕ} (x : R) (I : Ideal R)
    (p : Fin r → Ideal R)
    (hp : ∀ i, (p i).IsPrime)
    (h : ∀ i, ¬ (Set.image (fun y : R => x + y) (I : Set R) ⊆ (p i : Set R))) :
    ∃ y : R, y ∈ I ∧ ∀ i, x + y ∉ p i := by
  classical
  let vals : Finset (Ideal R) := Finset.univ.image p
  let maxs : Finset (Ideal R) := vals.filter (fun q => Maximal (· ∈ vals) q)
  have hmax_prime : ∀ q ∈ maxs, q.IsPrime := by
    intro q hq
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp (Finset.mem_filter.mp hq).1
    exact hp i
  have hmax_coset : ∀ q ∈ maxs,
      ¬ (Set.image (fun y : R => x + y) (I : Set R) ⊆ (q : Set R)) := by
    intro q hq
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp (Finset.mem_filter.mp hq).1
    exact h i
  have hmax_antichain : ∀ q₁ ∈ maxs, ∀ q₂ ∈ maxs, q₁ ≠ q₂ → ¬ q₁ ≤ q₂ := by
    intro q₁ hq₁ q₂ hq₂ hne hle
    exact hne ((Finset.mem_filter.mp hq₁).2.eq_of_le
      (Finset.mem_filter.mp hq₂).1 hle)
  have hind : ∀ t : Finset (Ideal R), t ⊆ maxs →
      ∃ y : R, y ∈ I ∧ ∀ q ∈ t, x + y ∉ q := by
    intro t ht
    induction t using Finset.induction_on with
    | empty =>
        exact ⟨0, I.zero_mem, by simp⟩
    | @insert q t hqt ih =>
        obtain ⟨w, hwI, hw⟩ := ih (fun q' hq' => ht (Finset.mem_insert_of_mem hq'))
        have hq : q ∈ maxs := ht (Finset.mem_insert_self q t)
        by_cases hwi : x + w ∈ q
        · rcases Set.not_subset.mp (hmax_coset q hq) with ⟨u, hu, huq⟩
          rcases hu with ⟨z, hzI, rfl⟩
          have hnot : ∀ q' ∈ t, ¬ q' ≤ q := by
            intro q' hq't
            apply hmax_antichain q' (ht (Finset.mem_insert_of_mem hq't)) q hq
            intro heq
            exact hqt (heq ▸ hq't)
          have hex : ∀ q', ∃ c : R,
              q' ∈ t → c ∈ q' ∧ c ∉ q := by
            intro q'
            by_cases hq't : q' ∈ t
            · obtain ⟨c, hc, hcn⟩ := Set.not_subset.mp (hnot q' hq't)
              exact ⟨c, fun _ => ⟨hc, hcn⟩⟩
            · exact ⟨1, fun hq't' => (hq't hq't').elim⟩
          choose c hc using hex
          let f : R := ∏ q' ∈ t, c q'
          have hfmem : ∀ q' ∈ t, f ∈ q' := by
            intro q' hq'
            exact Ideal.prod_mem q' hq' (hc q' hq' |>.1)
          letI : q.IsPrime := hmax_prime q hq
          have hfnot : f ∉ q := by
            rw [Ideal.IsPrime.prod_mem_iff]
            push_neg
            intro q' hq'
            exact (hc q' hq' |>.2)
          have hdiff : z - w ∉ q := by
            intro hdiff
            apply huq
            have hsum : x + w + (z - w) ∈ q := q.add_mem hwi hdiff
            simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hsum
          have hfdnot : f * (z - w) ∉ q := by
            intro hfd
            exact (‹q.IsPrime›.mul_mem_iff_mem_or_mem.mp hfd).elim hfnot hdiff
          let w' : R := w + f * (z - w)
          refine ⟨w', I.add_mem hwI (I.mul_mem_left f (I.sub_mem hzI hwI)), ?_⟩
          intro q' hq'
          rcases Finset.mem_insert.mp hq' with hqeq | hq't
          · intro hnew
            subst q'
            apply hfdnot
            have hsum : x + w + f * (z - w) ∈ q := by
              simpa [w', add_assoc] using hnew
            have hmem := q.sub_mem hsum hwi
            have heq : x + w + f * (z - w) - (x + w) = f * (z - w) := by
              abel
            rw [heq] at hmem
            exact hmem
          · intro hnew
            apply hw q' hq't
            have hfd : f * (z - w) ∈ q' := by
              simpa [mul_comm] using q'.mul_mem_left (z - w) (hfmem q' hq't)
            have hsum : x + w + f * (z - w) ∈ q' := by
              simpa [w', add_assoc] using hnew
            simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
              q'.sub_mem hsum hfd
        · refine ⟨w, hwI, ?_⟩
          intro q' hq'
          rcases Finset.mem_insert.mp hq' with hqeq | hq't
          · subst q'
            exact hwi
          · exact hw q' hq't
  obtain ⟨y, hyI, hy⟩ := hind maxs (by intro q hq; exact hq)
  refine ⟨y, hyI, ?_⟩
  intro i hi
  obtain ⟨q, hle, hqmax⟩ := vals.exists_le_maximal
    (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩)
  have hq : q ∈ maxs := Finset.mem_filter.mpr ⟨hqmax.1, hqmax⟩
  exact hy q hq (hle hi)

/-! ## Chinese remainder -/

theorem chinese_remainder
    {R ι : Type*} [CommRing R] [Fintype ι] (I : ι → Ideal R)
    (hI : Pairwise (fun i j => I i + I j = ⊤)) :
    (⨅ i, I i = ∏ i, I i) ∧
      Nonempty ((R ⧸ ∏ i, I i) ≃+* (∀ i, R ⧸ I i)) := by
  have hcop : Pairwise (fun i j => IsCoprime (I i) (I j)) := by
    intro i j hij
    apply Ideal.isCoprime_iff_sup_eq.mpr
    exact hI hij
  have hprod : (∏ i, I i) = ⨅ i, I i := by
    simpa using
      (Ideal.prod_eq_iInf_of_pairwise_isCoprime
        (s := (Finset.univ : Finset ι)) (J := I) (by
          intro i hi j hj hij
          exact hcop hij))
  refine ⟨hprod.symm, ⟨(Ideal.quotEquivOfEq hprod).trans
    (Ideal.quotientInfRingEquivPiQuotient I hcop)⟩⟩

theorem chinese_remainder_of_pairwise_distinct_maximal
    {R ι : Type*} [CommRing R] [Fintype ι] (I : ι → Ideal R)
    (hmax : ∀ i, (I i).IsMaximal)
    (hdistinct : Pairwise (fun i j => I i ≠ I j)) :
    (⨅ i, I i = ∏ i, I i) ∧
      Nonempty ((R ⧸ ∏ i, I i) ≃+* (∀ i, R ⧸ I i)) := by
  apply chinese_remainder I
  intro i j hij
  letI : (I i).IsMaximal := hmax i
  letI : (I j).IsMaximal := hmax j
  exact (Ideal.isCoprime_of_isMaximal (hdistinct hij)).sup_eq

/-! ## Determinantal ideals and matrix inverses -/

/- The `rowMinor` construction from the earlier basic-notions chapter is the
   determinant of every square row minor of a rectangular matrix. -/
noncomputable def maximalMinorIdeal
    {R : Type u} [CommRing R] {m n : ℕ}
    (A : Matrix (Fin n) (Fin m) R) : Ideal R :=
  Ideal.span (Set.range (fun S : {s : Finset (Fin n) // s.card = m} =>
    Unit03.rowMinor A S))

theorem matrix_left_inverse_of_mem_maximalMinorIdeal
    {R : Type u} [CommRing R] {m n : ℕ} (hmn : m ≤ n)
    (A : Matrix (Fin n) (Fin m) R) {f : R}
    (hf : f ∈ maximalMinorIdeal A) :
    ∃ B : Matrix (Fin m) (Fin n) R,
      B * A = f • (1 : Matrix (Fin m) (Fin m) R) := by
  classical
  unfold maximalMinorIdeal at hf
  induction hf using Submodule.span_induction with
  | mem f hf =>
      obtain ⟨S, rfl⟩ := hf
      let e : Fin m ↪ Fin n := (S.1.orderEmbOfFin S.2).toEmbedding
      let A_S : Matrix (Fin m) (Fin m) R := A.submatrix e id
      refine ⟨A_S.adjugate *
          (1 : Matrix (Fin n) (Fin n) R).submatrix e (Equiv.refl (Fin n)), ?_⟩
      rw [Matrix.mul_assoc, Matrix.one_submatrix_mul e (Equiv.refl (Fin n)) A]
      simpa [A_S, e, Unit03.rowMinor, Function.comp_def] using
        (Matrix.adjugate_mul A_S)
  | zero =>
      exact ⟨0, by simp⟩
  | add f g hf hg hf' hg' =>
      obtain ⟨Bf, hBf⟩ := hf'
      obtain ⟨Bg, hBg⟩ := hg'
      refine ⟨Bf + Bg, ?_⟩
      rw [Matrix.add_mul, hBf, hBg, add_smul]
  | smul c f hf hf' =>
      obtain ⟨Bf, hBf⟩ := hf'
      refine ⟨c • Bf, ?_⟩
      rw [Matrix.smul_mul, hBf, smul_smul]
      simp [smul_eq_mul]

theorem matrix_left_inverse_power_mem_maximalMinorIdeal
    {R : Type u} [CommRing R] {m n : ℕ} (hmn : m ≤ n)
    (A : Matrix (Fin n) (Fin m) R) {f : R}
    {B : Matrix (Fin m) (Fin n) R}
    (hBA : B * A = f • (1 : Matrix (Fin m) (Fin m) R)) :
    f ^ m ∈ maximalMinorIdeal A := by
  have hdet : f ^ m =
      ∑ S : {s : Finset (Fin n) // s.card = m},
        Unit03.columnMinor B S * Unit03.rowMinor A S := by
    calc
      f ^ m = (f • (1 : Matrix (Fin m) (Fin m) R)).det := by
        simp [Matrix.det_smul]
      _ = (B * A).det := by rw [hBA]
      _ = _ := Unit03.cauchyBinet B A
  rw [maximalMinorIdeal, hdet]
  apply Ideal.sum_mem
  intro S hS
  exact Ideal.mul_mem_left _ _
    (Ideal.subset_span ⟨S, rfl⟩)

/- The first conjunct records the upper block of the displayed product.  The
   second records that every lower entry is, up to sign, the determinant of
   the minor obtained by deleting the corresponding upper row and adjoining
   the corresponding lower row. -/
theorem matrix_right_inverse_block_form
    {R : Type u} [CommRing R] {m n : ℕ} (hmn : m ≤ n)
    (A : Matrix (Fin n) (Fin m) R) :
    let A₁ : Matrix (Fin m) (Fin m) R :=
      A.submatrix (fun i : Fin m => i.castLE hmn) id
    let B : Matrix (Fin m) (Fin m) R := A₁.adjugate
    (∀ i j : Fin m,
        (A * B) (i.castLE hmn) j =
          (A₁.det • (1 : Matrix (Fin m) (Fin m) R)) i j) ∧
      (∀ i : Fin (n - m), ∀ j : Fin m,
        ∃ S : {s : Finset (Fin n) // s.card = m},
          S.1 =
            insert
              (Fin.cast (Nat.add_sub_of_le hmn) (Fin.natAdd m i))
              ((Finset.univ.image (fun k : Fin m => k.castLE hmn)).erase
                (j.castLE hmn)) ∧
            ∃ ε : R, (ε = 1 ∨ ε = -1) ∧
            (A * B)
                (Fin.cast (Nat.add_sub_of_le hmn) (Fin.natAdd m i)) j =
              ε * Unit03.rowMinor A S) := by
  dsimp
  constructor
  · intro i j
    have hsub := Matrix.submatrix_mul A
      (A.submatrix (fun k : Fin m => k.castLE hmn) id).adjugate
      (fun k : Fin m => k.castLE hmn) (Equiv.refl (Fin m)) id
      (Equiv.refl (Fin m)).bijective
    calc
      (A * (A.submatrix (fun k : Fin m => k.castLE hmn) id).adjugate)
          (i.castLE hmn) j =
          ((A * (A.submatrix (fun k : Fin m => k.castLE hmn) id).adjugate).submatrix
            (fun k : Fin m => k.castLE hmn) id) i j := rfl
      _ = ((A.submatrix (fun k : Fin m => k.castLE hmn) id) *
          (A.submatrix (fun k : Fin m => k.castLE hmn) id).adjugate) i j := by
        rw [hsub]
        rfl
      _ = ((A.submatrix (fun k : Fin m => k.castLE hmn) id).det •
          (1 : Matrix (Fin m) (Fin m) R)) i j := by
        rw [Matrix.mul_adjugate]
  · classical
    intro i j
    let u : Fin m → Fin n := fun k => k.castLE hmn
    let l : Fin n := Fin.cast (Nat.add_sub_of_le hmn) (Fin.natAdd m i)
    let T : Finset (Fin n) := (Finset.univ.image u).erase (u j)
    have huinj : Function.Injective u := by
      exact Fin.castLE_injective hmn
    have hu_mem : u j ∈ Finset.univ.image u := by
      exact Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩
    have hl_not : l ∉ Finset.univ.image u := by
      intro hl
      obtain ⟨k, -, hk⟩ := Finset.mem_image.mp hl
      have hval := congrArg Fin.val hk
      simp [l, u] at hval
      omega
    have hTcard : T.card = m - 1 := by
      dsimp [T]
      rw [Finset.card_erase_of_mem hu_mem,
        Finset.card_image_of_injective _ huinj]
      simp
    have hScard : (insert l T).card = m := by
      rw [Finset.card_insert_of_notMem (fun hlT =>
          hl_not ((Finset.erase_subset (u j) (Finset.univ.image u)) hlT)),
        hTcard]
      have hj := j.isLt
      omega
    let S : {s : Finset (Fin n) // s.card = m} := ⟨insert l T, hScard⟩
    refine ⟨S, ?_, ?_⟩
    · simp [S, T, u, l]
    · let C : Matrix (Fin m) (Fin m) R :=
        (A.submatrix u id).updateRow j (A l)
      have hrow : C.det = ∑ k : Fin m, A l k *
          (A.submatrix u id).adjugate k j := by
        calc
          C.det = ∑ k : Fin m, C j k * C.adjugate k j :=
            Matrix.det_eq_sum_mul_adjugate_row C j
          _ = ∑ k : Fin m, A l k *
              (A.submatrix u id).adjugate k j := by
            apply Finset.sum_congr rfl
            intro k hk
            have hcjk : C j k = A l k := by simp [C]
            have hadj : C.adjugate k j =
                (A.submatrix u id).adjugate k j := by
              rw [Matrix.adjugate_apply, Matrix.adjugate_apply]
              congr 1
              ext r' s'
              by_cases hr' : r' = j
              · subst r'
                simp [C]
              · simp [C, hr']
            rw [hcjk, hadj]
      let eS : Fin m → Fin n := fun k => (S.1.orderIsoOfFin S.2 k : Fin n)
      let D : Matrix (Fin m) (Fin m) R := A.submatrix eS id
      let eC : Fin m → Fin n := fun k => if k = j then l else u k
      have heC_mem : ∀ k : Fin m, eC k ∈ S.1 := by
        intro k
        by_cases hkj : k = j
        · simp [eC, hkj, S]
        · have hku : u k ∈ T := by
            apply Finset.mem_erase.mpr
            refine ⟨?_, Finset.mem_image.mpr ⟨k, Finset.mem_univ _, rfl⟩⟩
            intro hku
            exact hkj (huinj hku)
          simpa [S, eC, hkj] using Finset.mem_insert_of_mem hku
      have heC_inj : Function.Injective eC := by
        intro k k' hkk'
        by_cases hkj : k = j <;> by_cases hk'j : k' = j
        · exact hkj.trans hk'j.symm
        · subst k
          have : l ∈ Finset.univ.image u := by
            have heq : l = u k' := by simpa [eC, hk'j] using hkk'
            exact Finset.mem_image.mpr ⟨k', Finset.mem_univ _, heq.symm⟩
          exact (hl_not this).elim
        · subst k'
          have : l ∈ Finset.univ.image u := by
            exact Finset.mem_image.mpr ⟨k, Finset.mem_univ _,
              by simpa [eC, hkj] using hkk'⟩
          exact (hl_not this).elim
        · exact huinj (by simpa [eC, hkj, hk'j] using hkk')
      let eC' : Fin m → S.1 := fun k => ⟨eC k, heC_mem k⟩
      have heC_surj : Function.Surjective eC' := by
        intro z
        by_cases hzl : (z : Fin n) = l
        · refine ⟨j, ?_⟩
          apply Subtype.ext
          change eC j = (z : Fin n)
          simp [eC, hzl]
        · have hzT : (z : Fin n) ∈ T := by
            exact (Finset.mem_insert.mp z.property).resolve_left hzl
          obtain ⟨k, hk⟩ := Finset.mem_image.mp (Finset.mem_erase.mp hzT).2
          have hkj : k ≠ j := by
            intro hkj
            subst k
            apply (Finset.mem_erase.mp hzT).1
            exact hk.2.symm
          refine ⟨k, ?_⟩
          apply Subtype.ext
          change eC k = (z : Fin n)
          simpa [eC, hkj] using hk
      have heC'_inj : Function.Injective eC' := by
        intro k k' hkk'
        apply heC_inj
        exact congrArg (fun z : S.1 => (z : Fin n)) hkk'
      let eCeq : Fin m ≃ S.1 := Equiv.ofBijective eC' ⟨heC'_inj, heC_surj⟩
      let eSeq : Fin m ≃ S.1 := S.1.orderIsoOfFin S.2
      let σ : Equiv.Perm (Fin m) := eCeq.trans eSeq.symm
      have hCD : C = D.submatrix σ id := by
        ext k c
        change (A.submatrix u id).updateRow j (A l) k c =
          A (eS (eSeq.symm (eCeq k))) c
        have hindex : eS (eSeq.symm (eCeq k)) = eC k := by
          change (eSeq (eSeq.symm (eCeq k)) : Fin n) = eC k
          exact congrArg (fun z : S.1 => (z : Fin n))
            (eSeq.apply_symm_apply (eCeq k))
        rw [hindex]
        by_cases hkj : k = j <;> simp [C, eC, hkj]
      have hrowminor : Unit03.rowMinor A S = D.det := by
        rfl
      have hdet : C.det = Equiv.Perm.sign σ * D.det := by
        rw [hCD, Matrix.det_permute]
      have hprod :
          (A * (A.submatrix u id).adjugate) l j = C.det := by
        rw [Matrix.mul_apply]
        simpa [hrow] using hrow.symm
      rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with hsign | hsign
      · refine ⟨1, Or.inl rfl, ?_⟩
        rw [hprod, hdet, hsign, hrowminor]
        simp
      · refine ⟨-1, Or.inr rfl, ?_⟩
        rw [hprod, hdet, hsign, hrowminor]
        simp

/-! ## Finite free rank -/

theorem module_map_from_fin_generators_not_injective
    {R M : Type*} [CommRing R] [Nontrivial R]
    [AddCommGroup M] [Module R M] {n : ℕ} (hn : 1 ≤ n)
    (hM : ∃ k : ℕ, k < n ∧
      ∃ g : (Fin k → R) →ₗ[R] M, Function.Surjective g)
    (f : (Fin n → R) →ₗ[R] M) :
    LinearMap.ker f ≠ ⊥ := by
  rcases hM with ⟨k, hk, g, hg⟩
  intro hker
  have hf_inj : Function.Injective f := LinearMap.ker_eq_bot.mp hker
  obtain ⟨l, hl⟩ := Module.projective_lifting_property g f hg
  have hl_inj : Function.Injective l := by
    intro x y hxy
    apply hf_inj
    calc
      f x = (g.comp l) x := by rw [hl]
      _ = g (l x) := rfl
      _ = g (l y) := congrArg g hxy
      _ = (g.comp l) y := rfl
      _ = f y := by rw [hl]
  exact (Nat.not_lt_of_ge (le_of_fin_injective R l hl_inj)) hk

theorem fin_free_module_rank_unique
    {R : Type*} [CommRing R] [Nontrivial R] {n m : ℕ}
    (e : (Fin n → R) ≃ₗ[R] (Fin m → R)) : n = m := by
  exact eq_of_fin_equiv R e

end Formalization.Books.Algebra.Unit15
