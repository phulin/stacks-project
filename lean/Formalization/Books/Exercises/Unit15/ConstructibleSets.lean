import Mathlib.RingTheory.Nullstellensatz
import Mathlib.Data.Set.Finite.Range

/-!
# Exercises, Chapter 15: Constructible sets

This file records the definitions and theorem interfaces for the first two
exercises.  Affine algebraic sets use Mathlib's multivariate-polynomial
zero-locus API, while the finite-union and disjoint-union statements retain
the source's description by basic pieces.
-/

namespace Formalization.Books.Exercises.Unit15

open Set

universe u v

noncomputable section

/-! ## Algebraic sets -/

/- The source writes `k[x₁, ..., xₙ]`; the canonical Lean presentation is
   `MvPolynomial (Fin n) k`. -/

/-- Evaluation of a polynomial at a point of affine `n`-space. -/
def polynomialEvaluation {k : Type u} [CommSemiring k] {n : ℕ}
    (f : MvPolynomial (Fin n) k) (x : Fin n → k) : k :=
  MvPolynomial.eval x f

/-- The common zero locus of a collection of polynomials in affine space. -/
def polynomialZeroSet (k : Type u) [Field k] [IsAlgClosed k] (n : ℕ)
    (S : Set (MvPolynomial (Fin n) k)) : Set (Fin n → k) :=
  MvPolynomial.zeroLocus k (Ideal.span S)

/-- An algebraic set is the common zero locus of a collection of polynomials. -/
def IsAlgebraicSet (k : Type u) [Field k] [IsAlgClosed k] (n : ℕ)
    (Z : Set (Fin n → k)) : Prop :=
  ∃ S : Set (MvPolynomial (Fin n) k), Z = polynomialZeroSet k n S

/-! ### Exercise `finite-nr-equations` -/

/-- Every algebraic set is the zero locus of finitely many polynomials. -/
theorem exists_finite_polynomials_eq_polynomialZeroSet
    {k : Type u} [Field k] [IsAlgClosed k] (n : ℕ)
    {Z : Set (Fin n → k)} (hZ : IsAlgebraicSet k n Z) :
    ∃ S : Set (MvPolynomial (Fin n) k), S.Finite ∧
      Z = polynomialZeroSet k n S := by
  rcases hZ with ⟨S, rfl⟩
  obtain ⟨T, hT⟩ := Ideal.fg_of_isNoetherianRing (Ideal.span S)
  refine ⟨(T : Set (MvPolynomial (Fin n) k)), T.finite_toSet, ?_⟩
  simp only [polynomialZeroSet]
  rw [hT]

/-! ## Constructible sets -/

/-- Data for one basic constructible piece `Z ∩ {f ≠ 0}`. -/
structure ConstructiblePiece (k : Type u) [Field k] [IsAlgClosed k] (n : ℕ) where
  zeroSet : Set (Fin n → k)
  polynomial : MvPolynomial (Fin n) k
  zeroSet_isAlgebraic : IsAlgebraicSet k n zeroSet

/-- The subset represented by a basic constructible piece. -/
def ConstructiblePiece.toSet {k : Type u} [Field k] [IsAlgClosed k] {n : ℕ}
    (P : ConstructiblePiece k n) : Set (Fin n → k) :=
  P.zeroSet ∩ {x | polynomialEvaluation P.polynomial x ≠ 0}

/- A finite set of `ConstructiblePiece`s gives the source's finite union of
   sets `Z ∩ {f ≠ 0}`. -/
/-- A subset of affine space is constructible when it is a finite union of
basic constructible pieces. -/
def IsConstructible (k : Type u) [Field k] [IsAlgClosed k] (n : ℕ)
    (E : Set (Fin n → k)) : Prop :=
  ∃ T : Set (ConstructiblePiece k n), T.Finite ∧
    E = ⋃ P ∈ T, P.toSet

private theorem isConstructible_finite_iUnion_aux
    {k : Type u} [Field k] [IsAlgClosed k] (n : ℕ)
    {ι : Type v} (T : Set ι) (hT : T.Finite)
    (E : ι → Set (Fin n → k))
    (hE : ∀ i ∈ T, IsConstructible k n (E i)) :
    IsConstructible k n (⋃ i ∈ T, E i) := by
  classical
  let U : ι → Set (ConstructiblePiece k n) := fun i =>
    if hi : i ∈ T then Classical.choose (hE i hi) else ∅
  have hUfin : ∀ i ∈ T, (U i).Finite := by
    intro i hi
    simp only [U, dif_pos hi]
    exact (Classical.choose_spec (hE i hi)).1
  have hUeq : ∀ i ∈ T, E i = ⋃ P ∈ U i, P.toSet := by
    intro i hi
    simp only [U, dif_pos hi]
    exact (Classical.choose_spec (hE i hi)).2
  refine ⟨⋃ i ∈ T, U i, hT.biUnion hUfin, ?_⟩
  ext x
  constructor
  · intro hx
    rcases mem_iUnion.mp hx with ⟨i, hx⟩
    rcases mem_iUnion.mp hx with ⟨hi, hx⟩
    rw [hUeq i hi] at hx
    rcases mem_iUnion.mp hx with ⟨P, hx⟩
    rcases mem_iUnion.mp hx with ⟨hP, hx⟩
    have hPbig : P ∈ ⋃ i ∈ T, U i :=
      mem_iUnion.mpr ⟨i, mem_iUnion.mpr ⟨hi, hP⟩⟩
    exact mem_iUnion.mpr ⟨P, mem_iUnion.mpr ⟨hPbig, hx⟩⟩
  · intro hx
    rcases mem_iUnion.mp hx with ⟨P, hx⟩
    rcases mem_iUnion.mp hx with ⟨hP, hx⟩
    rcases mem_iUnion.mp hP with ⟨i, hP⟩
    rcases mem_iUnion.mp hP with ⟨hi, hP⟩
    have hEi : x ∈ E i :=
      (hUeq i hi).symm ▸ mem_iUnion.mpr ⟨P, mem_iUnion.mpr ⟨hP, hx⟩⟩
    exact mem_iUnion.mpr ⟨i, mem_iUnion.mpr ⟨hi, hEi⟩⟩

private theorem isConstructible_finite_iInter_aux
    {k : Type u} [Field k] [IsAlgClosed k] (n : ℕ)
    {ι : Type v} (T : Set ι) (hT : T.Finite)
    (E : ι → Set (Fin n → k))
    (hE : ∀ i ∈ T, IsConstructible k n (E i)) :
    IsConstructible k n (⋂ i ∈ T, E i) := by
  have interAlg : ∀ P Q : ConstructiblePiece k n,
      IsAlgebraicSet k n (P.zeroSet ∩ Q.zeroSet) := by
    intro P Q
    rcases P.zeroSet_isAlgebraic with ⟨S, hS⟩
    rcases Q.zeroSet_isAlgebraic with ⟨R, hR⟩
    refine ⟨S ∪ R, ?_⟩
    rw [hS, hR]
    unfold polynomialZeroSet
    simp only [MvPolynomial.zeroLocus_span]
    ext x
    simp only [mem_inter_iff, mem_union]
    constructor
    · rintro ⟨hS, hR⟩ p (hp | hp)
      · exact hS p hp
      · exact hR p hp
    · intro h
      exact ⟨fun p hp => h p (Or.inl hp), fun p hp => h p (Or.inr hp)⟩
  let interPiece : ConstructiblePiece k n → ConstructiblePiece k n → ConstructiblePiece k n :=
    fun P Q =>
      { zeroSet := P.zeroSet ∩ Q.zeroSet
        polynomial := P.polynomial * Q.polynomial
        zeroSet_isAlgebraic := interAlg P Q }
  have hInterPiece : ∀ P Q, (interPiece P Q).toSet = P.toSet ∩ Q.toSet := by
    intro P Q
    ext x
    simp [interPiece, ConstructiblePiece.toSet, polynomialEvaluation]
    constructor
    · rintro ⟨⟨hP, hQ⟩, hfP, hfQ⟩
      exact ⟨⟨hP, hfP⟩, hQ, hfQ⟩
    · rintro ⟨⟨hP, hfP⟩, hQ, hfQ⟩
      exact ⟨⟨hP, hQ⟩, hfP, hfQ⟩
  have hInter : ∀ A B : Set (Fin n → k),
      IsConstructible k n A → IsConstructible k n B →
        IsConstructible k n (A ∩ B) := by
    intro A B hA hB
    rcases hA with ⟨U, hU, hAU⟩
    rcases hB with ⟨V, hV, hBV⟩
    let F : (ConstructiblePiece k n × ConstructiblePiece k n) → ConstructiblePiece k n :=
      fun pq => interPiece pq.1 pq.2
    have hUV : (U ×ˢ V).Finite := by
      exact @Finite.Set.finite_prod _ _ U V hU hV
    refine ⟨F '' (U ×ˢ V), hUV.image F, ?_⟩
    rw [hAU, hBV]
    ext x
    constructor
    · intro hx
      rcases hx with ⟨hxA, hxB⟩
      rcases mem_iUnion.mp hxA with ⟨P, hxA⟩
      rcases mem_iUnion.mp hxA with ⟨hP, hxA⟩
      rcases mem_iUnion.mp hxB with ⟨Q, hxB⟩
      rcases mem_iUnion.mp hxB with ⟨hQ, hxB⟩
      have hxPQ : x ∈ (interPiece P Q).toSet := by
        rw [hInterPiece]
        exact ⟨hxA, hxB⟩
      have hF : interPiece P Q ∈ F '' (U ×ˢ V) := by
        change ∃ pq ∈ U ×ˢ V, F pq = interPiece P Q
        exact ⟨(P, Q), ⟨hP, hQ⟩, rfl⟩
      exact mem_iUnion.mpr ⟨interPiece P Q, mem_iUnion.mpr ⟨hF, hxPQ⟩⟩
    · intro hx
      rcases mem_iUnion.mp hx with ⟨R, hx⟩
      rcases mem_iUnion.mp hx with ⟨hR, hx⟩
      change ∃ pq ∈ U ×ˢ V, F pq = R at hR
      rcases hR with ⟨⟨P, Q⟩, ⟨hP, hQ⟩, hFR⟩
      subst R
      rw [hInterPiece] at hx
      exact ⟨mem_iUnion.mpr ⟨P, mem_iUnion.mpr ⟨hP, hx.1⟩⟩,
        mem_iUnion.mpr ⟨Q, mem_iUnion.mpr ⟨hQ, hx.2⟩⟩⟩
  let univPiece : ConstructiblePiece k n :=
    { zeroSet := Set.univ
      polynomial := 1
      zeroSet_isAlgebraic := by
        refine ⟨∅, ?_⟩
        simp [polynomialZeroSet] }
  have huniv : IsConstructible k n (Set.univ : Set (Fin n → k)) := by
    refine ⟨{univPiece}, finite_singleton _, ?_⟩
    ext x
    simp [univPiece, ConstructiblePiece.toSet, polynomialEvaluation]
  revert hE
  induction T, hT using Set.Finite.induction_on with
  | empty =>
      intro hE
      simpa using huniv
  | @insert a T ha hT ih =>
      intro hE
      have haE : IsConstructible k n (E a) := hE a (by simp)
      have hTE : ∀ i ∈ T, IsConstructible k n (E i) := by
        intro i hi
        exact hE i (by simp [hi])
      have hsmall := ih hTE
      have hset : (⋂ i ∈ insert a T, E i) = E a ∩ ⋂ i ∈ T, E i := by
        ext x
        simp
      rw [hset]
      exact hInter _ _ haE hsmall

/-! ### Exercise `constructible-classical` -/

/-- The complement of a constructible set is constructible. -/
theorem isConstructible_compl
    {k : Type u} [Field k] [IsAlgClosed k] (n : ℕ)
    {E : Set (Fin n → k)} (hE : IsConstructible k n E) :
    IsConstructible k n Eᶜ := by
  have hPieceCompl : ∀ P : ConstructiblePiece k n,
      IsConstructible k n (P.toSet)ᶜ := by
    intro P
    obtain ⟨S, hSfin, hS⟩ :=
      exists_finite_polynomials_eq_polynomialZeroSet n P.zeroSet_isAlgebraic
    let A : MvPolynomial (Fin n) k → ConstructiblePiece k n := fun f =>
      { zeroSet := Set.univ
        polynomial := f
        zeroSet_isAlgebraic := by
          refine ⟨∅, ?_⟩
          simp [polynomialZeroSet] }
    let B : ConstructiblePiece k n :=
      { zeroSet := polynomialZeroSet k n {P.polynomial}
        polynomial := 1
        zeroSet_isAlgebraic := ⟨{P.polynomial}, rfl⟩ }
    refine ⟨A '' S ∪ {B}, (hSfin.image A).union (finite_singleton B), ?_⟩
    change (P.zeroSet ∩ {x | polynomialEvaluation P.polynomial x ≠ 0})ᶜ =
      ⋃ Q ∈ A '' S ∪ {B}, Q.toSet
    rw [hS]
    ext x
    simp [ConstructiblePiece.toSet, A, B, polynomialZeroSet,
      MvPolynomial.zeroLocus_span, polynomialEvaluation]
    constructor
    · intro h
      by_cases hzero : MvPolynomial.eval x P.polynomial = 0
      · exact Or.inl hzero
      · right
        by_contra hnot
        apply hzero
        apply h
        intro p hp
        by_contra hnon
        exact hnot ⟨p, hp, hnon⟩
    · rintro (hP | ⟨p, hp, hnp⟩) hS'
      · exact hP
      · exact False.elim (hnp (hS' p hp))
  rcases hE with ⟨T, hT, hET⟩
  have hI : IsConstructible k n (⋂ P ∈ T, (P.toSet)ᶜ) :=
    isConstructible_finite_iInter_aux n T hT (fun P => (P.toSet)ᶜ)
      (fun P hP => hPieceCompl P)
  rw [hET]
  simpa only [compl_iUnion] using hI

/-- A finite union of constructible sets is constructible. -/
theorem isConstructible_finite_iUnion
    {k : Type u} [Field k] [IsAlgClosed k] (n : ℕ)
    {ι : Type v} (T : Set ι) (hT : T.Finite)
    (E : ι → Set (Fin n → k))
    (hE : ∀ i ∈ T, IsConstructible k n (E i)) :
    IsConstructible k n (⋃ i ∈ T, E i) :=
  isConstructible_finite_iUnion_aux n T hT E hE

/-- A finite intersection of constructible sets is constructible. -/
theorem isConstructible_finite_iInter
    {k : Type u} [Field k] [IsAlgClosed k] (n : ℕ)
    {ι : Type v} (T : Set ι) (hT : T.Finite)
    (E : ι → Set (Fin n → k))
    (hE : ∀ i ∈ T, IsConstructible k n (E i)) :
    IsConstructible k n (⋂ i ∈ T, E i) :=
  isConstructible_finite_iInter_aux n T hT E hE

private theorem isAlgebraic_inter
    {k : Type u} [Field k] [IsAlgClosed k] (n : ℕ)
    (A B : Set (Fin n → k)) (hA : IsAlgebraicSet k n A)
    (hB : IsAlgebraicSet k n B) : IsAlgebraicSet k n (A ∩ B) := by
  rcases hA with ⟨S, hS⟩
  rcases hB with ⟨R, hR⟩
  refine ⟨S ∪ R, ?_⟩
  rw [hS, hR]
  unfold polynomialZeroSet
  simp only [MvPolynomial.zeroLocus_span]
  ext x
  simp only [mem_inter_iff, mem_union]
  constructor
  · rintro ⟨hS, hR⟩ p (hp | hp)
    · exact hS p hp
    · exact hR p hp
  · intro h
    exact ⟨fun p hp => h p (Or.inl hp), fun p hp => h p (Or.inr hp)⟩

private def intersectConstructiblePieces
    {k : Type u} [Field k] [IsAlgClosed k] {n : ℕ}
    (P Q : ConstructiblePiece k n) : ConstructiblePiece k n :=
  { zeroSet := P.zeroSet ∩ Q.zeroSet
    polynomial := P.polynomial * Q.polynomial
    zeroSet_isAlgebraic :=
      isAlgebraic_inter n _ _ P.zeroSet_isAlgebraic Q.zeroSet_isAlgebraic }

private theorem intersectConstructiblePieces_toSet
    {k : Type u} [Field k] [IsAlgClosed k] {n : ℕ}
    (P Q : ConstructiblePiece k n) :
    (intersectConstructiblePieces P Q).toSet = P.toSet ∩ Q.toSet := by
  ext x
  simp [intersectConstructiblePieces, ConstructiblePiece.toSet,
    polynomialEvaluation]
  constructor
  · rintro ⟨⟨hP, hQ⟩, hfP, hfQ⟩
    exact ⟨⟨hP, hfP⟩, hQ, hfQ⟩
  · rintro ⟨⟨hP, hfP⟩, hQ, hfQ⟩
    exact ⟨⟨hP, hQ⟩, hfP, hfQ⟩

private theorem exists_piece_for_finite_intersection
    {k : Type u} [Field k] [IsAlgClosed k] (n : ℕ)
    (U : Set (ConstructiblePiece k n)) (hU : U.Finite) :
    ∃ P : ConstructiblePiece k n, P.toSet = ⋂ Q ∈ U, Q.toSet := by
  classical
  let univPiece : ConstructiblePiece k n :=
    { zeroSet := Set.univ
      polynomial := 1
      zeroSet_isAlgebraic := by
        refine ⟨∅, ?_⟩
        simp [polynomialZeroSet] }
  induction U, hU using Set.Finite.induction_on with
  | empty =>
      refine ⟨univPiece, ?_⟩
      simp [univPiece, ConstructiblePiece.toSet, polynomialEvaluation]
  | @insert P U hP hU ih =>
      obtain ⟨Q, hQ⟩ := ih
      refine ⟨intersectConstructiblePieces P Q, ?_⟩
      rw [intersectConstructiblePieces_toSet, hQ]
      ext x
      simp

private theorem exists_finite_pairwiseDisjoint_zeroSet_compl
    {k : Type u} [Field k] [IsAlgClosed k] (n : ℕ)
    (S : Set (MvPolynomial (Fin n) k)) (hS : S.Finite) :
    ∃ U : Set (ConstructiblePiece k n), U.Finite ∧
      ((polynomialZeroSet k n S)ᶜ = ⋃ P ∈ U, P.toSet) ∧
        U.PairwiseDisjoint (fun P : ConstructiblePiece k n => P.toSet) := by
  classical
  induction S, hS using Set.Finite.induction_on with
  | empty =>
      refine ⟨∅, finite_empty, ?_, pairwiseDisjoint_empty⟩
      simp [polynomialZeroSet]
  | @insert p S hp hS ih =>
      obtain ⟨U, hUfin, hUeq, hUdis⟩ := ih
      let Q : ConstructiblePiece k n :=
        { zeroSet := polynomialZeroSet k n S
          polynomial := p
          zeroSet_isAlgebraic := ⟨S, rfl⟩ }
      have hQ : Q.toSet = polynomialZeroSet k n S ∩
          {x | polynomialEvaluation p x ≠ 0} := by
        rfl
      refine ⟨insert Q U, hUfin.insert _, ?_, ?_⟩
      · have hVinsert : polynomialZeroSet k n (insert p S) =
            polynomialZeroSet k n S ∩ {x | polynomialEvaluation p x = 0} := by
          ext x
          simp [polynomialZeroSet, MvPolynomial.zeroLocus_span,
            polynomialEvaluation, and_comm]
        rw [hVinsert]
        ext x
        constructor
        · intro hx
          by_cases hxS : x ∈ polynomialZeroSet k n S
          · by_cases hxp : polynomialEvaluation p x = 0
            · exact (hx ⟨hxS, hxp⟩).elim
            · refine mem_iUnion.mpr ⟨Q,
                mem_iUnion.mpr ⟨mem_insert _ _, ?_⟩⟩
              exact ⟨hxS, hxp⟩
          · have hxSc : x ∈ (polynomialZeroSet k n S)ᶜ := hxS
            rw [hUeq] at hxSc
            rcases mem_iUnion.mp hxSc with ⟨R, hxR⟩
            rcases mem_iUnion.mp hxR with ⟨hR, hxR⟩
            exact mem_iUnion.mpr ⟨R,
              mem_iUnion.mpr ⟨mem_insert_iff.mpr (Or.inr hR), hxR⟩⟩
        · intro hx
          rcases mem_iUnion.mp hx with ⟨R, hxR⟩
          rcases mem_iUnion.mp hxR with ⟨hR, hxR⟩
          rcases mem_insert_iff.mp hR with rfl | hR
          · intro htarget
            exact hxR.2 htarget.2
          · have hxSc : x ∈ (polynomialZeroSet k n S)ᶜ := by
              rw [hUeq]
              exact mem_iUnion.mpr ⟨R, mem_iUnion.mpr ⟨hR, hxR⟩⟩
            intro htarget
            exact hxSc htarget.1
      · refine pairwiseDisjoint_insert.2 ⟨hUdis, ?_⟩
        intro P hP hne
        apply Set.disjoint_left.2
        intro x hxQ hxP
        have hxS : x ∈ polynomialZeroSet k n S := hxQ.1
        have hxSc : x ∈ (polynomialZeroSet k n S)ᶜ := by
          rw [hUeq]
          exact mem_iUnion.mpr ⟨P, mem_iUnion.mpr ⟨hP, hxP⟩⟩
        exact hxSc hxS

private theorem exists_finite_pairwiseDisjoint_piece_compl
    {k : Type u} [Field k] [IsAlgClosed k] (n : ℕ)
    (P : ConstructiblePiece k n) :
    ∃ U : Set (ConstructiblePiece k n), U.Finite ∧
      (P.toSet)ᶜ = ⋃ Q ∈ U, Q.toSet ∧
        U.PairwiseDisjoint (fun Q : ConstructiblePiece k n => Q.toSet) := by
  classical
  obtain ⟨S, hSfin, hS⟩ :=
    exists_finite_polynomials_eq_polynomialZeroSet n P.zeroSet_isAlgebraic
  obtain ⟨U, hUfin, hUeq, hUdis⟩ :=
    exists_finite_pairwiseDisjoint_zeroSet_compl n S hSfin
  let Q : ConstructiblePiece k n :=
    { zeroSet := P.zeroSet ∩ polynomialZeroSet k n {P.polynomial}
      polynomial := 1
      zeroSet_isAlgebraic :=
        isAlgebraic_inter n _ _ P.zeroSet_isAlgebraic ⟨{P.polynomial}, rfl⟩ }
  have hQ : Q.toSet = P.zeroSet ∩
      polynomialZeroSet k n {P.polynomial} := by
    simp [Q, ConstructiblePiece.toSet, polynomialEvaluation,
      polynomialZeroSet, MvPolynomial.zeroLocus_span]
  refine ⟨insert Q U, hUfin.insert _, ?_, ?_⟩
  · unfold ConstructiblePiece.toSet
    ext x
    constructor
    · intro hx
      by_cases hxP : x ∈ P.zeroSet
      · by_cases hxp : polynomialEvaluation P.polynomial x = 0
        · refine mem_iUnion.mpr ⟨Q, mem_iUnion.mpr ⟨mem_insert _ _, ?_⟩⟩
          have hzeroP : x ∈ polynomialZeroSet k n {P.polynomial} := by
            simpa [polynomialZeroSet, MvPolynomial.zeroLocus_span,
              polynomialEvaluation] using hxp
          change x ∈ (P.zeroSet ∩ polynomialZeroSet k n {P.polynomial}) ∩
            {x | polynomialEvaluation (1 : MvPolynomial (Fin n) k) x ≠ 0}
          exact ⟨⟨hxP, hzeroP⟩, by simp [polynomialEvaluation]⟩
        · exact (hx ⟨hxP, hxp⟩).elim
      · have hxPc : x ∈ P.zeroSetᶜ := hxP
        rw [hS, hUeq] at hxPc
        rcases mem_iUnion.mp hxPc with ⟨R, hxR⟩
        rcases mem_iUnion.mp hxR with ⟨hR, hxR⟩
        exact mem_iUnion.mpr ⟨R, mem_iUnion.mpr ⟨mem_insert_iff.mpr (Or.inr hR), hxR⟩⟩
    · intro hx
      rcases mem_iUnion.mp hx with ⟨R, hxR⟩
      rcases mem_iUnion.mp hxR with ⟨hR, hxR⟩
      rcases mem_insert_iff.mp hR with rfl | hR
      · have hxzero : polynomialEvaluation P.polynomial x = 0 := by
          simpa [Q, polynomialZeroSet, MvPolynomial.zeroLocus_span,
            polynomialEvaluation] using hxR.1.2
        intro htarget
        exact htarget.2 hxzero
      · have hxPc : x ∈ P.zeroSetᶜ := by
          rw [hS, hUeq]
          exact mem_iUnion.mpr ⟨R, mem_iUnion.mpr ⟨hR, hxR⟩⟩
        intro htarget
        exact hxPc htarget.1
  · refine pairwiseDisjoint_insert.2 ⟨hUdis, ?_⟩
    intro R hR hne
    apply Set.disjoint_left.2
    intro x hxQ hxR
    have hxZ : x ∈ P.zeroSet := by
      rw [hQ] at hxQ
      exact hxQ.1
    have hxZc : x ∈ P.zeroSetᶜ := by
      rw [hS, hUeq]
      exact mem_iUnion.mpr ⟨R, mem_iUnion.mpr ⟨hR, hxR⟩⟩
    exact hxZc hxZ

/-- Every constructible set is a finite disjoint union of basic pieces. -/
theorem exists_finite_pairwiseDisjoint_constructiblePieces
    {k : Type u} [Field k] [IsAlgClosed k] (n : ℕ)
    {E : Set (Fin n → k)} (hE : IsConstructible k n E) :
    ∃ T : Set (ConstructiblePiece k n), T.Finite ∧
      (E = ⋃ P ∈ T, P.toSet) ∧
        T.PairwiseDisjoint (fun P : ConstructiblePiece k n => P.toSet) := by
  classical
  rcases hE with ⟨T, hT, hET⟩
  let I := {P : ConstructiblePiece k n // P ∈ T}
  letI : Finite I := hT.to_subtype
  let C : I → Set (ConstructiblePiece k n) := fun P =>
    Classical.choose (exists_finite_pairwiseDisjoint_piece_compl n P.1)
  have hCspec (P : I) :
      (C P).Finite ∧
        (P.1.toSet)ᶜ = ⋃ Q ∈ C P, Q.toSet ∧
          (C P).PairwiseDisjoint (fun Q : ConstructiblePiece k n => Q.toSet) := by
    exact Classical.choose_spec (exists_finite_pairwiseDisjoint_piece_compl n P.1)
  let O : I → Set (ConstructiblePiece k n) := fun P => insert P.1 (C P)
  have hOfin (P : I) : (O P).Finite := by
    simpa [O] using (Set.Finite.insert P.1 (hCspec P).1)
  have hOdis (P : I) {A B : ConstructiblePiece k n}
      (hA : A ∈ O P) (hB : B ∈ O P) (hne : A ≠ B) :
      Disjoint A.toSet B.toSet := by
    have hCsub (Q : ConstructiblePiece k n) (hQ : Q ∈ C P) :
        Disjoint P.1.toSet Q.toSet := by
      apply Set.disjoint_left.2
      intro x hxP hxQ
      have hxc : x ∈ (P.1.toSet)ᶜ := by
        rw [(hCspec P).2.1]
        exact mem_iUnion.mpr ⟨Q, mem_iUnion.mpr ⟨hQ, hxQ⟩⟩
      exact hxc hxP
    rcases mem_insert_iff.mp hA with rfl | hA
    · rcases mem_insert_iff.mp hB with rfl | hB
      · exact (hne rfl).elim
      · exact hCsub B hB
    · rcases mem_insert_iff.mp hB with rfl | hB
      · exact (hCsub A hA).symm
      · exact (hCspec P).2.2 hA hB hne
  let Choices : Set (∀ P : I, ConstructiblePiece k n) :=
    {f | ∀ P, f P ∈ O P}
  have hChoices : Choices.Finite := by
    exact Set.Finite.pi' hOfin
  let Cells : Set (∀ P : I, ConstructiblePiece k n) :=
    {f | f ∈ Choices ∧ ∃ P, f P = P.1}
  have hCells : Cells.Finite := hChoices.subset (by
    intro f hf
    exact hf.1)
  let pieceOf : (∀ P : I, ConstructiblePiece k n) → ConstructiblePiece k n := fun f =>
    Classical.choose (exists_piece_for_finite_intersection n (Set.range f)
      (Set.finite_range f))
  have hpieceOf (f : ∀ P : I, ConstructiblePiece k n) :
      (pieceOf f).toSet = ⋂ Q ∈ Set.range f, Q.toSet := by
    exact Classical.choose_spec (exists_piece_for_finite_intersection n (Set.range f)
      (Set.finite_range f))
  let U : Set (ConstructiblePiece k n) := pieceOf '' Cells
  have hUfin : U.Finite := hCells.image pieceOf
  have hcoord (f : ∀ P : I, ConstructiblePiece k n) (x : Fin n → k)
      (hx : x ∈ (pieceOf f).toSet) (P : I) : x ∈ (f P).toSet := by
    rw [hpieceOf f] at hx
    exact mem_iInter.mp (mem_iInter.mp hx (f P)) ⟨P, rfl⟩
  have hUeq : E = ⋃ Q ∈ U, Q.toSet := by
    rw [hET]
    ext x
    constructor
    · intro hx
      rcases mem_iUnion.mp hx with ⟨P, hx⟩
      rcases mem_iUnion.mp hx with ⟨hP, hx⟩
      let hcomp : ∀ (Q : I), x ∉ Q.1.toSet →
          ∃ R ∈ C Q, x ∈ R.toSet := by
        intro Q hxQ
        have hxc : x ∈ (Q.1.toSet)ᶜ := hxQ
        rw [(hCspec Q).2.1] at hxc
        rcases mem_iUnion.mp hxc with ⟨R, hxc⟩
        rcases mem_iUnion.mp hxc with ⟨hR, hxR⟩
        exact ⟨R, hR, hxR⟩
      let f : ∀ Q : I, ConstructiblePiece k n := fun Q =>
        if hxQ : x ∈ Q.1.toSet then Q.1 else
          Classical.choose (hcomp Q hxQ)
      have hfChoices : f ∈ Choices := by
        intro Q
        dsimp [f, O]
        split_ifs with hxQ
        · exact mem_insert _ _
        · exact mem_insert_iff.mpr (Or.inr (Classical.choose_spec (hcomp Q hxQ)).1)
      have hfCells : f ∈ Cells := by
        refine ⟨hfChoices, ?_⟩
        refine ⟨⟨P, hP⟩, ?_⟩
        dsimp [f]
        simp [hx]
      refine mem_iUnion.mpr ⟨pieceOf f, mem_iUnion.mpr ⟨⟨f, hfCells, rfl⟩, ?_⟩⟩
      rw [hpieceOf f]
      simp only [mem_iInter]
      intro Q hQ
      rcases hQ with ⟨R, rfl⟩
      dsimp [f]
      split_ifs with hxR
      · exact hxR
      · exact (Classical.choose_spec (hcomp R hxR)).2
    · intro hx
      rcases mem_iUnion.mp hx with ⟨Q, hx⟩
      rcases mem_iUnion.mp hx with ⟨hQ, hx⟩
      rcases hQ with ⟨f, hfCells, rfl⟩
      rcases hfCells.2 with ⟨P, hP⟩
      have hxP : x ∈ (f P).toSet := hcoord f x hx P
      rw [hP] at hxP
      exact mem_iUnion.mpr ⟨P.1, mem_iUnion.mpr ⟨P.2, hxP⟩⟩
  refine ⟨U, hUfin, hUeq, ?_⟩
  intro A hA B hB hne
  rcases hA with ⟨f, hf, rfl⟩
  rcases hB with ⟨g, hg, rfl⟩
  have hfg : f ≠ g := by
    intro hfg
    subst g
    exact hne rfl
  have hdiff : ∃ P : I, f P ≠ g P := by
    by_contra h'
    apply hfg
    funext P
    by_contra hP
    exact h' ⟨P, hP⟩
  rcases hdiff with ⟨P, hP⟩
  apply Set.disjoint_left.2
  intro x hxf hxg
  exact Set.disjoint_left.1 (hOdis P (hf.1 P) (hg.1 P) hP)
    (hcoord f x hxf P) (hcoord g x hxg P)

end

end Formalization.Books.Exercises.Unit15
