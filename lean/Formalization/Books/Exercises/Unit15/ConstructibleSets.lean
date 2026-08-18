import Mathlib.RingTheory.Nullstellensatz

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
  simp [polynomialZeroSet, hT]

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

/-- Every constructible set is a finite disjoint union of basic pieces. -/
theorem exists_finite_pairwiseDisjoint_constructiblePieces
    {k : Type u} [Field k] [IsAlgClosed k] (n : ℕ)
    {E : Set (Fin n → k)} (hE : IsConstructible k n E) :
    ∃ T : Set (ConstructiblePiece k n), T.Finite ∧
      (E = ⋃ P ∈ T, P.toSet) ∧
        T.PairwiseDisjoint (fun P : ConstructiblePiece k n => P.toSet) := by
  sorry

end

end Formalization.Books.Exercises.Unit15
