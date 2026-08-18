import Formalization.Books.Algebra.Unit44.SeparableExtensionsContinued
import Mathlib.FieldTheory.Perfect
import Mathlib.FieldTheory.PerfectClosure
import Mathlib.FieldTheory.PurelyInseparable.PerfectClosure
import Mathlib.RingTheory.Nilpotent.Lemmas

/-!
# Commutative Algebra, Chapter 45: Perfect fields

The source's perfect-field predicate is represented by Mathlib's canonical
`PerfectField` class.  Relative perfect closures are represented by
`perfectClosure` inside an algebraic closure, while the positive-characteristic
root levels are represented by the canonical `PerfectClosure` construction.
-/

namespace Formalization.Books.Algebra.Unit45

open Set
open scoped TensorProduct

universe u v w

noncomputable section

open Formalization.Books.Algebra.Unit42
open Formalization.Books.Algebra.Unit43

private theorem algebra_isSeparable_of_isSeparableExtension_of_isAlgebraic
    {F E : Type*} [Field F] [Field E] [Algebra F E]
    [Algebra.IsAlgebraic F E]
    (h : IsSeparableExtension F E) : Algebra.IsSeparable F E := by
  sorry

/-! ## Perfect fields -/

/- The source defines perfection by separability of every field extension.
   `PerfectField` is Mathlib's canonical equivalent formulation, while
   `IsSeparableExtension` is the earlier chapter's arbitrary-extension notion. -/
/-- Mathlib's canonical perfect-field class is equivalent to the source's
    definition by separability of every field extension. -/
theorem perfectField_iff_all_field_extensions_separable
    {k : Type u} [Field k] :
    PerfectField k ↔
      ∀ (K : Type v) [Field K] [Algebra k K],
        IsSeparableExtension k K := by
  sorry

/-- A field is perfect exactly in characteristic zero or in prime
    characteristic with surjective Frobenius on elements. -/
theorem perfectField_iff_charZero_or_prime_root
    {k : Type u} [Field k] :
    PerfectField k ↔
      CharZero k ∨
        ∃ p : ℕ, p.Prime ∧ CharP k p ∧
          ∀ x : k, ∃ y : k, y ^ p = x := by
  constructor
  · intro h
    by_cases hzero : CharZero k
    · exact Or.inl hzero
    · obtain _ | ⟨p, hp, hpk⟩ := CharP.exists' k
      · exact (hzero ‹CharZero k›).elim
      right
      refine ⟨p, hp.out, hpk, ?_⟩
      let _ : PerfectField k := h
      let _ : Fact p.Prime := hp
      let _ : CharP k p := hpk
      let _ : ExpChar k p := ExpChar.prime hp.out
      intro x
      rcases (surjective_frobenius k p) x with ⟨y, hy⟩
      exact ⟨y, by change y ^ p = x; exact hy⟩
  · rintro (hzero | ⟨p, hp, hpk, hroot⟩)
    · let _ : CharZero k := hzero
      exact inferInstance
    · let _ : Fact p.Prime := ⟨hp⟩
      let _ : CharP k p := hpk
      let _ : ExpChar k p := ExpChar.prime hp
      letI : PerfectRing k p :=
        PerfectRing.ofSurjective k p (by
          intro x
          rcases hroot x with ⟨y, hy⟩
          exact ⟨y, by change y ^ p = x; exact hy⟩)
      exact PerfectRing.toPerfectField k p

/-! ## Making a finitely generated extension separable -/

/- Unit 42 already bundles the source's commuting diagram and the finite
   purely inseparable hypotheses.  These predicates expose the two additional
   normalizations stated in this chapter without duplicating that structure. -/
/-- The upper extension in a `PurelyInseparableBaseChange` is separable in the
    source's arbitrary-extension sense. -/
def IsSeparableBaseChange
    {k : Type u} {K : Type v} [Field k] [Field K] [Algebra k K]
    (b : PurelyInseparableBaseChange k K) : Prop :=
  letI := b.baseField
  letI := b.topField
  letI := b.baseAlgebra
  letI := b.topAlgebra
  letI := b.topOverK
  letI := b.topOverBase
  letI := b.baseTower
  letI := b.topTower
  IsSeparableExtension b.base b.top

/-- The upper field of a base-change diagram is the compositum of the base
    field and the original extension inside the upper field. -/
def IsCompositumBaseChange
    {k : Type u} {K : Type v} [Field k] [Field K] [Algebra k K]
    (b : PurelyInseparableBaseChange k K) : Prop :=
  letI := b.baseField
  letI := b.topField
  letI := b.baseAlgebra
  letI := b.topAlgebra
  letI := b.topOverK
  letI := b.topOverBase
  letI := b.baseTower
  letI := b.topTower
  IntermediateField.adjoin b.base (range (algebraMap K b.top)) = ⊤

/- The notation `(R)_{red}` in the source is the quotient by the nilradical.
   The assertion is recorded as the corresponding canonical algebra
   equivalence, rather than by introducing a second reduced-ring definition. -/
/-- The upper field is the reduced tensor product of the two lower fields. -/
def IsReducedTensorProductBaseChange
    {k : Type u} {K : Type v} [Field k] [Field K] [Algebra k K]
    (b : PurelyInseparableBaseChange k K) : Prop :=
  letI := b.baseField
  letI := b.topField
  letI := b.baseAlgebra
  letI := b.topAlgebra
  letI := b.topOverK
  letI := b.topOverBase
  letI := b.baseTower
  letI := b.topTower
  Nonempty
    (((b.base ⊗[k] K) ⧸ (nilradical (b.base ⊗[k] K))) ≃ₐ[k] b.top)

/-- A finitely generated field extension admits the source's finite purely
    inseparable base-change diagram with separable, compositum, and reduced
    tensor-product normalizations. -/
theorem exists_make_separable_base_change
    {k : Type u} {K : Type v} [Field k] [Field K] [Algebra k K]
    [Algebra.EssFiniteType k K] :
    ∃ b : PurelyInseparableBaseChange k K,
      IsSeparableBaseChange b ∧
        IsCompositumBaseChange b ∧ IsReducedTensorProductBaseChange b := by
  obtain ⟨b⟩ := exists_purely_inseparable_base_change (k := k) (K := K)
  letI := b.baseField
  letI := b.topField
  letI := b.baseAlgebra
  letI := b.topAlgebra
  letI := b.topOverK
  letI := b.topOverBase
  letI := b.baseTower
  letI := b.topTower
  refine ⟨b, ?_, ?_, ?_⟩
  · simp only [IsSeparableBaseChange]
    exact Formalization.Books.Algebra.Unit44.isSeparableExtension_of_isSeparablyGenerated
      b.topSeparablyGenerated
  · sorry
  · sorry

/-! ## Perfect closures -/

/- The source's characteristic-free `k^{perf}` is the relative perfect
   closure of `k` in an algebraic closure. -/
/-- The canonical relative perfect closure is purely inseparable over the
    base and is a perfect field. -/
theorem perfectClosure_is_purelyInseparable_and_perfect
    (k : Type u) [Field k] :
    IsPurelyInseparable k (perfectClosure k (AlgebraicClosure k)) ∧
      PerfectField (perfectClosure k (AlgebraicClosure k)) := by
  constructor
  · infer_instance
  · infer_instance

/-- In characteristic zero the canonical perfect closure is the base field,
    represented as the bottom intermediate field. -/
theorem perfectClosure_eq_bot_of_charZero
    (k : Type u) [Field k] [CharZero k] :
    perfectClosure k (AlgebraicClosure k) = ⊥ := by
  sorry

/-- Any two purely inseparable perfect extensions of a field are uniquely
    isomorphic as extensions of that field. -/
theorem perfectClosure_unique_up_to_unique_algEquiv
    {k : Type u} {k' : Type v} {k'' : Type w}
    [Field k] [Field k'] [Field k'']
    [Algebra k k'] [Algebra k k'']
    [IsPurelyInseparable k k'] [IsPurelyInseparable k k'']
    [PerfectField k'] [PerfectField k''] :
    ∃ e : k' ≃ₐ[k] k'', ∀ e' : k' ≃ₐ[k] k'', e' = e := by
  sorry

/- Mathlib's absolute perfect closure presents the positive-characteristic
   levels `k^(1/p^n)` by representatives `PerfectClosure.mk (n, x)`. -/
/- `PerfectClosure.of` is the canonical structure map, and its associated
   algebra instance is needed to form the intermediate fields generated by
   the finite root levels below. -/
noncomputable instance perfectClosureAlgebra
    (k : Type u) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p] :
    Algebra k (PerfectClosure k p) :=
  (PerfectClosure.of k p).toAlgebra

/-- The canonical finite `p^n`-th-root level inside the absolute perfect
    closure. -/
noncomputable def pthRootLevel
    (k : Type u) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p] (n : ℕ) :
    IntermediateField k (PerfectClosure k p) :=
  IntermediateField.adjoin k
    (range fun x : k => PerfectClosure.mk k p (n, x))

/-- Every element of the finite root level has a `p^n`-th root in the level
    for each element of the base field. -/
theorem pthRootLevel_has_roots
    {k : Type u} [Field k] (p : ℕ) [Fact p.Prime] [CharP k p]
    (n : ℕ) (x : k) :
    ∃ y : pthRootLevel k p n,
      (y : PerfectClosure k p) ^ (p ^ n) = PerfectClosure.of k p x := by
  sorry

/-- Every element of the finite root level has its `p^n`-th power in the base
    field. -/
theorem pthRootLevel_element_pow_mem_base
    {k : Type u} [Field k] (p : ℕ) [Fact p.Prime] [CharP k p]
    (n : ℕ) (y : pthRootLevel k p n) :
    ∃ x : k,
      (y : PerfectClosure k p) ^ (p ^ n) = PerfectClosure.of k p x := by
  sorry

/-- Each finite root level is algebraic over its base field. -/
theorem pthRootLevel_is_algebraic
    {k : Type u} [Field k] (p : ℕ) [Fact p.Prime] [CharP k p]
    (n : ℕ) :
    Algebra.IsAlgebraic k (pthRootLevel k p n) := by
  sorry

/-- Each finite root level is purely inseparable over its base field. -/
theorem pthRootLevel_is_purelyInseparable
    {k : Type u} [Field k] (p : ℕ) [Fact p.Prime] [CharP k p]
    (n : ℕ) :
    IsPurelyInseparable k (pthRootLevel k p n) := by
  sorry

/-- The finite root levels form an increasing tower inside the absolute
    perfect closure. -/
theorem pthRootLevel_mono
    {k : Type u} [Field k] (p : ℕ) [Fact p.Prime] [CharP k p]
    (n : ℕ) :
    pthRootLevel k p n ≤ pthRootLevel k p (n + 1) := by
  sorry

/-- The finite root level is uniquely determined, up to a unique isomorphism,
    by its algebraicity and its two `p^n`-power properties. -/
theorem pthRootLevel_unique_up_to_unique_algEquiv
    {k : Type u} {L : Type v} [Field k] [Field L] (p : ℕ) [Fact p.Prime] [CharP k p]
    [Algebra k L] (n : ℕ) (hn : 0 < n) [Algebra.IsAlgebraic k L]
    (hroot : ∀ x : k, ∃ y : L,
      y ^ (p ^ n) = algebraMap k L x)
    (hbase : ∀ y : L, ∃ x : k,
      y ^ (p ^ n) = algebraMap k L x) :
    ∃ e : pthRootLevel k p n ≃ₐ[k] L,
      ∀ e' : pthRootLevel k p n ≃ₐ[k] L, e' = e := by
  sorry

/-- Every element of the canonical `p`-th-root level has the expected
    `p^n`-th power in the base. -/
theorem perfectClosure_mk_pow
    {k : Type u} [Field k] (p : ℕ) [Fact p.Prime] [CharP k p]
    (n : ℕ) (x : k) :
    (PerfectClosure.mk k p (n, x)) ^ (p ^ n) = PerfectClosure.of k p x := by
  sorry

/-- Every element of the absolute perfect closure occurs at some finite
    `p`-th-root level. -/
theorem perfectClosure_is_union_of_pth_root_levels
    {k : Type u} [Field k] (p : ℕ) [Fact p.Prime] [CharP k p] :
    ∀ y : PerfectClosure k p,
      ∃ n : ℕ, ∃ x : k, y = PerfectClosure.mk k p (n, x) := by
  intro y
  obtain ⟨⟨n, x⟩, h⟩ := PerfectClosure.mk_surjective k p y
  exact ⟨n, x, h.symm⟩

/-- An element represented at level `n` has its `p^n`-th power in the base. -/
theorem perfectClosure_level_element_pow_mem_base
    {k : Type u} [Field k] (p : ℕ) [Fact p.Prime] [CharP k p]
    (n : ℕ) (y : PerfectClosure k p)
    (hy : ∃ x : k, y = PerfectClosure.mk k p (n, x)) :
    ∃ x : k, y ^ (p ^ n) = PerfectClosure.of k p x := by
  sorry

/-- The absolute perfect closure is the union of its positive finite root
    levels. -/
theorem perfectClosure_is_union_of_finite_pth_root_levels
    {k : Type u} [Field k] (p : ℕ) [Fact p.Prime] [CharP k p] :
    ∀ y : PerfectClosure k p,
      ∃ n : ℕ, 0 < n ∧
        ∃ z : pthRootLevel k p n, (z : PerfectClosure k p) = y := by
  sorry

/- The source's subextension observation is stated with the necessary choice
   of an embedding into a fixed algebraic closure. -/
/-- An algebraic purely inseparable extension embeds over the base into the
    canonical perfect closure inside an algebraic closure. -/
theorem algebraic_purelyInseparable_extension_embeds_in_perfectClosure
    {k : Type u} {E : Type v} [Field k] [Field E] [Algebra k E]
    [Algebra.IsAlgebraic k E] [IsPurelyInseparable k E] :
    ∃ i : E →ₐ[k] AlgebraicClosure k,
      ∀ x : E, i x ∈ perfectClosure k (AlgebraicClosure k) := by
  sorry

/-! ## Perfect fields and reduced algebras -/

/-- A reduced algebra over a perfect field is geometrically reduced. -/
theorem isGeometricallyReduced_of_perfectField
    {k : Type u} {S : Type v} [Field k] [CommRing S]
    [Algebra k S] [PerfectField k] (hS : IsReduced S) :
    IsGeometricallyReduced k S := by
  sorry

/-- The tensor product of two reduced algebras over a perfect field is
    reduced. -/
theorem isReduced_tensorProduct_of_perfectField
    {k : Type u} {R : Type v} {S : Type w} [Field k] [CommRing R] [CommRing S]
    [Algebra k R] [Algebra k S] [PerfectField k]
    (hR : IsReduced R) (hS : IsReduced S) :
    IsReduced (R ⊗[k] S) := by
  sorry

end

end Formalization.Books.Algebra.Unit45
