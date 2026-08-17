import Mathlib.Algebra.Polynomial.Splits
import Mathlib.FieldTheory.Normal.Basic
import Mathlib.FieldTheory.Normal.Closure
import Mathlib.FieldTheory.SeparableClosure
import Mathlib.FieldTheory.SeparableDegree

/-!
# Fields, Chapter 15: Normal extensions

The source's “splits completely” predicate is Mathlib's canonical
`Polynomial.Splits`.  Normality is likewise Mathlib's `Normal` class, which
packages algebraicity with splitting of every minimal polynomial.  A
`K`-algebra embedding is an `AlgHom`, an automorphism group is `Gal(L / K)`,
and the source's separable degree is `Field.finSepDegree`.
-/

namespace Formalization.Books.Fields.Unit15

noncomputable section

open Polynomial

/-! ## Splitting and normality -/

/- `Polynomial.Splits` is the existing definition of splitting into a scalar
   and monic linear factors.  The source's scalar is the leading coefficient
   in this factorization, and the definition itself needs no parallel
   predicate.  The theorem below records the nonconstant case from the
   displayed factorization, using a finite multiset for the list of roots. -/
theorem polynomial_splits_completely_iff
    {F : Type*} [Field F] {P : F[X]} (hP : P.natDegree ≠ 0) :
    P.Splits ↔
      ∃ (c : F) (roots : Multiset F),
        c ≠ 0 ∧ 0 < roots.card ∧
          P = C c * (roots.map (X - C ·)).prod := by
  rw [splits_iff_exists_multiset]
  constructor
  · rintro ⟨roots, hroots⟩
    have hc : P.leadingCoeff ≠ 0 := by
      rw [leadingCoeff_ne_zero]
      intro hzero
      apply hP
      rw [hzero, natDegree_zero]
    have hcard : 0 < roots.card := by
      have hdeg := congrArg natDegree hroots
      rw [natDegree_C_mul hc, natDegree_multiset_prod_X_sub_C_eq_card] at hdeg
      rw [← hdeg]
      exact Nat.pos_of_ne_zero hP
    exact ⟨P.leadingCoeff, roots, hc, hcard, hroots⟩
  · rintro ⟨c, roots, hc, hcard, hroots⟩
    refine ⟨roots, ?_⟩
    rw [hroots, leadingCoeff_mul, leadingCoeff_C,
      (monic_multisetProd_X_sub_C roots).leadingCoeff]
    simp

/- `Normal F E` is the existing definition of an algebraic normal extension;
   its `normal_iff` theorem already exposes the pointwise minimal-polynomial
   splitting condition. -/

/-! ## Basic properties -/

/- The source assumes an algebraic tower.  `Normal F K` already supplies the
   needed algebraicity of the top extension, and Mathlib's tower theorem
   derives the algebraicity over the middle field. -/
theorem normal_goes_up
    {F E K : Type*} [Field F] [Field E] [Field K]
    [Algebra F E] [Algebra E K] [Algebra F K] [IsScalarTower F E K]
    [Normal F K] :
    Normal E K :=
  Normal.tower_top_of_normal F E K

/- The source's index type is required to be nonempty: for an empty family,
   the intersection is the ambient algebraic extension, which need not be
   normal. -/
theorem normal_intersection
    {F M ι : Type*} [Field F] [Field M] [Algebra F M]
    [Algebra.IsAlgebraic F M] [Nonempty ι]
    (E : ι → IntermediateField F M)
    [hE : ∀ i, Normal F (E i)] :
    Normal F (⨅ i, E i : IntermediateField F M) := by
  infer_instance

/- The separable subextension in the source is Mathlib's canonical
   `separableClosure`. -/
theorem separable_closure_normal
    {F E : Type*} [Field F] [Field E] [Algebra F E] [Normal F E] :
    Normal F (separableClosure F E) := by
  exact (separableClosure.normalClosure_eq_self F E).symm ▸
    (normalClosure.normal F (separableClosure F E) E)

/-! ## Embeddings and generators -/

/- The source's algebraic closure is represented by `IsAlgClosure`, and its
   extension maps by `AlgHom`.  `fieldRange` is the bundled image
   intermediate field. -/
theorem normal_iff_algebraic_closure_embedding_ranges
    {F E L : Type*} [Field F] [Field E] [Field L]
    [Algebra F E] [Algebra F L] [IsAlgClosure F L]
    [Algebra.IsAlgebraic F E] :
    Normal F E ↔
      ∀ σ σ' : E →ₐ[F] L, σ.fieldRange = σ'.fieldRange := by
  let _ : IsAlgClosed L := IsAlgClosure.isAlgClosed (K := L) F
  let i : E →ₐ[F] L := IsAlgClosed.lift
  let e : E ≃ₐ[F] i.fieldRange := i.equivFieldRange
  have range_comp (f : i.fieldRange →ₐ[F] L) :
      (f.comp e.toAlgHom).fieldRange = f.fieldRange := by
    apply SetLike.ext'
    simp only [AlgHom.coe_fieldRange, AlgHom.coe_comp, Set.range_comp]
    apply Set.Subset.antisymm
    · rintro z ⟨y, ⟨x, rfl⟩, rfl⟩
      exact ⟨e x, rfl⟩
    · rintro z ⟨y, rfl⟩
      obtain ⟨x, rfl⟩ := e.surjective y
      exact ⟨e x, ⟨x, rfl⟩, rfl⟩
  constructor
  · intro h σ σ'
    let _ : Normal F i.fieldRange := Normal.of_algEquiv e (h := h)
    have hσ : (σ.comp e.symm.toAlgHom).fieldRange = i.fieldRange :=
      AlgHom.fieldRange_of_normal (σ.comp e.symm.toAlgHom)
    have hσ' : (σ'.comp e.symm.toAlgHom).fieldRange = i.fieldRange :=
      AlgHom.fieldRange_of_normal (σ'.comp e.symm.toAlgHom)
    have heq : (σ.comp e.symm.toAlgHom).comp e.toAlgHom = σ := by
      ext x
      simp
    have heq' : (σ'.comp e.symm.toAlgHom).comp e.toAlgHom = σ' := by
      ext x
      simp
    have hrange : σ.fieldRange = (σ.comp e.symm.toAlgHom).fieldRange := by
      exact (congrArg (fun f : E →ₐ[F] L => f.fieldRange) heq).symm.trans (range_comp _)
    have hrange' : σ'.fieldRange = (σ'.comp e.symm.toAlgHom).fieldRange := by
      exact (congrArg (fun f : E →ₐ[F] L => f.fieldRange) heq').symm.trans (range_comp _)
    exact (hrange.trans hσ).trans (hrange'.trans hσ').symm
  · intro h
    have hnormal : Normal F i.fieldRange := by
      rw [IntermediateField.normal_iff_forall_fieldRange_eq]
      intro f
      exact (range_comp f).symm.trans (h (f.comp e.toAlgHom) i)
    exact Normal.of_algEquiv e.symm (h := hnormal)

/- The source's indexed family of generators is represented by a set. -/
theorem normal_of_generated_by_splits
    {F E : Type*} [Field F] [Field E] [Algebra F E]
    [Algebra.IsAlgebraic F E] (S : Set E)
    (hS : IntermediateField.adjoin F S = ⊤)
    (hsplits : ∀ α ∈ S,
      ((minpoly F α).map (algebraMap F E)).Splits) :
    Normal F E := by
  apply normal_iff.mpr
  intro x
  refine ⟨Algebra.IsIntegral.isIntegral x, ?_⟩
  have hx : x ∈ IntermediateField.adjoin F S := by
    rw [hS]
    exact IntermediateField.mem_top
  exact IntermediateField.splits_of_mem_adjoin F E
    (fun y hy ↦ ⟨Algebra.IsIntegral.isIntegral y, hsplits y hy⟩)
    hx

/-! ## Lifting maps and automorphisms -/

/- Part (1) of the source's lifting lemma: the restriction is an
   automorphism of the normal middle field, expressed by the commutative
   equation from the displayed diagram. -/
theorem automorphism_restricts_to_normal_subextension
    {K M L : Type*} [Field K] [Field M] [Field L]
    [Algebra K M] [Algebra M L] [Algebra K L] [IsScalarTower K M L]
    [Algebra.IsAlgebraic M L] [Normal K M]
    (τ : L ≃ₐ[K] L) :
    ∃ σ : M ≃ₐ[K] M,
      ∀ x : M, algebraMap M L (σ x) = τ (algebraMap M L x) := by
  exact ⟨τ.restrictNormal M, fun x => AlgEquiv.restrictNormal_commutes τ M x⟩

/- Part (2) is already supplied by the canonical `AlgHom.liftNormal` together
   with `AlgHom.normal_bijective`.
   The source-facing theorem below states its extension property without
   introducing a parallel wrapper definition. -/
theorem normal_extension_lifts_algebra_map
    {K M L : Type*} [Field K] [Field M] [Field L]
    [Algebra K M] [Algebra M L] [Algebra K L] [IsScalarTower K M L]
    [Algebra.IsAlgebraic K M] [Algebra.IsAlgebraic M L] [Normal K L]
    (σ : M →ₐ[K] L) :
    ∃ τ : L ≃ₐ[K] L,
      ∀ x : M, τ (algebraMap M L x) = σ x := by
  refine ⟨AlgEquiv.ofBijective (σ.liftNormal L) (AlgHom.normal_bijective K L L _), ?_⟩
  intro x
  change σ.liftNormal L (algebraMap M L x) = σ x
  rw [AlgHom.liftNormal_commutes]
  simp

/- The source's `Aut(E/F)` is Mathlib's existing `Gal(E / F)` notation for
   the group `E ≃ₐ[F] E`; no new automorphism-group definition is needed. -/

/-! ## Automorphism counts -/

/- `Field.finSepDegree` is Mathlib's natural-number version of the source's
   separable degree. -/
theorem finite_extension_automorphism_card_le_finSepDegree
    {F E : Type*} [Field F] [Field E] [Algebra F E]
    [FiniteDimensional F E] :
    Nat.card (Gal(E / F)) ≤ Field.finSepDegree F E := by
  rw [Field.finSepDegree]
  let i : E →ₐ[F] AlgebraicClosure E := IsScalarTower.toAlgHom F E _
  let f : Gal(E / F) → E →ₐ[F] AlgebraicClosure E :=
    fun σ => i.comp σ.toAlgHom
  apply Nat.card_le_card_of_injective f
  intro σ τ h
  ext x
  apply (algebraMap E (AlgebraicClosure E)).injective
  exact DFunLike.congr_fun h x

theorem finite_extension_automorphism_card_eq_finSepDegree_iff_normal
    {F E : Type*} [Field F] [Field E] [Algebra F E]
    [FiniteDimensional F E] :
    Nat.card (Gal(E / F)) = Field.finSepDegree F E ↔ Normal F E := by
  constructor
  · intro hcard
    let i : E →ₐ[F] AlgebraicClosure E :=
      IsScalarTower.toAlgHom F E (AlgebraicClosure E)
    let f : Gal(E / F) → E →ₐ[F] AlgebraicClosure E :=
      fun σ => i.comp σ.toAlgHom
    have hf : Function.Injective f := by
      intro σ τ h
      ext x
      apply (algebraMap E (AlgebraicClosure E)).injective
      exact DFunLike.congr_fun h x
    have hcard' :
        Nat.card (Gal(E / F)) = Nat.card (E →ₐ[F] AlgebraicClosure E) := by
      simpa [Field.finSepDegree] using hcard
    have hbij : Function.Bijective f :=
      (Nat.bijective_iff_injective_and_card f).2 ⟨hf, hcard'⟩
    let _ : IsAlgClosure F (AlgebraicClosure E) :=
      IsAlgClosure.ofAlgebraic F E (AlgebraicClosure E)
    apply (normal_iff_algebraic_closure_embedding_ranges
      (F := F) (E := E) (L := AlgebraicClosure E)).2
    intro σ τ
    have hrange (a : Gal(E / F)) :
        (i.comp a.toAlgHom).fieldRange = i.fieldRange := by
      apply SetLike.ext'
      simp only [AlgHom.coe_fieldRange, AlgHom.coe_comp, Set.range_comp]
      apply Set.Subset.antisymm
      · rintro z ⟨y, ⟨x, rfl⟩, rfl⟩
        exact ⟨a x, rfl⟩
      · rintro z ⟨y, rfl⟩
        exact ⟨y, ⟨a.symm y, by simp⟩, rfl⟩
    obtain ⟨a, ha⟩ := hbij.2 σ
    obtain ⟨b, hb⟩ := hbij.2 τ
    calc
      σ.fieldRange = (f a).fieldRange :=
        congrArg (fun g : E →ₐ[F] AlgebraicClosure E => g.fieldRange) ha.symm
      _ = i.fieldRange := by simpa [f] using hrange a
      _ = (f b).fieldRange := by
        simpa [f] using (hrange b).symm
      _ = τ.fieldRange :=
        congrArg (fun g : E →ₐ[F] AlgebraicClosure E => g.fieldRange) hb
  · intro hnormal
    let _ : Normal F E := hnormal
    rw [Field.finSepDegree]
    exact (Nat.card_congr
      (Normal.algHomEquivAut F (AlgebraicClosure E) E)).symm

/-! ## Embeddings into an extension -/

/- For a normal algebraic extension, all embeddings into a fixed target form
   either the empty set or one orbit under the source automorphism group. -/
theorem normal_embeddings_empty_or_differ_by_automorphism
    {K L E : Type*} [Field K] [Field L] [Field E]
    [Algebra K L] [Algebra K E] [Normal K L] :
    (¬ Nonempty (L →ₐ[K] E)) ∨
      ∃ τ : L →ₐ[K] E,
        ∀ φ : L →ₐ[K] E,
          ∃ σ : Gal(L / K), φ = τ.comp σ.toAlgHom := by
  by_cases h : Nonempty (L →ₐ[K] E)
  · right
    obtain ⟨τ⟩ := h
    refine ⟨τ, ?_⟩
    intro φ
    have hrange (ψ : L →ₐ[K] E) : ψ.fieldRange = τ.fieldRange := by
      let e : L ≃ₐ[K] τ.fieldRange := τ.equivFieldRange
      let _ : Normal K τ.fieldRange :=
        Normal.of_algEquiv e (h := (inferInstance : Normal K L))
      let g : τ.fieldRange →ₐ[K] E := ψ.comp e.symm.toAlgHom
      have hg : g.fieldRange = τ.fieldRange :=
        AlgHom.fieldRange_of_normal g
      have hcomp : g.comp e.toAlgHom = ψ := by
        ext x
        simp [g, e]
      have hcomp_range : (g.comp e.toAlgHom).fieldRange = g.fieldRange := by
        apply SetLike.ext'
        simp only [AlgHom.coe_fieldRange, AlgHom.coe_comp, Set.range_comp]
        apply Set.Subset.antisymm
        · rintro z ⟨y, ⟨x, rfl⟩, rfl⟩
          exact ⟨e x, rfl⟩
        · rintro z ⟨y, rfl⟩
          exact ⟨y, ⟨e.symm y, by simp⟩, rfl⟩
      exact (congrArg (fun f : L →ₐ[K] E => f.fieldRange) hcomp).symm.trans
        (hcomp_range.trans hg)
    let φ' : L →ₐ[K] τ.fieldRange :=
      (IntermediateField.equivOfEq (hrange φ)).toAlgHom.comp
        φ.equivFieldRange.toAlgHom
    have hφ' : Function.Bijective φ' := by
      dsimp [φ']
      exact (IntermediateField.equivOfEq (hrange φ)).bijective.comp
        φ.equivFieldRange.bijective
    let σ : Gal(L / K) :=
      AlgEquiv.ofBijective
        ((τ.equivFieldRange).symm.toAlgHom.comp φ')
        ((τ.equivFieldRange).symm.bijective.comp hφ')
    refine ⟨σ, ?_⟩
    ext x
    calc
      φ x = (φ.equivFieldRange x : E) := rfl
      _ = (IntermediateField.equivOfEq (hrange φ) (φ.equivFieldRange x) : E) := rfl
      _ = (τ.equivFieldRange (σ x) : E) := by
        have hs : σ x = (τ.equivFieldRange).symm (φ' x) := by
          change (τ.equivFieldRange).symm (φ' x) =
            (τ.equivFieldRange).symm (φ' x)
          rfl
        rw [hs]
        simp [φ']
      _ = τ (σ x) := rfl
  · left
    exact h

end

end Formalization.Books.Fields.Unit15
