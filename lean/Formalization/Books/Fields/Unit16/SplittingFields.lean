import Mathlib.FieldTheory.SeparableDegree
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.LinearAlgebra.PiTensorProduct.Finite

/-!
# Fields, Chapter 16: Splitting fields

The source's splitting-field predicate is Mathlib's canonical
`Polynomial.IsSplittingField`, with `Polynomial.SplittingField` providing the
chosen construction.  Normal closures are represented by
`IntermediateField.normalClosure` and its predicate `IsNormalClosure`.
For the displayed tensor product, `PiTensorProduct` gives the finite indexed
tensor product of copies of a field as a `K`-algebra.
-/

namespace Formalization.Books.Fields.Unit16

noncomputable section

open Polynomial
open scoped BigOperators TensorProduct

universe u v w

/-! ## Splitting fields -/

/- The source's “smallest extension” is the universal property of
   `Polynomial.SplittingField`: it splits the polynomial, embeds into every
   field in which the polynomial splits, and is unique up to an algebra
   equivalence among splitting fields.  The normality assertion is the
   existing `Polynomial.SplittingField.instNormal` instance. -/
theorem splitting_field_spec
    {F : Type u} [Field F] {P : F[X]} (_hP : P.natDegree ≠ 0) :
    P.IsSplittingField F P.SplittingField ∧
      Normal F P.SplittingField ∧
        (∀ {L : Type v} [Field L] [Algebra F L],
          (P.map (algebraMap F L)).Splits →
            Nonempty (P.SplittingField →ₐ[F] L)) ∧
          (∀ {L : Type v} [Field L] [Algebra F L]
              [_hL : P.IsSplittingField F L],
            Nonempty (L ≃ₐ[F] P.SplittingField)) := by
  refine ⟨inferInstance, inferInstance, ?_, ?_⟩
  · intro L _ _ hL
    exact ⟨SplittingField.lift P hL⟩
  · intro L _ _ hL
    exact ⟨IsSplittingField.algEquiv L P (h := hL)⟩

/- The source's definition introduces no new object: the canonical object
   `P.SplittingField`, together with the predicate above, is the Mathlib
   splitting field of `P` over `F`. -/

/-! ## Normal closures -/

/- `IntermediateField.normalClosure F E L` is the smallest intermediate field
   containing the images of all `F`-algebra embeddings of `E` into `L`.
   The theorem below records the finite, normal, and uniqueness properties in
   a normal ambient extension. -/
theorem normal_closure_spec
    {F E L : Type*} [Field F] [Field E] [Field L]
    [Algebra F E] [Algebra F L] [Algebra E L] [IsScalarTower F E L]
    [FiniteDimensional F E] [Normal F L] :
    let K := IntermediateField.normalClosure F E L
    Normal F K ∧
      FiniteDimensional F K ∧
        FiniteDimensional E K ∧
          IsNormalClosure F E K ∧
            (∀ K' : IntermediateField F L,
              K ≤ K' ↔ ∀ φ : E →ₐ[F] L, φ.fieldRange ≤ K') ∧
            (∀ {T : Type*} [Field T] [Algebra F T] [Algebra E T]
                [IsScalarTower F E T] [_hT : IsNormalClosure F E T],
              Nonempty (T ≃ₐ[E] K)) := by
  dsimp only
  let hEL : Nonempty (E →ₐ[F] L) := ⟨IsScalarTower.toAlgHom F E L⟩
  refine ⟨inferInstance, inferInstance, ?_, inferInstance, ?_, ?_⟩
  · exact Module.Finite.right F E (IntermediateField.normalClosure F E L)
  · intro K'
    exact normalClosure_le_iff
  · intro T _ _ _ _ hT
    let iT : E →ₐ[F] T := IsScalarTower.toAlgHom F E T
    let iK : E →ₐ[F] IntermediateField.normalClosure F E L :=
      IsScalarTower.toAlgHom F E (IntermediateField.normalClosure F E L)
    let g : T ≃ₐ[F] IntermediateField.normalClosure F E L :=
      IsNormalClosure.equiv (F := F) (K := E) (L := T)
        (L' := IntermediateField.normalClosure F E L) (h := hT)
    let u : E →ₐ[F] IntermediateField.normalClosure F E L := g.toAlgHom.comp iT
    let η : u.fieldRange ≃ₐ[F] iK.fieldRange :=
      u.equivFieldRange.symm.trans iK.equivFieldRange
    let σ : Gal(IntermediateField.normalClosure F E L / F) := η.liftNormal _
    let q : T →ₐ[F] IntermediateField.normalClosure F E L := σ.toAlgHom.comp g.toAlgHom
    let qE : T →ₐ[E] IntermediateField.normalClosure F E L :=
      { q.toRingHom with
        commutes' := by
          intro x
          change q (algebraMap E T x) = algebraMap E
            (IntermediateField.normalClosure F E L) x
          change σ (g (algebraMap E T x)) = algebraMap E
            (IntermediateField.normalClosure F E L) x
          rw [show g (algebraMap E T x) = u x by rfl]
          rw [← show (algebraMap u.fieldRange
            (IntermediateField.normalClosure F E L)) (u.equivFieldRange x) = u x by rfl]
          rw [η.liftNormal_commutes]
          simp [η, iK]
        }
    exact ⟨AlgEquiv.ofBijective qE (σ.bijective.comp g.bijective)⟩

/- The algebra over `E` on the normal closure is the canonical one supplied
   by Mathlib's `normalClosure.algebra`; finiteness over `E` follows from the
   tower finiteness theorem once finiteness over `F` is known. -/
theorem normal_closure_finite_over_middle
    {F E L : Type*} [Field F] [Field E] [Field L]
    [Algebra F E] [Algebra F L] [Algebra E L] [IsScalarTower F E L]
    [FiniteDimensional F E] :
    FiniteDimensional E (IntermediateField.normalClosure F E L) := by
  exact Module.Finite.right F E (IntermediateField.normalClosure F E L)

/- Choosing an algebraic closure supplies the ambient normal extension needed
   for existence.  The `letI`s make the chosen embedding of the finite
   extension into the algebraic closure the algebra structure used on the
   normal closure. -/
theorem exists_normal_closure_of_finite_extension
    {F : Type u} {E : Type v} [Field F] [Field E] [Algebra F E]
    [FiniteDimensional F E] :
    ∃ ι : E →ₐ[F] AlgebraicClosure F,
      letI : Algebra E (AlgebraicClosure F) := ι.toRingHom.toAlgebra
      letI : IsScalarTower F E (AlgebraicClosure F) :=
        IsScalarTower.of_algebraMap_eq fun x => (ι.commutes x).symm
      let K := IntermediateField.normalClosure F E (AlgebraicClosure F)
      Nonempty (E →ₐ[F] K) ∧
        Normal F K ∧ FiniteDimensional E K ∧ IsNormalClosure F E K := by
  let ι : E →ₐ[F] AlgebraicClosure F := IsAlgClosed.lift
  refine ⟨ι, ?_⟩
  let hAlg : Algebra E (AlgebraicClosure F) := ι.toRingHom.toAlgebra
  let hTower : IsScalarTower F E (AlgebraicClosure F) :=
    IsScalarTower.of_algebraMap_eq fun x => (ι.commutes x).symm
  let K := IntermediateField.normalClosure F E (AlgebraicClosure F)
  let hι : Nonempty (E →ₐ[F] AlgebraicClosure F) := ⟨ι⟩
  refine ⟨⟨IsScalarTower.toAlgHom F E K⟩, inferInstance, ?_, inferInstance⟩
  exact Module.Finite.right F E K

/-! ## Normal closures inside a normal extension -/

/- The source's subextensions are represented by intermediate fields.  If
   `M ≤ M'`, `M'.extendScalars hM` is the same field viewed as an extension of
   `M`, so the tower and its finiteness are explicit in the conclusion. -/
theorem normal_closure_inside_normal_extension_first
    {K L : Type*} [Field K] [Field L] [Algebra K L] [Normal K L]
    (M : IntermediateField K L) [FiniteDimensional K M] :
    ∃ (M' : IntermediateField K L) (hM : M ≤ M'),
        FiniteDimensional K M' ∧ Normal K M' ∧
        FiniteDimensional M (IntermediateField.extendScalars hM) := by
  let M' := IntermediateField.normalClosure K M L
  have hM' : M ≤ M' := IntermediateField.le_normalClosure M
  refine ⟨M', hM', inferInstance, inferInstance, ?_⟩
  exact Module.Finite.right K M M'

/- In the second part, `M/K` is normal and `M'/M` is finite.  The normal
   closure of `M'` in the ambient normal field supplies `M''`; the conclusion
   records that it contains `M'`, is normal over `K`, and is finite over `M`. -/
theorem normal_closure_inside_normal_extension_second
    {K L : Type*} [Field K] [Field L] [Algebra K L] [Normal K L]
    (M M' : IntermediateField K L) (hMM' : M ≤ M')
    [hM : Normal K M]
    [FiniteDimensional M (IntermediateField.extendScalars hMM')] :
    ∃ (M'' : IntermediateField K L) (hM'M'' : M' ≤ M''),
      Normal K M'' ∧
        FiniteDimensional M (IntermediateField.extendScalars (hMM'.trans hM'M'')) := by
  classical
  let b := Module.finBasis M (IntermediateField.extendScalars hMM')
  let R : Set L := ⋃ i, (minpoly K (b i : L)).rootSet L
  let B : Set L := (M : Set L) ∪ R
  let M'' := IntermediateField.adjoin K B
  have hR : R.Finite := Set.finite_iUnion fun i =>
    (minpoly K (b i : L)).rootSet_finite L
  let hRfin : Finite R := Set.finite_coe_iff.mpr hR
  have hM'M'' : M' ≤ M'' := by
    have hMle : M ≤ M'' := by
      intro x hx
      exact IntermediateField.subset_adjoin K B (Or.inl hx)
    intro x hx
    let y : IntermediateField.extendScalars hMM' :=
      ⟨x, hx⟩
    change (y : L) ∈ M''
    have hb : ∀ i, (b i : L) ∈ M'' := by
      intro i
      apply IntermediateField.subset_adjoin K
      exact Or.inr <| Set.mem_iUnion.mpr ⟨i,
        (Polynomial.mem_rootSet_of_ne
          (minpoly.ne_zero ((inferInstance : Normal K L).isIntegral (b i : L)))).2
          (minpoly.aeval K (b i : L))⟩
    rw [show (y : L) =
        ∑ i, ((b.repr y i : M) : L) * (b i : L) by
      have hsum := congr_arg (fun z : IntermediateField.extendScalars hMM' => (z : L))
        (b.sum_repr y)
      rw [← hsum]
      change (IntermediateField.extendScalars hMM').val
          (∑ i, (b.repr y i) • b i) = _
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro i hi
      change (algebraMap M L (b.repr y i)) * (b i : L) = _
      rfl]
    exact M''.toSubalgebra.sum_mem fun i _ =>
      M''.toSubalgebra.mul_mem (hMle (b.repr y i).property) (hb i)
  refine ⟨M'', hM'M'', ?_, ?_⟩
  · have hbase : ∀ x ∈ B,
        IsIntegral K x ∧ ((minpoly K x).map (algebraMap K M'')).Splits := by
      intro x hx
      rcases hx with hxM | hxR
      · let xM : M := ⟨x, hxM⟩
        refine ⟨IntermediateField.coe_isIntegral_iff.mpr (hM.isIntegral xM), ?_⟩
        have hmin : minpoly K x = minpoly K xM := by
          change minpoly K (algebraMap M L xM) = minpoly K xM
          exact minpoly.algebraMap_eq (algebraMap M L).injective xM
        rw [hmin]
        apply IntermediateField.splits_of_splits
          ((hM.splits xM).of_isScalarTower L) (F := M'')
        intro y hy
        exact IntermediateField.subset_adjoin K B <|
          Or.inl ((IntermediateField.splits_iff_mem
            (F := M) ((hM.splits xM).of_isScalarTower L)).1 (hM.splits xM) y hy)
      · rcases Set.mem_iUnion.mp hxR with ⟨i, hx⟩
        have hi : IsIntegral K (b i : L) := (inferInstance : Normal K L).isIntegral _
        have hsplit : ((minpoly K (b i : L)).map (algebraMap K M'')).Splits := by
          apply IntermediateField.splits_of_splits ((inferInstance : Normal K L).splits _)
          intro y hy
          exact IntermediateField.subset_adjoin K B <|
            Or.inr (Set.mem_iUnion.mpr ⟨i, hy⟩)
        refine ⟨(isAlgebraic_of_mem_rootSet hx).isIntegral, ?_⟩
        exact hsplit.of_dvd
          (map_ne_zero (minpoly.ne_zero hi))
          ((map_dvd_map' _).mpr (minpoly.dvd K x
            (aeval_eq_zero_of_mem_rootSet hx)))
    let hAlgM : Algebra.IsAlgebraic K M'' :=
      IntermediateField.isAlgebraic_adjoin fun x hx => (hbase x hx).1
    apply normal_iff.mpr
    intro x
    have hs := IntermediateField.splits_of_mem_adjoin K L (S := B) hbase x.property
    have hminx : minpoly K (x : L) = minpoly K x := by
      change minpoly K (algebraMap M'' L x) = minpoly K x
      exact minpoly.algebraMap_eq (algebraMap M'' L).injective x
    rw [hminx] at hs
    exact ⟨Algebra.IsIntegral.isIntegral x, hs⟩
  · let A := IntermediateField.adjoin M R
    let A_K : IntermediateField K L := A.restrictScalars K
    have hM''A : M'' ≤ A_K := by
      change IntermediateField.adjoin K B ≤ A_K
      rw [IntermediateField.adjoin_le_iff]
      intro x hx
      rcases hx with hxM | hxR
      · change x ∈ A
        exact A.algebraMap_mem ⟨x, hxM⟩
      · change x ∈ A
        exact IntermediateField.subset_adjoin M R hxR
    have hA : A ≤ IntermediateField.extendScalars (hMM'.trans hM'M'') := by
      rw [IntermediateField.adjoin_le_iff]
      intro x hx
      change x ∈ M''
      exact IntermediateField.subset_adjoin K B (Or.inr hx)
    have hEq : IntermediateField.extendScalars (hMM'.trans hM'M'') = A := by
      apply IntermediateField.ext
      intro x
      constructor
      · intro hx
        change x ∈ M'' at hx
        exact hM''A hx
      · intro hx
        exact hA hx
    rw [hEq]
    exact IntermediateField.finiteDimensional_adjoin fun x hx => by
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
      exact (isAlgebraic_of_mem_rootSet hi).tower_top M |>.isIntegral

/-! ## The tensor-product description of a normal closure -/

/- The source's map sends a pure tensor to the product of the images under an
   enumeration of all `K`-embeddings of `L` into the normal closure.  The
   indexed tensor product is already a `K`-algebra in Mathlib, and
   `PiTensorProduct.liftAlgHom` is its universal construction. -/
noncomputable def normalClosureTensorProductMap
    {K L M : Type*} [Field K] [Field L] [Field M]
    [Algebra K L] [Algebra K M]
    (e : Fin (Field.finSepDegree K L) ≃ (L →ₐ[K] M)) :
    (⨂[K] _ : Fin (Field.finSepDegree K L), L) →ₐ[K] M :=
  PiTensorProduct.liftAlgHom
    ((MultilinearMap.mkPiAlgebra K (Fin (Field.finSepDegree K L)) M).compLinearMap
      (fun i => (e i).toLinearMap))
    (by simp)
    (by
      intro x y
      simp [MultilinearMap.compLinearMap_apply,
        MultilinearMap.mkPiAlgebra_apply, Finset.prod_mul_distrib])

theorem normalClosureTensorProductMap_tprod
    {K L M : Type*} [Field K] [Field L] [Field M]
    [Algebra K L] [Algebra K M]
    (e : Fin (Field.finSepDegree K L) ≃ (L →ₐ[K] M))
    (x : Fin (Field.finSepDegree K L) → L) :
    normalClosureTensorProductMap e (PiTensorProduct.tprod K x) =
      ∏ i, e i (x i) := by
  change PiTensorProduct.lift
      ((MultilinearMap.mkPiAlgebra K (Fin (Field.finSepDegree K L)) M).compLinearMap
        (fun i => (e i).toLinearMap)) (PiTensorProduct.tprod K x) = _
  rw [PiTensorProduct.lift.tprod]
  simp [MultilinearMap.compLinearMap_apply, MultilinearMap.mkPiAlgebra_apply]

/- The finite-extension tensor-product assertion is stated with the canonical
   `IsNormalClosure` predicate.  Its normality is the existing
   `IsNormalClosure.normal` theorem, while the last inequality is exactly
   Mathlib's `Field.finSepDegree_le_finrank`. -/
theorem normal_closure_tensor_product_surjective
    {K L M : Type*} [Field K] [Field L] [Field M]
    [Algebra K L] [Algebra K M] [Algebra L M] [IsScalarTower K L M]
    [FiniteDimensional K L]
    [hM : IsNormalClosure K L M] :
    ∃ e : Fin (Field.finSepDegree K L) ≃ (L →ₐ[K] M),
      Function.Surjective (normalClosureTensorProductMap e) ∧
        Field.finSepDegree K L ≤ Module.finrank K L := by
  classical
  let hAlgKL : Algebra.IsAlgebraic K L := Algebra.IsAlgebraic.of_finite K L
  have hcard : Field.finSepDegree K L = Nat.card (L →ₐ[K] M) :=
    Field.finSepDegree_eq_of_adjoin_splits K L M (IntermediateField.adjoin_univ K L) <| by
      intro x _
      exact ⟨Algebra.IsIntegral.isIntegral x, hM.splits x⟩
  let e : Fin (Field.finSepDegree K L) ≃ (L →ₐ[K] M) :=
    Fintype.equivOfCardEq (by simpa [Nat.card_eq_fintype_card] using hcard)
  refine ⟨e, ?_, Field.finSepDegree_le_finrank K L⟩
  let f := normalClosureTensorProductMap e
  let hFin : Module.Finite K f.range := Module.Finite.range f.toLinearMap
  let hAlgRange : Algebra.IsAlgebraic K f.range := Algebra.IsAlgebraic.of_finite K f.range
  let S : IntermediateField K M := Algebra.IsAlgebraic.toIntermediateField f.range
  have hclosure : IntermediateField.normalClosure K L M = (⊤ : IntermediateField K M) :=
    (Algebra.IsAlgebraic.isNormalClosure_iff (F := K) (K := L) (L := M)).1 hM |>.2
  have hle : IntermediateField.normalClosure K L M ≤ S := by
    rw [normalClosure_le_iff]
    intro φ y hy
    obtain ⟨x, rfl⟩ := hy
    obtain ⟨i, hi⟩ := e.surjective φ
    let z : Fin (Field.finSepDegree K L) → L := Function.update (fun _ => 1) i x
    have hz : f (PiTensorProduct.tprod K z) = φ x := by
      rw [normalClosureTensorProductMap_tprod]
      rw [Fintype.prod_eq_single i]
      · simp [z, hi]
      · intro j hji
        simp [z, hji]
    change φ x ∈ S
    change φ x ∈ f.range
    exact ⟨PiTensorProduct.tprod K z, hz⟩
  have hS : S = (⊤ : IntermediateField K M) := by
    apply top_unique
    rw [← hclosure]
    exact hle
  intro y
  have hy : y ∈ S := by rw [hS]; trivial
  change y ∈ f.range at hy
  exact hy

end

end Formalization.Books.Fields.Unit16
