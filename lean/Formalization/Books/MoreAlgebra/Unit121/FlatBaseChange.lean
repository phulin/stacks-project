/-
# More on Algebra, Chapter 121: flat base change
-/

import Formalization.Books.MoreAlgebra.Unit121.Multiplication
import Mathlib.LinearAlgebra.Charpoly.BaseChange
import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.LocalRing.Length

namespace Formalization.Books.MoreAlgebra.Unit121

noncomputable section

open CategoryTheory
open scoped TensorProduct

/-! ## Base change of the pair -/

/-- The endomorphism on `S ⊗[R] M` induced by an `R`-linear endomorphism of `M`.  The
`AlgebraTensorModule` API supplies the canonical `S`-linear map. -/
def baseChangeEnd
    {R S M : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup M] [Module R M] (φ : Module.End R M) :
    Module.End S (S ⊗[R] M) :=
  TensorProduct.AlgebraTensorModule.lTensor S S φ

/-- The chapter's base-change endomorphism is Mathlib's extension of scalars. -/
theorem baseChangeEnd_eq_baseChange
    {R S M : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup M] [Module R M] (φ : Module.End R M) :
    baseChangeEnd (S := S) φ = φ.baseChange S :=
  rfl

/-- Application of the base-changed endomorphism to a pure tensor. -/
@[simp]
theorem baseChangeEnd_tmul
    {R S M : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup M] [Module R M] (φ : Module.End R M) (s : S) (m : M) :
    baseChangeEnd (S := S) φ (s ⊗ₜ[R] m) = s ⊗ₜ[R] φ m :=
  rfl

/-- Base change of a finite-length endomorphism, once finite length of the tensor product has
been supplied. -/
def baseChangePair
    {R S : Type*} [CommRing R] [CommRing S]
    [IsLocalRing R] [IsLocalRing S] [Algebra R S]
    (X : FiniteLengthEndomorphism R)
    (hBase : IsFiniteLength S (S ⊗[R] X.carrier)) :
    FiniteLengthEndomorphism S :=
  { carrier := ModuleCat.of S (S ⊗[R] X.carrier)
    finite_length := hBase
    endomorphism := ModuleCat.ofHom (baseChangeEnd X.endomorphism.hom) }

/-- The endomorphism field of `baseChangePair`, exposed without unfolding the package. -/
@[simp]
theorem baseChangePair_endomorphism_hom
    {R S : Type*} [CommRing R] [CommRing S]
    [IsLocalRing R] [IsLocalRing S] [Algebra R S]
    (X : FiniteLengthEndomorphism R)
    (hBase : IsFiniteLength S (S ⊗[R] X.carrier)) :
    (baseChangePair X hBase).endomorphism.hom = baseChangeEnd X.endomorphism.hom :=
  rfl

/-! ## Finiteness of the base change -/

/-- The tensor product has finite length under the flat local base-change hypotheses of the
source. -/
theorem finiteLength_flat_baseChange
    {R S : Type*} [CommRing R] [CommRing S]
    [IsLocalRing R] [IsLocalRing S] [Algebra R S]
    [IsLocalHom (algebraMap R S)] [Module.Flat R S]
    (_hfiber : Module.length S
        (S ⧸ (IsLocalRing.maximalIdeal R).map (algebraMap R S)) < ⊤)
    (X : FiniteLengthEndomorphism R) :
    IsFiniteLength S (S ⊗[R] X.carrier) := by
  apply Module.length_ne_top_iff.mp
  rw [IsLocalRing.length_baseChange R S X.carrier]
  exact WithTop.mul_ne_top (Module.length_ne_top_iff.mpr X.finite_length)
    (ne_of_lt _hfiber)

noncomputable def fiberLengthNat
    {R S : Type*} [CommRing R] [CommRing S]
    [IsLocalRing R] [IsLocalRing S] [Algebra R S]
    (_hfiber : Module.length S
        (S ⧸ (IsLocalRing.maximalIdeal R).map (algebraMap R S)) < ⊤) : ℕ :=
  (Module.length S (S ⧸ (IsLocalRing.maximalIdeal R).map (algebraMap R S))).toNat

def residueFieldMap
    {R S : Type*} [CommRing R] [CommRing S]
    [IsLocalRing R] [IsLocalRing S] [Algebra R S]
    [IsLocalHom (algebraMap R S)] :
    IsLocalRing.ResidueField R →+* IsLocalRing.ResidueField S :=
  IsLocalRing.ResidueField.map (algebraMap R S)

/-! ## Lemma `lemma-flat-base-change-det` -/

/-
Proof roadmap (B3966).  The statement is sound, but neither
`IsLocalRing.length_baseChange` nor `LinearMap.det_baseChange` by itself speaks about the
chapter's `determinant`: that invariant is a product over a chosen stable composition series.
The proof therefore has to connect two filtrations explicitly.

1. Fix the names

     kR := IsLocalRing.ResidueField R,
     kS := IsLocalRing.ResidueField S,
     A  := S ⧸ (IsLocalRing.maximalIdeal R).map (algebraMap R S),
     n  := fiberLengthNat hfiber,
     t  := stableCompositionSeries X.

   Install
   `letI : Module.FaithfullyFlat R S :=
     Module.FaithfullyFlat.of_flat_of_isLocalHom` (the construction is in
   `Mathlib/RingTheory/Flat/FaithfullyFlat/Algebra.lean`).  For every
   `P : StableSubmodule X.endomorphism.hom`, put
   `P_S := P.carrier.baseChange S`.  Strictness of this operation is supplied by
   `Submodule.baseChangeOrderEmbedding R X.carrier S` in
   `Mathlib/RingTheory/Flat/FaithfullyFlat/Basic.lean`.  Stability follows on pure tensors
   from `baseChangeEnd_tmul`, `P.stable`, `Submodule.baseChange_eq_span`, and
   `Submodule.tmul_mem_baseChange_of_mem` (the last two are in
   `Mathlib/LinearAlgebra/TensorProduct/Tower.lean`).  Thus `t.series` gives a stable coarse
   filtration of `baseChangePair X (finiteLength_flat_baseChange hfiber X)`, with bottom and
   top discharged by `Submodule.baseChange_bot` and `Submodule.baseChange_top`.
   Keep the helper polymorphic in the carrier universe: if `X.carrier : Type v`, the coarse
   series lives in `S ⊗[R] X.carrier : Type (max uS v)`; specializing both module types to
   one universe makes the factor equivalences fail to elaborate.

2. Prove a small local filtration-product lemma, rather than unfolding `determinant`: for a
   finite stable filtration from bottom to top, the determinant of the middle pair is the
   product of the determinants on its successive factors.  Induct on the `RelSeries` length
   and use `lemma_ses_det` from
   `Formalization/Books/MoreAlgebra/Unit121/ShortExact.lean` on the short exact sequence
   "previous submodule -> current submodule -> quotient".  The packaging pattern for the
   restricted and quotient endomorphisms is `restrictToStableSubmodule`/`factorEnd` in
   `Formalization/Books/MoreAlgebra/Unit121/Core.lean`; exactness after tensoring is
   `Module.Flat.lTensor_exact`, while surjectivity is `LinearMap.lTensor_surjective` from
   `Mathlib/LinearAlgebra/TensorProduct/RightExactness.lean`.  Use
   `Submodule.toBaseChange.toLinearEquiv` from `Mathlib/RingTheory/Flat/Basic.lean` to identify
   the tensor of a submodule with its image.  On generators, the induced quotient
   endomorphism is `(factorEnd t.series i).baseChange S`; the equality is exactly
   `baseChangeEnd_tmul`.  Record this equivalence with an explicit type

     S ⊗[R] factorModule t.series i ≃ₗ[S]
       factorModule coarseSeries i

   and its intertwining equation before invoking the filtration-product lemma.

3. Establish the residue-module compatibility used at every factor.  A convenient local
   helper has this mathematical statement: if a finite-dimensional `kS`-vector space `V`
   and `ψ : Module.End kS V` are regarded as an `S`-module and an `S`-linear endomorphism
   through `IsLocalRing.residue S`, then the chapter's `determinantOf` is `ψ.det`.
   Prove it with `determinant_eq_stableCompositionSeries_product` from `Core.lean` and an
   induction along that stable series.  At an invariant subspace `W`, ordinary determinants
   split by

     LinearMap.det_eq_det_mul_det W ψ hW

   from `Mathlib/LinearAlgebra/Determinant.lean`.  For each simple factor, compare its
   `SimplePairData.residue_endomorphism` with the quotient of `ψ` using
   `SimplePairData.residue_endomorphism_apply`; the two `kS`-module structures agree by
   `Module.ext'`, `IsLocalRing.residue_surjective`, and
   `Module.IsTorsionBySet.mk_smul`, exactly as in `Core.lean` at `simplePair_invariant`.
   Supply `Module.Free.of_divisionRing` and the finite instances explicitly before applying
   `LinearMap.det_eq_det_mul_det`.

4. Prove the formula for one factor `D := t.simple_factor i`.  Use
   `D.annihilated.module` and `D.finite_dimensional` to regard
   `M_i := factorModule t.series i` and `ψ_i := factorEnd t.series i` over `kR`.
   From `hfiber`, obtain `IsFiniteLength S A` with `Module.length_ne_top_iff`, then choose an
   `S`-module composition series `c` with
   `isFiniteLength_iff_exists_compositionSeries` (both interfaces are used in
   `Mathlib/RingTheory/LocalRing/Length.lean`).  Identify
   `S ⊗[R] M_i` with the fiber tensored with `M_i`.  Build this equivalence from
   `Algebra.TensorProduct.quotIdealMapEquivTensorQuot S
     (IsLocalRing.maximalIdeal R)` in
   `Mathlib/RingTheory/TensorProduct/Quotient.lean`, tensor commutativity/associativity, and
   `D.annihilated.mk_smul`; give it the explicit type

     S ⊗[R] M_i ≃ₗ[S] A ⊗[kR] M_i.

   Before forming the right side, install the `kR`-algebra structure on `A` using
   `Ideal.Quotient.lift (IsLocalRing.maximalIdeal R)` applied to the composite
   `R -> S -> A`; the kernel obligation is `Ideal.le_comap_map`, and `.toAlgebra` fixes the
   intended module instance.  This explicit choice is needed so that the later map to `kS`
   is the same one as `residueAlgebra (algebraMap R S)`.

   Tensor the submodules in `c` with `M_i`.  This is a stable filtration because the
   endomorphism is `1 ⊗ ψ_i`.  A `CovBy` step of `c` has quotient `kS`: follow the exact
   `isSimpleModule_iff_quot_maximal` / `eq_maximalIdeal` argument in
   `IsLocalRing.CovBy.length_baseChange` in
   `Mathlib/RingTheory/LocalRing/Length.lean`.  Consequently every successive endomorphism is
   conjugate to `ψ_i.baseChange kS`.  Step 3 and
   `LinearMap.det_baseChange` from `Mathlib/LinearAlgebra/Charpoly/BaseChange.lean` give its
   chapter determinant as

     residueFieldMap (simpleDeterminant D).

   Here install
   `letI : Algebra kR kS := residueAlgebra (algebraMap R S)` and change the resulting
   `algebraMap kR kS` to `residueFieldMap`; these are definitionally the same ring map.
   Apply the filtration-product lemma from step 2 to get the `c.length`-th power.
   Finally use `Module.length_compositionSeries c c_head c_last`, `fiberLengthNat`, and
   `ENat.toNat_natCast` to rewrite `c.series.length = n`.

5. Apply step 2 to the coarse filtration from step 1 and substitute the factor formula from
   step 4.  Rewrite the source determinant with
   `determinant_eq_stableCompositionSeries_product X t`; then use `map_prod` and
   `Finset.prod_pow` to identify

     residueFieldMap (∏ i, simpleDeterminant (t.simple_factor i)) ^ n

   with the product of the factor powers.  This is the required equality.

Do not try `simp [determinant, baseChangePair]`: it exposes the unrelated noncanonical choices
`stableCompositionSeries X` and `stableCompositionSeries (baseChangePair ...)`.  Also,
`IsLocalRing.length_baseChange` proves only the number of layers, and
`LinearMap.det_baseChange` applies only after passing to the residue-field vector-space layer;
neither closes the custom determinant goal directly.
-/

theorem lemma_flat_base_change_det
    {R S : Type*} [CommRing R] [CommRing S]
    [IsLocalRing R] [IsLocalRing S] [Algebra R S]
    [IsLocalHom (algebraMap R S)] [Module.Flat R S]
    (hfiber : Module.length S
        (S ⧸ (IsLocalRing.maximalIdeal R).map (algebraMap R S)) < ⊤)
    (X : FiniteLengthEndomorphism R) :
    residueFieldMap (R := R) (S := S) (determinant X) ^ fiberLengthNat hfiber =
      determinant (baseChangePair X (finiteLength_flat_baseChange hfiber X)) := by
  sorry

end
