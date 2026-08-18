/-
# More on Algebra, Chapter 121: flat base change
-/

import Formalization.Books.MoreAlgebra.Unit121.Multiplication
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
