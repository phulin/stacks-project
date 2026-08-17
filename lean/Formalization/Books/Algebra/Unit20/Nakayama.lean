import Mathlib.Algebra.Module.LocalizedModule.Submodule
import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.RingTheory.Ideal.Cotangent
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.RingTheory.Jacobson.Ideal
import Mathlib.RingTheory.LocalRing.ResidueField.Fiber
import Mathlib.RingTheory.Nakayama
import Mathlib.RingTheory.Localization.AtPrime.Basic

/-!
# Commutative Algebra, Chapter 20: Nakayama's lemma

The source's finite modules, ideal actions, localizations, residue fields, and
cotangent spaces use Mathlib's canonical interfaces.  The declarations below
record the twelve numbered forms of Nakayama's lemma, its localization form
and stated special cases, and the final local-ring surjectivity criterion.
-/

namespace Formalization.Books.Algebra.Unit20

universe u v w

noncomputable section

open Set
open scoped Pointwise TensorProduct

/-! ## The twelve forms of Nakayama's lemma -/

/- The canonical normalization of ``f ∈ 1 + I`` is `f - 1 ∈ I`. -/

/-- Nakayama, part (1): a finite module satisfying `IM = M` has a scalar in
`1 + I` that annihilates it. -/
theorem nakayama_part_one
    {R : Type u} {M : Type v} [CommRing R]
    [AddCommGroup M] [Module R M] (I : Ideal R) [Module.Finite R M]
    (hIM : I • (⊤ : Submodule R M) = ⊤) :
    ∃ f : R, f - 1 ∈ I ∧ ∀ m : M, f • m = 0 := by
  sorry

/-- Nakayama, part (2): the Jacobson-radical version of part (1). -/
theorem nakayama_part_two
    {R : Type u} {M : Type v} [CommRing R]
    [AddCommGroup M] [Module R M] (I : Ideal R) [Module.Finite R M]
    (hIM : I • (⊤ : Submodule R M) = ⊤)
    (hI : I ≤ Ring.jacobson R) :
    Subsingleton M := by
  sorry

/-- Nakayama, part (3): after adding `IN'` to `N`, localization at a scalar
in `1 + I` makes `N` equal to the localized ambient module. -/
theorem nakayama_part_three
    {R : Type u} {M : Type v} [CommRing R]
    [AddCommGroup M] [Module R M] (I : Ideal R)
    (N N' : Submodule R M) [Module.Finite R N']
    (hM : (⊤ : Submodule R M) = N ⊔ I • N') :
    ∃ f : R, f - 1 ∈ I ∧
      f • (⊤ : Submodule R M) ≤ N ∧
      N.localized (Submonoid.powers f) = ⊤ := by
  sorry

/-- Nakayama, part (4): the Jacobson-radical version of part (3). -/
theorem nakayama_part_four
    {R : Type u} {M : Type v} [CommRing R]
    [AddCommGroup M] [Module R M] (I : Ideal R)
    (N N' : Submodule R M) [Module.Finite R N']
    (hM : (⊤ : Submodule R M) = N ⊔ I • N')
    (hI : I ≤ Ring.jacobson R) :
    N = ⊤ := by
  sorry

/-- Nakayama, part (5): surjectivity modulo `I` becomes surjectivity after
localizing at some scalar in `1 + I`. -/
theorem nakayama_part_five
    {R : Type u} {M : Type v} {N : Type w} [CommRing R]
    [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N]
    (I : Ideal R) (φ : N →ₗ[R] M) [Module.Finite R M]
    (hφ : Function.Surjective
      ((I • (⊤ : Submodule R N)).mapQ (I • (⊤ : Submodule R M)) φ
        (Submodule.smul_top_le_comap_smul_top I φ))) :
    ∃ f : R, f - 1 ∈ I ∧
      Function.Surjective (LocalizedModule.map (Submonoid.powers f) φ) := by
  sorry

/-- Nakayama, part (6): the Jacobson-radical version of part (5). -/
theorem nakayama_part_six
    {R : Type u} {M : Type v} {N : Type w} [CommRing R]
    [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N]
    (I : Ideal R) (φ : N →ₗ[R] M) [Module.Finite R M]
    (hφ : Function.Surjective
      ((I • (⊤ : Submodule R N)).mapQ (I • (⊤ : Submodule R M)) φ
        (Submodule.smul_top_le_comap_smul_top I φ)))
    (hI : I ≤ Ring.jacobson R) :
    Function.Surjective φ := by
  sorry

/-- Nakayama, part (7): a finite generating family modulo `I` generates after
localization at a scalar in `1 + I`. -/
theorem nakayama_part_seven
    {R : Type u} {M : Type v} [CommRing R]
    [AddCommGroup M] [Module R M] (I : Ideal R) (n : ℕ) (x : Fin n → M)
    [Module.Finite R M]
    (hx : Submodule.span R
      (Set.range (fun i => (I • (⊤ : Submodule R M)).mkQ (x i))) = ⊤) :
    ∃ f : R, f - 1 ∈ I ∧
      Submodule.span (Localization.Away f)
        (Set.range (fun i =>
          LocalizedModule.mkLinearMap (Submonoid.powers f) M (x i))) = ⊤ := by
  sorry

/-- Nakayama, part (8): the Jacobson-radical version of part (7). -/
theorem nakayama_part_eight
    {R : Type u} {M : Type v} [CommRing R]
    [AddCommGroup M] [Module R M] (I : Ideal R) (n : ℕ) (x : Fin n → M)
    [Module.Finite R M]
    (hx : Submodule.span R
      (Set.range (fun i => (I • (⊤ : Submodule R M)).mkQ (x i))) = ⊤)
    (hI : I ≤ Ring.jacobson R) :
    Submodule.span R (Set.range x) = ⊤ := by
  sorry

/-- Nakayama, part (9): finiteness is unnecessary when the ideal is nilpotent. -/
theorem nakayama_part_nine
    {R : Type u} {M : Type v} [CommRing R]
    [AddCommGroup M] [Module R M] (I : Ideal R)
    (hIM : I • (⊤ : Submodule R M) = ⊤) (hI : IsNilpotent I) :
    Subsingleton M := by
  sorry

/-- Nakayama, part (10): the nilpotent version of part (4). -/
theorem nakayama_part_ten
    {R : Type u} {M : Type v} [CommRing R]
    [AddCommGroup M] [Module R M] (I : Ideal R)
    (N N' : Submodule R M)
    (hM : (⊤ : Submodule R M) = N ⊔ I • N') (hI : IsNilpotent I) :
    N = ⊤ := by
  sorry

/-- Nakayama, part (11): the nilpotent version of part (6). -/
theorem nakayama_part_eleven
    {R : Type u} {M : Type v} {N : Type w} [CommRing R]
    [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N]
    (I : Ideal R) (φ : N →ₗ[R] M)
    (hφ : Function.Surjective
      ((I • (⊤ : Submodule R N)).mapQ (I • (⊤ : Submodule R M)) φ
        (Submodule.smul_top_le_comap_smul_top I φ)))
    (hI : IsNilpotent I) :
    Function.Surjective φ := by
  sorry

/-- Nakayama, part (12): arbitrary generating families lift across a
nilpotent ideal. -/
theorem nakayama_part_twelve
    {R : Type u} {M : Type v} {A : Type w} [CommRing R]
    [AddCommGroup M] [Module R M] (I : Ideal R) (x : A → M)
    (hx : Submodule.span R
      (Set.range (fun a => (I • (⊤ : Submodule R M)).mkQ (x a))) = ⊤)
    (hI : IsNilpotent I) :
    Submodule.span R (Set.range x) = ⊤ := by
  sorry

/-! ## Localization form and the two stated special cases -/

/-- If the images of a finite family generate `S⁻¹(M/IM)`, they generate
`M_f` for some `f ∈ S + I`. -/
theorem nakayama_localization
    {R : Type u} {M : Type v} [CommRing R]
    [AddCommGroup M] [Module R M] (S : Submonoid R) (I : Ideal R)
    [Module.Finite R M] (n : ℕ) (x : Fin n → M)
    (hx : Submodule.span (Localization (S.map (Ideal.Quotient.mk I).toMonoidHom))
      (Set.range (fun i =>
        LocalizedModule.mkLinearMap
          (S.map (Ideal.Quotient.mk I).toMonoidHom)
          (M ⧸ (I • (⊤ : Submodule R M)))
          ((I • (⊤ : Submodule R M)).mkQ (x i)))) = ⊤) :
    ∃ f : R, f ∈ (S : Set R) + (I : Set R) ∧
      Submodule.span (Localization.Away f)
        (Set.range (fun i =>
          LocalizedModule.mkLinearMap (Submonoid.powers f) M (x i))) = ⊤ := by
  sorry

/-- Special case `I = 0` of `nakayama_localization`. -/
theorem nakayama_localization_zero
    {R : Type u} {M : Type v} [CommRing R]
    [AddCommGroup M] [Module R M] (S : Submonoid R)
    [Module.Finite R M] (n : ℕ) (x : Fin n → M)
    (hx : Submodule.span (Localization S)
      (Set.range (fun i => LocalizedModule.mkLinearMap S M (x i))) = ⊤) :
    ∃ f : R, f ∈ (S : Set R) ∧
      Submodule.span (Localization.Away f)
        (Set.range (fun i =>
          LocalizedModule.mkLinearMap (Submonoid.powers f) M (x i))) = ⊤ := by
  sorry

/-- Special case `I = p` and `S = R \ p`: generators of the fibre
`M ⊗ κ(p)` generate `M_f` for some `f ∉ p`. -/
theorem nakayama_localization_at_prime
    {R : Type u} {M : Type v} [CommRing R]
    [AddCommGroup M] [Module R M] (p : Ideal R) [p.IsPrime]
    [Module.Finite R M] (n : ℕ) (x : Fin n → M)
    (hx : Submodule.span p.ResidueField
      (Set.range (fun i => (1 : p.ResidueField) ⊗ₜ[R] x i)) = ⊤) :
    ∃ f : R, f ∉ p ∧
      Submodule.span (Localization.Away f)
        (Set.range (fun i =>
          LocalizedModule.mkLinearMap (Submonoid.powers f) M (x i))) = ⊤ := by
  sorry

/-! ## Surjectivity criterion for a local homomorphism -/

/-- A local map satisfying the four hypotheses in the source is surjective.
The cotangent spaces use Mathlib's canonical `Ideal.Cotangent` interface. -/
theorem local_ring_hom_surjective_of_residueField_bijective_of_cotangent_surjective
    {A : Type u} {B : Type v} [CommRing A] [CommRing B]
    [IsLocalRing A] [IsLocalRing B] [Algebra A B]
    [IsLocalHom (algebraMap A B)] [Module.Finite A B]
    (hB : (IsLocalRing.maximalIdeal B).FG)
    (hres : Function.Bijective
      (IsLocalRing.ResidueField.map (algebraMap A B)))
    (hcot : Function.Surjective
      (Ideal.mapCotangent (IsLocalRing.maximalIdeal A)
        (IsLocalRing.maximalIdeal B) (Algebra.ofId A B)
        (by
          change IsLocalRing.maximalIdeal A ≤
            (IsLocalRing.maximalIdeal B).comap (algebraMap A B)
          rw [IsLocalRing.maximalIdeal_comap]))) :
    Function.Surjective (algebraMap A B) := by
  sorry

end

end Formalization.Books.Algebra.Unit20
