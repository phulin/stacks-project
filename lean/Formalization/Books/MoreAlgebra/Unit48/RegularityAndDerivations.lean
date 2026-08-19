import Formalization.Books.MoreAlgebra.Unit47.SingularLocus
import Formalization.Books.Algebra.Unit162.NagataRings
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.RingTheory.AdicCompletion.RingHom
import Mathlib.RingTheory.Derivation.Basic
import Mathlib.RingTheory.FiniteType
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.Regular.RegularSequence

/-!
# More Algebra, Chapter 48: Regularity and derivations

This file records the definitions and theorem interfaces in the chapter.  Ring
derivations use Mathlib's `Derivation ℤ R R`; the extension predicate below
expresses commutativity with an arbitrary ring map.  Quotients are represented
by `Ideal.Quotient`, completions by Mathlib's `AdicCompletion`, and the
Nagata predicate is reused from the earlier Algebra chapter.
-/

namespace Formalization.Books.MoreAlgebra.Unit48

open Set
open scoped BigOperators

universe u

noncomputable section

/-! ## Extending derivations -/

/-- A derivation on `R` extends across `f : R →+* S` when the square with the
induced map on `S` commutes. -/
def Derivation.ExtendsTo
    {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) (D : Derivation ℤ R R) (D' : S → S) : Prop :=
  ∃ d' : Derivation ℤ S S, (∀ s, d' s = D' s) ∧ ∀ r, D' (f r) = f (D r)

/-! The estimate used to pass a derivation to the inverse system of adic
quotients. -/

/-- For `n ≥ 2`, a derivation sends `Iⁿ` into `Iⁿ⁻¹`. -/
theorem derivation_mem_ideal_pow_sub_one
    {R : Type u} [CommRing R] (D : Derivation ℤ R R) (I : Ideal R)
    {n : ℕ} (hn : 2 ≤ n) :
    ∀ x ∈ I ^ n, D x ∈ I ^ (n - 1) := by
  sorry

/-- The canonical ring map from a ring to its adic completion. -/
def adicCompletionMap
    {R : Type u} [CommRing R] (I : Ideal R) :
    R →+* AdicCompletion I R where
  toFun := AdicCompletion.of I R
  map_one' := by
    apply Subtype.ext
    funext n
    rfl
  map_mul' x y := by
    apply Subtype.ext
    funext n
    rfl
  map_zero' := by
    apply Subtype.ext
    funext n
    rfl
  map_add' x y := by
    apply Subtype.ext
    funext n
    rfl

/-- Every derivation extends to the adic completion.  The extension is chosen
by the construction from the compatible quotient maps. -/
theorem derivation_extends_to_adicCompletion
    {R : Type u} [CommRing R] (I : Ideal R) (D : Derivation ℤ R R) :
    ∃ D' : Derivation ℤ (AdicCompletion I R) (AdicCompletion I R),
      Derivation.ExtendsTo (adicCompletionMap I) D D' := by
  sorry

/-- The canonical adic-completion extension supplied by the preceding
existence theorem. -/
noncomputable def derivationAdicCompletion
    {R : Type u} [CommRing R] (I : Ideal R) (D : Derivation ℤ R R) :
    Derivation ℤ (AdicCompletion I R) (AdicCompletion I R) :=
  Classical.choose (derivation_extends_to_adicCompletion I D)

theorem derivationAdicCompletion_extends
    {R : Type u} [CommRing R] (I : Ideal R) (D : Derivation ℤ R R) :
    Derivation.ExtendsTo (adicCompletionMap I) D (derivationAdicCompletion I D) :=
  Classical.choose_spec (derivation_extends_to_adicCompletion I D)

/-- A derivation extends uniquely to a localization. -/
theorem derivation_extends_to_localization
    {R : Type u} [CommRing R] (S : Submonoid R) (D : Derivation ℤ R R) :
    ∃! D' : Derivation ℤ (Localization S) (Localization S),
      Derivation.ExtendsTo (algebraMap R (Localization S)) D D' := by
  sorry

/-- The localization extension selected by the unique-extension theorem. -/
noncomputable def derivationLocalization
    {R : Type u} [CommRing R] (S : Submonoid R) (D : Derivation ℤ R R) :
    Derivation ℤ (Localization S) (Localization S) :=
  Classical.choose (derivation_extends_to_localization S D).exists

theorem derivationLocalization_extends
    {R : Type u} [CommRing R] (S : Submonoid R) (D : Derivation ℤ R R) :
    Derivation.ExtendsTo (algebraMap R (Localization S)) D
      (derivationLocalization S D) :=
  Classical.choose_spec (derivation_extends_to_localization S D).exists

/-- The usual quotient-of-fractions formula for the localization extension. -/
theorem derivationLocalization_apply
    {R : Type u} [CommRing R] (S : Submonoid R) (D : Derivation ℤ R R)
    (r : R) (s : S) :
    derivationLocalization S D (IsLocalization.mk' (Localization S) r s) =
      IsLocalization.mk' (Localization S) (D r) s -
        IsLocalization.mk' (Localization S) (r * D s.1) (s * s) := by
  sorry

/-! The finite-type extension statement.  The localization hypothesis is
written as bijectivity of the induced canonical map between the two away
localizations. -/

/-- After a finite-type localization becomes an isomorphism, a power of the
element clears all denominators and makes the derivation extend. -/
theorem exists_derivation_extension_of_finiteType_localization
    {R R' : Type u} [CommRing R] [CommRing R']
    (f : R →+* R') (hinj : Function.Injective f)
    (hfinite : RingHom.FiniteType f) (g : R) (hg : IsRegular (f g))
    (hlocal :
      Function.Bijective
        (IsLocalization.Away.map (Localization.Away g)
          (Localization.Away (f g)) f g))
    (D : Derivation ℤ R R) :
    ∃ N : ℕ, ∃ D' : Derivation ℤ R' R',
      Derivation.ExtendsTo f ((g ^ N) • D) D' := by
  sorry

/-! The monomial identity used in the denominator-clearing argument. -/

theorem derivation_finset_prod_pow
    {R : Type u} [CommRing R] (D : Derivation ℤ R R) {n : ℕ}
    (x : Fin n → R) (e : Fin n → ℕ) :
    D (Finset.univ.prod (fun i : Fin n => x i ^ e i)) =
      Finset.univ.sum (fun i : Fin n =>
        (e i : R) *
          (Finset.univ.erase i).prod (fun j => x j ^ e j) *
            x i ^ (e i - 1) * D (x i)) := by
  sorry

/-! ## Jacobian criteria -/

/-- A hypersurface cut out by an element whose derivative is a unit is
regular. -/
theorem regularRing_quotient_of_derivation_unit
    {R : Type u} [CommRing R] [IsRegularRing R] (f : R)
    (D : Derivation ℤ R R)
    (hD : IsUnit (Ideal.Quotient.mk (Ideal.span ({f} : Set R)) (D f))) :
    IsRegularRing (R ⧸ Ideal.span ({f} : Set R)) := by
  sorry

/-- The Jacobian determinant criterion for a regular local ring. -/
theorem regularLocalRing_quotient_of_derivation_matrix_unit
    {R : Type u} [CommRing R] [IsRegularLocalRing R] (m : ℕ) (hm : 1 ≤ m)
    (f : Fin m → R) (hf : ∀ j, f j ∈ IsLocalRing.maximalIdeal R)
    (D : Fin m → Derivation ℤ R R)
    (hdet : IsUnit (Matrix.det (fun i j => D i (f j)))) :
    IsRegularLocalRing (R ⧸ Ideal.span (Set.range f)) ∧
      RingTheory.Sequence.IsRegular R (List.ofFn f) := by
  sorry

/-! ## Polynomial and purely inseparable extensions -/

/-- Adjoining an `n`th root of an element with a unit derivative preserves
regularity. -/
theorem regularRing_quotient_of_derivation_pow
    {R : Type u} [CommRing R] [IsRegularRing R] (f : R)
    (D : Derivation ℤ R R) (hD : IsUnit (D f)) (n : ℕ) (hn : 1 ≤ n) :
    IsRegularRing
      (Polynomial R ⧸
        Ideal.span ({(Polynomial.X : Polynomial R) ^ n - Polynomial.C f} :
          Set (Polynomial R))) := by
  sorry

/-- The same criterion for a polynomial with integer coefficients. -/
theorem regularRing_quotient_of_derivation_int_polynomial
    {R : Type u} [CommRing R] [IsRegularRing R] (f : R)
    (D : Derivation ℤ R R) (hD : IsUnit (D f)) (p : Polynomial ℤ) :
    IsRegularRing
      (Polynomial R ⧸
        Ideal.span
          ({Polynomial.map (algebraMap ℤ R) p - Polynomial.C f} :
            Set (Polynomial R))) := by
  sorry

/-- In characteristic `p`, a non-`p`th-power element over a Noetherian
complete local base has a derivation detecting it. -/
theorem exists_derivation_of_not_pth_power
    {B R : Type u} [CommRing B] [IsDomain B] [CommRing R]
    [Algebra R B] [Algebra.FiniteType R B]
    [IsNoetherianRing R] [IsLocalRing R]
    [IsAdicComplete (IsLocalRing.maximalIdeal R) R]
    (p : ℕ) (hp : Nat.Prime p) [CharP B p] (f : B)
    (hnot : ∀ x : FractionRing B,
      x ^ p ≠ algebraMap B (FractionRing B) f) :
    ∃ D : Derivation ℤ B B, D f ≠ 0 := by
  sorry

/-! ## J-0 and J-2 consequences -/

/-- A Noetherian complete local domain is J-0. -/
theorem isJ0_of_noetherian_complete_local_domain
    {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    [IsDomain A] [IsAdicComplete (IsLocalRing.maximalIdeal A) A] :
    Formalization.Books.MoreAlgebra.Unit47.IsJ0 A := by
  sorry

/-- The list of J-2 rings established in the chapter, together with stability
under finite-type extensions. -/
theorem isJ2_ubiquity :
    (∀ (K : Type u) [Field K],
      Formalization.Books.MoreAlgebra.Unit47.IsJ2 K) ∧
    (∀ (R : Type u) [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
      [IsAdicComplete (IsLocalRing.maximalIdeal R) R],
      Formalization.Books.MoreAlgebra.Unit47.IsJ2 R) ∧
    Formalization.Books.MoreAlgebra.Unit47.IsJ2 ℤ ∧
    (∀ (R : Type u) [CommRing R] [IsNoetherianRing R] [IsLocalRing R],
      ringKrullDim R = 1 → Formalization.Books.MoreAlgebra.Unit47.IsJ2 R) ∧
    (∀ (R : Type u) [CommRing R],
      Formalization.Books.Algebra.Unit162.IsNagataRing R →
        ringKrullDim R = 1 → Formalization.Books.MoreAlgebra.Unit47.IsJ2 R) ∧
    (∀ (R : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R]
      [IsDedekindDomain R] [CharZero (FractionRing R)],
      Formalization.Books.MoreAlgebra.Unit47.IsJ2 R) ∧
    (∀ (R S : Type u) [CommRing R] [CommRing S] (f : R →+* S),
      Formalization.Books.MoreAlgebra.Unit47.IsJ2 R →
        RingHom.FiniteType f → Formalization.Books.MoreAlgebra.Unit47.IsJ2 S) := by
  sorry

end

end Formalization.Books.MoreAlgebra.Unit48
