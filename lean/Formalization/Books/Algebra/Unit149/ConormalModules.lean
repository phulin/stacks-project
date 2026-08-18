import Formalization.Books.Algebra.Unit134.NaiveCotangentComplex
import Formalization.Books.Algebra.Unit148.FormallyUnramifiedMaps
import Mathlib.RingTheory.Extension.Cotangent.Basic
import Mathlib.RingTheory.Extension.ExtendScalars
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Ideal.Quotient.PowTransition
import Mathlib.RingTheory.Localization.Basic

/-!
# Commutative Algebra, Chapter 149: Conormal modules and universal thickenings

The source constructs a universal square-zero extension for a formally
unramified algebra.  Mathlib's `Algebra.Extension` is the canonical interface
for a surjection of algebras, and its `Cotangent` is the canonical
presentation-independent `I/I²` module.  The declarations below add the
universal property and record the quotient, localization, and differential
statements from the source section.
-/

namespace Formalization.Books.Algebra.Unit149

open scoped TensorProduct

noncomputable section

universe u

/-! ## Universal first-order thickenings -/

/--
An extension is a universal first-order thickening when its kernel is
square-zero and it has the lifting property against every square-zero ideal.

The quotient map in the lifting property is Mathlib's canonical algebra map,
so the displayed equality is precisely the commutative diagram in the source.
-/
def IsUniversalFirstOrderThickening
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    (P : Algebra.Extension.{u} R S) : Prop :=
  P.ker ^ 2 = ⊥ ∧
    ∀ {A : Type u} [CommRing A] [Algebra R A]
      (I : Ideal A) (_hI : I ^ 2 = ⊥) (a : S →ₐ[R] A ⧸ I),
      ∃! a' : P.Ring →ₐ[R] A,
        (Ideal.Quotient.mkₐ R I).comp a' =
          a.comp (IsScalarTower.toAlgHom R P.Ring S)

/-- A universal first-order thickening exists for every formally unramified map. -/
theorem exists_universal_first_order_thickening
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    (h : Algebra.FormallyUnramified R S) :
    ∃ P : Algebra.Extension.{u} R S, IsUniversalFirstOrderThickening P := by
  sorry

/-- A chosen universal first-order thickening. -/
noncomputable def universalFirstOrderThickening
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    (h : Algebra.FormallyUnramified R S) : Algebra.Extension.{u} R S :=
  Classical.choose (exists_universal_first_order_thickening h)

theorem universalFirstOrderThickening_isUniversal
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    (h : Algebra.FormallyUnramified R S) :
    IsUniversalFirstOrderThickening (universalFirstOrderThickening h) :=
  Classical.choose_spec (exists_universal_first_order_thickening h)

/-- The algebra map underlying the chosen universal first-order thickening. -/
noncomputable def universalFirstOrderThickeningMap
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    (h : Algebra.FormallyUnramified R S) :
    (universalFirstOrderThickening h).Ring →ₐ[R] S :=
  IsScalarTower.toAlgHom R (universalFirstOrderThickening h).Ring S

/-- The conormal module, represented by Mathlib's canonical `I/I²` module. -/
abbrev conormalModule
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    (h : Algebra.FormallyUnramified R S) : Type u :=
  (universalFirstOrderThickening h).Cotangent

/-- Any two universal first-order thickenings are uniquely isomorphic over `S`. -/
theorem universal_first_order_thickening_unique
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    (P Q : Algebra.Extension.{u} R S)
    (hP : IsUniversalFirstOrderThickening P)
    (hQ : IsUniversalFirstOrderThickening Q) :
    ∃! e : P.Ring ≃ₐ[R] Q.Ring,
      (IsScalarTower.toAlgHom R Q.Ring S).comp e.toAlgHom =
        IsScalarTower.toAlgHom R P.Ring S := by
  sorry

/-! ## Quotients -/

/-- The canonical extension `R/I² → R/I`. -/
noncomputable def quotientFirstOrderThickening
    {R : Type u} [CommRing R] (I : Ideal R) :
    Algebra.Extension.{u} R (R ⧸ I) := by
  let hI : I ^ 2 ≤ I := Ideal.pow_le_self two_ne_zero
  let f : (R ⧸ I ^ 2) →ₐ[R] (R ⧸ I) := Ideal.Quotient.factorₐ R hI
  exact Algebra.Extension.ofSurjective f (Ideal.Quotient.factor_surjective hI)

/-- The quotient `R/I² → R/I` is the universal first-order thickening. -/
theorem universal_first_order_thickening_quotient
    {R : Type u} [CommRing R] (I : Ideal R) :
    IsUniversalFirstOrderThickening (quotientFirstOrderThickening I) := by
  sorry

/-- The quotient description of the conormal module is `I/I²`. -/
abbrev quotientConormalModule
    {R : Type u} [CommRing R] (I : Ideal R) : Type u := I.Cotangent

theorem conormalModule_quotient
    {R : Type u} [CommRing R] (I : Ideal R)
    (h : Algebra.FormallyUnramified R (R ⧸ I)) :
    Nonempty
      (conormalModule h ≃ₗ[R ⧸ I] quotientConormalModule I) := by
  sorry

/-! ## Localization -/

/-- Localization of the target preserves the universal first-order property.

`P.localization M` has underlying ring
`(M.comap (algebraMap P.Ring S))⁻¹P.Ring`, which is the source's `S'⁻¹B'`.
-/
theorem universal_first_order_thickening_localize_target
    {A B B' : Type u} [CommRing A] [CommRing B] [CommRing B']
    [Algebra A B] [Algebra B B'] [Algebra A B']
    [IsScalarTower A B B']
    (P : Algebra.Extension.{u} A B)
    (hP : IsUniversalFirstOrderThickening P)
    (M : Submonoid B) [IsLocalization M B'] :
    IsUniversalFirstOrderThickening (P.localization (S' := B') M) ∧
      Nonempty
        (B' ⊗[B] P.Cotangent ≃ₗ[B'] (P.localization (S' := B') M).Cotangent) := by
  sorry

/-- Localization of the base preserves the universal first-order property.

The explicit localization algebra hypotheses allow either the standard
`Localization` types or any equivalent chosen models of those localizations.
-/
theorem universal_first_order_thickening_localize_base
    {A B Aₘ Bₘ : Type u} [CommRing A] [CommRing B] [CommRing Aₘ] [CommRing Bₘ]
    [Algebra A B] [Algebra A Aₘ] [Algebra B Bₘ] [Algebra A Bₘ]
    [Algebra Aₘ Bₘ] [IsScalarTower A Aₘ Bₘ] [IsScalarTower A B Bₘ]
    (M : Submonoid A) [IsLocalization M Aₘ]
    [IsLocalization (M.map (algebraMap A B)) Bₘ]
    (P : Algebra.Extension.{u} A B)
    (hP : IsUniversalFirstOrderThickening P) :
    ∃ Q : Algebra.Extension.{u} Aₘ Bₘ,
      IsUniversalFirstOrderThickening Q ∧
        Nonempty (Bₘ ⊗[B] P.Cotangent ≃ₗ[Bₘ] Q.Cotangent) := by
  sorry

/-! ## Differentials -/

/-- The universal thickening remains formally unramified over the base. -/
theorem universal_first_order_thickening_formallyUnramified
    {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    (P : Algebra.Extension.{u} A B)
    (hP : IsUniversalFirstOrderThickening P) :
    Algebra.FormallyUnramified A P.Ring := by
  sorry

/-- Differential comparison for a universal first-order thickening.

The displayed equivalence is the source's canonical map
`Ω[A/R] ⊗[A] B → Ω[P.Ring/R] ⊗[P.Ring] B`, with the target written as
Mathlib's `P.CotangentSpace`.
-/
theorem differentials_universal_first_order_thickening
    {R A B : Type u} [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] [Algebra A B] [IsScalarTower R A B]
    (hAB : Algebra.FormallyUnramified A B)
    (P : Algebra.Extension.{u} A B)
    (hP : IsUniversalFirstOrderThickening P) :
    Algebra.FormallyUnramified A P.Ring ∧
      Nonempty
        (B ⊗[A] KaehlerDifferential R A ≃ₗ[B] P.CotangentSpace) := by
  sorry

end

end Formalization.Books.Algebra.Unit149
