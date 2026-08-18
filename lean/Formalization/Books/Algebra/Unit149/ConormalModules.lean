import Mathlib.RingTheory.Extension.Cotangent.Basic
import Mathlib.RingTheory.Extension.ExtendScalars
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Ideal.Quotient.PowTransition
import Mathlib.RingTheory.Localization.Basic
import Mathlib.RingTheory.Unramified.Basic

/-!
# Commutative Algebra, Chapter 149: Conormal modules and universal thickenings

The source constructs a universal square-zero extension for a formally
unramified algebra.  Mathlib's `Algebra.Extension` is the canonical interface
for a surjection of algebras, and its `Cotangent` is the canonical
presentation-independent `I/I²` module.  The declarations below add the
universal property and record the quotient, localization, and differential
statements from the source section.  The universal-property predicate itself
is stated independently of the hypothesis used by the existence lemma, which
lets the quotient construction be recorded directly before relating it to a
chosen universal thickening.
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

/-- The square-zero kernel of a universal first-order thickening. -/
abbrev universalFirstOrderThickeningKernel
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    (h : Algebra.FormallyUnramified R S) :
    Ideal (universalFirstOrderThickening h).Ring :=
  (universalFirstOrderThickening h).ker

theorem universalFirstOrderThickening_kernel_square_zero
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    (h : Algebra.FormallyUnramified R S) :
    universalFirstOrderThickeningKernel h ^ 2 = ⊥ :=
  (universalFirstOrderThickening_isUniversal h).1

/-- The algebra map underlying the chosen universal first-order thickening. -/
noncomputable def universalFirstOrderThickeningMap
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    (h : Algebra.FormallyUnramified R S) :
    (universalFirstOrderThickening h).Ring →ₐ[R] S :=
  IsScalarTower.toAlgHom R (universalFirstOrderThickening h).Ring S

theorem universalFirstOrderThickeningMap_surjective
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    (h : Algebra.FormallyUnramified R S) :
    Function.Surjective (universalFirstOrderThickeningMap h) :=
  (universalFirstOrderThickening h).algebraMap_surjective

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

/-- The quotient map underlying `quotientFirstOrderThickening`. -/
noncomputable def quotientFirstOrderThickeningMap
    {R : Type u} [CommRing R] (I : Ideal R) :
    (quotientFirstOrderThickening I).Ring →ₐ[R] R ⧸ I :=
  IsScalarTower.toAlgHom R (quotientFirstOrderThickening I).Ring (R ⧸ I)

theorem quotientFirstOrderThickeningMap_surjective
    {R : Type u} [CommRing R] (I : Ideal R) :
    Function.Surjective (quotientFirstOrderThickeningMap I) :=
  (quotientFirstOrderThickening I).algebraMap_surjective

/-- The quotient `R/I² → R/I` is the universal first-order thickening. -/
theorem universal_first_order_thickening_quotient
    {R : Type u} [CommRing R] (I : Ideal R) :
    IsUniversalFirstOrderThickening (quotientFirstOrderThickening I) := by
  sorry

/-- The quotient description of the conormal module is `I/I²`. -/
abbrev quotientConormalModule
    {R : Type u} [CommRing R] (I : Ideal R) : Type u := I.Cotangent

theorem quotient_first_order_thickening_conormal
    {R : Type u} [CommRing R] (I : Ideal R) :
    Nonempty
      ((quotientFirstOrderThickening I).Cotangent ≃ₗ[R ⧸ I]
        quotientConormalModule I) := by
  sorry

theorem conormalModule_quotient
    {R : Type u} [CommRing R] (I : Ideal R)
    (h : Algebra.FormallyUnramified R (R ⧸ I)) :
    Nonempty
      (conormalModule h ≃ₗ[R ⧸ I] quotientConormalModule I) := by
  sorry

/-! ## Localization -/

/-- The multiplicative subset in an extension ring lying over a target subset. -/
def localizationPreimage
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    (P : Algebra.Extension.{u} R S) (M : Submonoid S) : Submonoid P.Ring :=
  M.comap (algebraMap P.Ring S)

/- The source's base-localization statement uses the localization of the
   extension ring at the image of the base multiplicative set.  This is the
   canonical ring map from that localization to the localized target. -/
noncomputable def baseLocalizationMap
    {A B Bₘ : Type u} [CommRing A] [CommRing B] [CommRing Bₘ]
    [Algebra A B] [Algebra B Bₘ] [Algebra A Bₘ] [IsScalarTower A B Bₘ]
    (P : Algebra.Extension.{u} A B) (M : Submonoid A)
    [IsLocalization (M.map (algebraMap A B)) Bₘ] :
    Localization (M.map (algebraMap A P.Ring)) →+* Bₘ := by
  let h : ∀ y : M.map (algebraMap A P.Ring),
      IsUnit ((algebraMap B Bₘ)
        ((algebraMap P.Ring B) (y : P.Ring))) := by
    rintro ⟨_, ⟨a, ha, rfl⟩⟩
    change IsUnit ((algebraMap B Bₘ)
      ((algebraMap P.Ring B) ((algebraMap A P.Ring) a)))
    rw [← IsScalarTower.algebraMap_apply A P.Ring B]
    exact IsLocalization.map_units Bₘ
      ⟨algebraMap A B a, Submonoid.mem_map_of_mem (algebraMap A B) ha⟩
  exact IsLocalization.lift (M := M.map (algebraMap A P.Ring))
    (g := (algebraMap B Bₘ).comp (IsScalarTower.toAlgHom A P.Ring B).toRingHom) h

/-- Localization of the target preserves the universal first-order property.

`P.localization M` has underlying ring
`(M.comap (algebraMap P.Ring S))⁻¹P.Ring`, which is the source's `S'⁻¹B'`.
-/
theorem universal_first_order_thickening_localize_target
    {A B B' : Type u} [CommRing A] [CommRing B] [CommRing B']
    [Algebra A B] [Algebra B B'] [Algebra A B']
    [IsScalarTower A B B']
    (hAB : Algebra.FormallyUnramified A B)
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
    (hAB : Algebra.FormallyUnramified A B)
    (M : Submonoid A) [IsLocalization M Aₘ]
    [IsLocalization (M.map (algebraMap A B)) Bₘ]
    (P : Algebra.Extension.{u} A B)
    (hP : IsUniversalFirstOrderThickening P)
    [Algebra Aₘ (Localization (M.map (algebraMap A P.Ring)))] :
    ∃ Q : Algebra.Extension.{u} Aₘ Bₘ,
      IsUniversalFirstOrderThickening Q ∧
        Nonempty (Bₘ ⊗[B] P.Cotangent ≃ₗ[Bₘ] Q.Cotangent) ∧
        ∃ e : Q.Ring ≃ₐ[Aₘ] Localization (M.map (algebraMap A P.Ring)),
          ((IsScalarTower.toAlgHom Aₘ Q.Ring Bₘ : Q.Ring →ₐ[Aₘ] Bₘ).toRingHom) =
            (baseLocalizationMap (Bₘ := Bₘ) P M).comp
              e.toRingEquiv.toRingHom := by
  sorry

/-! ## Differentials -/

/-- The canonical differential map in the final lemma of the source section.

It is the base change to `B` of the Kähler differential map induced by
`A → P.Ring`, with codomain
`B ⊗[P.Ring] Ω[P.Ring⁄R]`.  This is deliberately not `P.CotangentSpace`,
which uses differentials relative to `A`.
-/
noncomputable def differentialComparisonMap
    {R A B : Type u} [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] [Algebra A B] [IsScalarTower R A B]
    (P : Algebra.Extension.{u} A B) :
    B ⊗[A] KaehlerDifferential R A →ₗ[B]
      B ⊗[P.Ring] KaehlerDifferential R P.Ring :=
  let q : KaehlerDifferential R P.Ring →ₗ[A]
      B ⊗[P.Ring] KaehlerDifferential R P.Ring :=
    by
      exact (TensorProduct.mk P.Ring B (KaehlerDifferential R P.Ring) 1).restrictScalars A
  LinearMap.liftBaseChange B (q ∘ₗ KaehlerDifferential.map R R A P.Ring)

/-- The canonical differential map is an isomorphism for the universal
first-order thickening. -/
theorem differentialComparisonMap_bijective
    {R A B : Type u} [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] [Algebra A B] [IsScalarTower R A B]
    (hAB : Algebra.FormallyUnramified A B)
    (P : Algebra.Extension.{u} A B)
    (hP : IsUniversalFirstOrderThickening P) :
    Function.Bijective (differentialComparisonMap (R := R) (A := A) (B := B) P) := by
  sorry

/--
The canonical linear equivalence induced by the differential comparison map.

This packages the source's assertion that the comparison map is an isomorphism
in a reusable form, while `differentialComparisonMap` remains available when
the actual canonical map is needed.
-/
noncomputable def differentialComparisonEquiv
    {R A B : Type u} [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] [Algebra A B] [IsScalarTower R A B]
    (hAB : Algebra.FormallyUnramified A B)
    (P : Algebra.Extension.{u} A B)
    (hP : IsUniversalFirstOrderThickening P) :
    B ⊗[A] KaehlerDifferential R A ≃ₗ[B]
      B ⊗[P.Ring] KaehlerDifferential R P.Ring :=
  LinearEquiv.ofBijective (differentialComparisonMap (R := R) (A := A) (B := B) P)
    (differentialComparisonMap_bijective (R := R) (A := A) (B := B) hAB P hP)

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
the explicit base-changed differential module.
-/
theorem differentials_universal_first_order_thickening
    {R A B : Type u} [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] [Algebra A B] [IsScalarTower R A B]
    (hAB : Algebra.FormallyUnramified A B)
    (P : Algebra.Extension.{u} A B)
    (hP : IsUniversalFirstOrderThickening P) :
    Algebra.FormallyUnramified A P.Ring ∧
      Nonempty
        (B ⊗[A] KaehlerDifferential R A ≃ₗ[B]
          B ⊗[P.Ring] KaehlerDifferential R P.Ring) := by
  exact ⟨universal_first_order_thickening_formallyUnramified P hP,
    ⟨differentialComparisonEquiv hAB P hP⟩⟩

end

end Formalization.Books.Algebra.Unit149
