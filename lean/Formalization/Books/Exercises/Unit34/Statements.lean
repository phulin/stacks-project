import Formalization.Books.Exercises.Unit34.Core
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.AlgebraicGeometry.FunctionField
import Mathlib.FieldTheory.IsAlgClosed.Basic

/-!
# Exercises, Chapter 34: Morphisms

The declarations below follow the source order.  The concrete constructions
are in `Core.lean`; proposition-valued exercise proofs are deferred.
-/

namespace Formalization.Books.Exercises.Unit34

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry
open Opposite TopologicalSpace

universe u

noncomputable section

/-! ## Exercise `exercise-no-section` -/

/-- The displayed morphism has no section over all of `Spec(ℂ[t])`. -/
theorem noSection_has_no_section :
    ¬ HasSection noSectionMorphism := by
  rintro ⟨σ, hσ⟩
  obtain ⟨φ, rfl⟩ := Scheme.Spec.map_surjective σ
  have hφ : CommRingCat.ofHom noSectionBaseToSource ≫ φ.unop = 𝟙 _ := by
    apply AlgebraicGeometry.Spec.map_injective
    simpa [noSectionMorphism, affineSchemeMap, ← AlgebraicGeometry.Spec.map_comp] using hσ
  have hu : IsUnit (φ.unop.hom (algebraMap noSectionPolynomialRing
      noSectionLocalizationRing noSectionInvertingElement)) := by
    exact IsUnit.map φ.unop.hom
      (IsLocalization.Away.algebraMap_isUnit noSectionInvertingElement)
  have hu' : IsUnit
      (φ.unop.hom (algebraMap noSectionPolynomialRing noSectionLocalizationRing noSectionX) *
        φ.unop.hom (algebraMap noSectionPolynomialRing noSectionLocalizationRing noSectionT)) := by
    simpa [noSectionInvertingElement, map_mul] using hu
  let t : noSectionBaseRing := MvPolynomial.X 0
  have htmap : φ.unop.hom (noSectionBaseToSource t) = t := by
    have h := congrArg (fun g : noSectionBaseRing →+* noSectionBaseRing => g t)
      (congrArg CommRingCat.Hom.hom hφ)
    simpa using h
  have ht' : IsUnit (φ.unop.hom (algebraMap noSectionPolynomialRing
      noSectionLocalizationRing noSectionT)) :=
    (IsUnit.mul_iff.mp hu').2
  have hunit_t : IsUnit t := by
    rw [← htmap]
    simpa [t, noSectionBaseToSource, noSectionBaseRing, noSectionPolynomialRing,
      polynomialBaseMap, noSectionT, RingHom.comp_apply] using ht'
  let e := MvPolynomial.eval₂Hom
    (Polynomial.C : ℂ →+* Polynomial ℂ) (fun _ : Fin 1 ↦ Polynomial.X)
  have hunit_poly : IsUnit (Polynomial.X : Polynomial ℂ) := by
    have h := IsUnit.map e hunit_t
    simpa [e, t] using h
  exact (Polynomial.not_isUnit_X (R := ℂ)) hunit_poly

/-- The same morphism acquires a section after restricting to a nonempty open
of the base. -/
theorem noSection_has_nonempty_open_section :
    HasOpenSection noSectionMorphism := by
  let t : (CommRingCat.of noSectionBaseRing : Type) := MvPolynomial.X 0
  let g : noSectionPolynomialRing →+* Localization.Away t :=
    MvPolynomial.eval₂Hom
      (algebraMap ℂ (Localization.Away t))
      (fun i : Fin 2 => if i = 0 then algebraMap noSectionBaseRing
        (Localization.Away t) t else 1)
  have hg : IsUnit (g noSectionInvertingElement) := by
    have ht : IsUnit (algebraMap noSectionBaseRing (Localization.Away t) t) :=
      IsLocalization.Away.algebraMap_isUnit t
    simpa [g, noSectionInvertingElement, noSectionX, noSectionT, t] using ht
  let ψ : noSectionLocalizationRing →+* Localization.Away t :=
    IsLocalization.Away.lift noSectionInvertingElement hg
  have hcomp : CommRingCat.ofHom noSectionBaseToSource ≫
      CommRingCat.ofHom ψ =
      CommRingCat.ofHom (algebraMap noSectionBaseRing (Localization.Away t)) := by
    rw [← CommRingCat.ofHom_comp]
    ext i
    · simp [noSectionBaseToSource, ψ, g, polynomialBaseMap, t,
        IsScalarTower.algebraMap_apply ℂ noSectionBaseRing (Localization.Away t)]
    · fin_cases i
      simp [noSectionBaseToSource, ψ, g, polynomialBaseMap, t]
  let e := basicOpenIsoSpecAway t
  have hsource :
      AlgebraicGeometry.Spec.map (CommRingCat.ofHom ψ) ≫ noSectionMorphism =
        AlgebraicGeometry.Spec.map
          (CommRingCat.ofHom (algebraMap noSectionBaseRing (Localization.Away t))) := by
    rw [noSectionMorphism, affineSchemeMap, ← AlgebraicGeometry.Spec.map_comp,
      ← CommRingCat.ofHom_comp]
    exact congrArg AlgebraicGeometry.Spec.map hcomp
  refine ⟨PrimeSpectrum.basicOpen t, ?_, e.hom ≫
      AlgebraicGeometry.Spec.map (CommRingCat.ofHom ψ), ?_⟩
  · change (PrimeSpectrum.basicOpen t : Set (PrimeSpectrum noSectionBaseRing)).Nonempty
    refine ⟨⟨⊥, inferInstance⟩, ?_⟩
    change t ∉ (⊥ : Ideal noSectionBaseRing)
    simp [t]
  · have hι : openSubschemeInclusion noSectionBase
        (PrimeSpectrum.basicOpen t) =
        Scheme.Opens.ι (X := noSectionBase) (PrimeSpectrum.basicOpen t) := by
      rfl
    rw [hι]
    calc
      (e.hom ≫ AlgebraicGeometry.Spec.map (CommRingCat.ofHom ψ)) ≫ noSectionMorphism =
          e.hom ≫ (AlgebraicGeometry.Spec.map (CommRingCat.ofHom ψ) ≫ noSectionMorphism) := by
            simp only [Category.assoc]
      _ = e.hom ≫ AlgebraicGeometry.Spec.map
          (CommRingCat.ofHom (algebraMap noSectionBaseRing (Localization.Away t))) := by
            rw [hsource]
      _ = Scheme.Opens.ι (X := noSectionBase)
          (PrimeSpectrum.basicOpen t) := by
        simpa using (basicOpenIsoSpecAway_hom_SpecMap t)

/-! ## Exercise `exercise-no-rational-section` -/

/-- The morphism cut out by `x² + t` has no section over any nonempty open of
the base. -/
theorem noRationalSection_has_no_open_section :
    ¬ HasOpenSection noRationalSectionMorphism := by
  intro h
  obtain ⟨U, hU, σ, hσ⟩ := h
  let x := genericPoint noRationalSectionBase
  have hxU : x ∈ U := by
    exact ((genericPoint_spec noRationalSectionBase).mem_open_set_iff U.isOpen).mpr
      (by simpa using hU)
  let hUN : Nonempty U := ⟨⟨x, hxU⟩⟩
  let htop : Nonempty (⊤ : Opens noRationalSectionBase) := ⟨⟨x, trivial⟩⟩
  let τ : Γ(openSubscheme noRationalSectionBase U, ⊤) ⟶
      Γ(noRationalSectionBase, U) :=
    (Scheme.restrictFunctorΓ (X := noRationalSectionBase)).hom.app (op U)
  let q : noRationalSectionRing →+* noRationalSectionBase.functionField :=
    ((Scheme.ΓSpecIso (CommRingCat.of noRationalSectionRing)).inv ≫
      σ.appTop ≫ τ ≫
      @Scheme.germToFunctionField noRationalSectionBase inferInstance U hUN).hom
  let f : noRationalSectionPolynomialRing →+* noRationalSectionBase.functionField :=
    q.comp (quotientMap noRationalSectionIdeal)
  have hrel : f noRationalSectionRelation = 0 := by
    change q (quotientMap noRationalSectionIdeal noRationalSectionRelation) = 0
    have hzero : quotientMap noRationalSectionIdeal noRationalSectionRelation = 0 := by
      exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self _)
    calc
      q (quotientMap noRationalSectionIdeal noRationalSectionRelation) = q 0 := by rw [hzero]
      _ = 0 := q.map_zero
  have hcomp : noRationalSectionMorphism.appTop ≫ σ.appTop =
      (openSubschemeInclusion noRationalSectionBase U).appTop := by
    simpa only [Scheme.Hom.comp_appTop] using
      congrArg (fun f : openSubscheme noRationalSectionBase U ⟶
        noRationalSectionBase => f.appTop) hσ
  let b : noRationalSectionBaseRing →+* noRationalSectionBase.functionField :=
    ((Scheme.ΓSpecIso (CommRingCat.of noRationalSectionBaseRing)).inv ≫
      @Scheme.germToFunctionField noRationalSectionBase inferInstance
        (⊤ : Opens noRationalSectionBase) htop).hom
  let alg : Algebra (CommRingCat.of noRationalSectionBaseRing)
      noRationalSectionBase.functionField := RingHom.toAlgebra b
  let fr : IsFractionRing (CommRingCat.of noRationalSectionBaseRing)
      noRationalSectionBase.functionField :=
    AlgebraicGeometry.functionField_isFractionRing_of_affine
      (CommRingCat.of noRationalSectionBaseRing)
  have hbase : q.comp noRationalSectionBaseToSource = b := by
    change (CommRingCat.ofHom noRationalSectionBaseToSource ≫
        (Scheme.ΓSpecIso (CommRingCat.of noRationalSectionRing)).inv ≫
        σ.appTop ≫ τ ≫
        @Scheme.germToFunctionField noRationalSectionBase inferInstance U hUN).hom =
      ((Scheme.ΓSpecIso (CommRingCat.of noRationalSectionBaseRing)).inv ≫
        @Scheme.germToFunctionField noRationalSectionBase inferInstance
          (⊤ : Opens noRationalSectionBase) htop).hom
    have hcat0 : CommRingCat.ofHom noRationalSectionBaseToSource ≫
          (Scheme.ΓSpecIso (CommRingCat.of noRationalSectionRing)).inv =
        (Scheme.ΓSpecIso (CommRingCat.of noRationalSectionBaseRing)).inv ≫
          noRationalSectionMorphism.appTop :=
      Scheme.ΓSpecIso_inv_naturality
        (f := CommRingCat.ofHom noRationalSectionBaseToSource)
    have hcat : CommRingCat.ofHom noRationalSectionBaseToSource ≫
          (Scheme.ΓSpecIso (CommRingCat.of noRationalSectionRing)).inv ≫
          σ.appTop ≫ τ ≫
          @Scheme.germToFunctionField noRationalSectionBase inferInstance U hUN =
        (Scheme.ΓSpecIso (CommRingCat.of noRationalSectionBaseRing)).inv ≫
          @Scheme.germToFunctionField noRationalSectionBase inferInstance
            (⊤ : Opens noRationalSectionBase) htop := by
      simp only [← Category.assoc]
      rw [hcat0]
      have hpost :
          ((noRationalSectionMorphism.appTop ≫ σ.appTop) ≫ τ) ≫
              @Scheme.germToFunctionField noRationalSectionBase inferInstance U hUN =
            ((openSubschemeInclusion noRationalSectionBase U).appTop ≫ τ) ≫
              @Scheme.germToFunctionField noRationalSectionBase inferInstance U hUN := by
        exact congrArg (fun k => (k ≫ τ) ≫
          @Scheme.germToFunctionField noRationalSectionBase inferInstance U hUN) hcomp
      calc
        (((Scheme.ΓSpecIso (CommRingCat.of noRationalSectionBaseRing)).inv ≫
            noRationalSectionMorphism.appTop) ≫ σ.appTop ≫ τ) ≫
              @Scheme.germToFunctionField noRationalSectionBase inferInstance U hUN =
            (Scheme.ΓSpecIso (CommRingCat.of noRationalSectionBaseRing)).inv ≫
              (((noRationalSectionMorphism.appTop ≫ σ.appTop) ≫ τ) ≫
                @Scheme.germToFunctionField noRationalSectionBase inferInstance U hUN) := by
                  simp only [Category.assoc]
        _ = (Scheme.ΓSpecIso (CommRingCat.of noRationalSectionBaseRing)).inv ≫
              (((openSubschemeInclusion noRationalSectionBase U).appTop ≫ τ) ≫
                @Scheme.germToFunctionField noRationalSectionBase inferInstance U hUN) := by
                  rw [hpost]
        _ = (Scheme.ΓSpecIso (CommRingCat.of noRationalSectionBaseRing)).inv ≫
              @Scheme.germToFunctionField noRationalSectionBase inferInstance
                (⊤ : Opens noRationalSectionBase) htop := by
                  simp [τ]
                  erw [← Functor.map_comp]
                  simp only [Functor.map_comp, Category.assoc, TopCat.Presheaf.germ_res']
    simpa only using congrArg CommRingCat.Hom.hom hcat
  have hmap : f.comp (polynomialBaseMap (K := ℂ) (n := 2) 1) = b := by
    simpa [f, noRationalSectionBaseToSource, RingHom.comp_assoc] using hbase
  let e0 : MvPolynomial (Fin 0) ℂ ≃ₐ[ℂ] ℂ :=
    MvPolynomial.isEmptyAlgEquiv ℂ (Fin 0)
  let e : noRationalSectionBaseRing ≃ₐ[ℂ] Polynomial ℂ :=
    (MvPolynomial.finSuccEquiv ℂ 0).trans (Polynomial.mapAlgEquiv e0)
  let eg : noRationalSectionBaseRing →+* FractionRing (Polynomial ℂ) :=
    (algebraMap (Polynomial ℂ) (FractionRing (Polynomial ℂ))).comp e.toRingHom
  have heg : Function.Injective eg := by
    exact (IsFractionRing.injective (Polynomial ℂ) (FractionRing (Polynomial ℂ))).comp
      e.injective
  let ℓ : noRationalSectionBase.functionField →+* FractionRing (Polynomial ℂ) :=
    @IsFractionRing.lift (CommRingCat.of noRationalSectionBaseRing) inferInstance
      noRationalSectionBase.functionField inferInstance
      (FractionRing (Polynomial ℂ)) inferInstance alg fr eg heg
  have hX0 := congrArg (fun g : noRationalSectionBaseRing →+*
      noRationalSectionBase.functionField => g (MvPolynomial.X 0)) hmap
  have hX1 : f (MvPolynomial.X 1) = b (MvPolynomial.X 0) := by
    simpa [polynomialBaseMap] using hX0
  have hℓX1 : ℓ (f (MvPolynomial.X 1)) =
      algebraMap (Polynomial ℂ) (FractionRing (Polynomial ℂ)) Polynomial.X := by
    rw [hX1]
    change ℓ (algebraMap (CommRingCat.of noRationalSectionBaseRing)
      noRationalSectionBase.functionField (MvPolynomial.X 0)) = _
    have h := IsFractionRing.lift_algebraMap
      (A := CommRingCat.of noRationalSectionBaseRing)
      (K := noRationalSectionBase.functionField)
      (L := FractionRing (Polynomial ℂ)) (g := eg) heg (MvPolynomial.X 0)
    simp [ℓ, eg, e, e0, MvPolynomial.finSuccEquiv_X_zero] at h ⊢
  have heq : (ℓ (f (MvPolynomial.X 0))) ^ 2 +
      algebraMap (Polynomial ℂ) (FractionRing (Polynomial ℂ)) Polynomial.X = 0 := by
    have h := congrArg ℓ hrel
    simpa [noRationalSectionRelation, map_add, map_pow, hℓX1] using h
  obtain ⟨p, q', hq', hpq⟩ :=
    IsFractionRing.div_surjective (Polynomial ℂ) (ℓ (f (MvPolynomial.X 0)))
  have hq0 : q' ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp hq'
  have hqK : algebraMap (Polynomial ℂ) (FractionRing (Polynomial ℂ)) q' ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hq'
  rw [← hpq] at heq
  field_simp [hqK] at heq
  have hpoly : p ^ 2 + Polynomial.X * q' ^ 2 = 0 := by
    apply (IsFractionRing.injective (Polynomial ℂ) (FractionRing (Polynomial ℂ)))
    simpa [map_add, map_mul, map_pow, mul_comm, mul_left_comm, mul_assoc] using heq
  have hp0 : p ≠ 0 := by
    intro hp
    have hqterm : Polynomial.X * q' ^ 2 = 0 := by
      simpa [hp] using hpoly
    rcases mul_eq_zero.mp hqterm with hX | hqpow
    · exact Polynomial.X_ne_zero hX
    · have hqmul : q' * q' = 0 := by simpa [pow_two] using hqpow
      rcases mul_eq_zero.mp hqmul with hq | hq
      · exact hq0 hq
      · exact hq0 hq
  have hEq : p ^ 2 = -(Polynomial.X * q' ^ 2) := by
    calc
      p ^ 2 = (p ^ 2 + Polynomial.X * q' ^ 2) - Polynomial.X * q' ^ 2 := by ring
      _ = -(Polynomial.X * q' ^ 2) := by rw [hpoly]; ring
  have hdeg := congrArg Polynomial.natDegree hEq
  rw [Polynomial.natDegree_pow, Polynomial.natDegree_neg,
    Polynomial.natDegree_mul Polynomial.X_ne_zero (pow_ne_zero 2 hq0),
    Polynomial.natDegree_pow, Polynomial.natDegree_X] at hdeg
  omega

/-! ## Exercise `exercise-has-rational-section` -/

/-- The conic with nonzero polynomial coefficients has a rational section. -/
/-
Interface audit: the statement is sound.  The three nonzero hypotheses are
exactly what makes the diagonal ternary quadratic nondegenerate over
`Frac(ℂ[t])`; no extra coprimality hypothesis is needed.

Proof roadmap for the normal `prove` stage.

1. Add the focused imports `Mathlib.RingTheory.Nullstellensatz`,
   `Mathlib.RingTheory.Ideal.KrullsHeightTheorem`,
   `Mathlib.RingTheory.KrullDimension.Polynomial`, and
   `Mathlib.RingTheory.MvPolynomial.Ideal`.  Prove a private helper
   `tsen_conic_homogeneous_solution` returning `X Y Z : Polynomial ℂ`, not
   all zero, with
   `(e A) * Z ^ 2 + (e B) * X ^ 2 + (e C) * Y ^ 2 = 0`, where the explicit
   equivalence is
   `e0 : MvPolynomial (Fin 0) ℂ ≃ₐ[ℂ] ℂ :=
      MvPolynomial.isEmptyAlgEquiv ℂ (Fin 0)` and
   `e := (MvPolynomial.finSuccEquiv ℂ 0).trans
      (Polynomial.mapAlgEquiv e0)`.

   Put `D := max (e A).natDegree
     (max (e B).natDegree (e C).natDegree)` and take `d := D`.  Three
   polynomials of degree at most `d` have `N := 3 * (d + 1)` coefficient
   variables.  For each `j : Fin (2 * d + D + 1)`, define the coefficient of
   the displayed quadratic as an element of `MvPolynomial (Fin N) ℂ` using
   `Polynomial.coeff_mul` and finite sums.  These are homogeneous quadrics,
   and `2 * d + D + 1 < N` is `omega`.

   Let `I` be the span of this finite family.  If
   `MvPolynomial.zeroLocus ℂ I = {0}`, then
   `MvPolynomial.vanishingIdeal_zeroLocus_eq_radical I` from
   `Mathlib/RingTheory/Nullstellensatz.lean` identifies `I.radical` with
   `MvPolynomial.idealOfVars (Fin N) ℂ`.  Use
   `Ideal.radical_minimalPrimes` and
   `Ideal.minimalPrimes_eq_subsingleton_self` from
   `Mathlib/RingTheory/Ideal/MinimalPrime/Basic.lean` to put that coordinate
   ideal in `I.minimalPrimes`, then apply
   `Ideal.height_le_card_of_mem_minimalPrimes_span_finset`.  Establish once
   as a small helper that the coordinate ideal has height `N`: its upper
   bound is `MvPolynomial.ringKrullDim_of_isNoetherianRing`, and the lower
   bound is the explicit chain of ideals generated by the first `j`
   variables, fed to `Order.index_le_height` from
   `Mathlib/Order/KrullDimension.lean`.  This contradicts the preceding
   strict inequality and supplies a nonzero common zero.  Split its `Fin N`
   coordinates into three blocks and use `Polynomial.ofFinsupp` from
   `Mathlib/Algebra/Polynomial/Coeff.lean` to obtain `X`, `Y`, and `Z`.
2. Strengthen the helper to return `Z ≠ 0` without introducing fraction
   fields.  If the first solution has `Z = 0`, then `X ≠ 0` (otherwise the
   relation and `C ≠ 0` force all three coordinates to vanish).  Replace it
   by
   `Z' := -2 * (e B) * X`,
   `X' := ((e A) - (e B)) * X`, and
   `Y' := ((e A) + (e B)) * Y`.
   Expanding and using `(e B) * X^2 + (e C) * Y^2 = 0` proves the new
   quadratic relation, while the domain instance and `hB`, `X ≠ 0` give
   `Z' ≠ 0`.  Transport the triple back through `e.symm`; this yields the
   final private interface
   `tsen_conic_polynomial_solution (A B C) (hA) (hB) (hC) :
      ∃ X Y Z : noSectionBaseRing, Z ≠ 0 ∧
        A * Z^2 + B * X^2 + C * Y^2 = 0`.
3. For such `X,Y,Z`, put `L := Localization.Away Z`.  The image `z` of `Z`
   is a unit by `IsLocalization.Away.algebraMap_isUnit`.  Define
   `g : complexPolynomialRing 3 →+* L` with `MvPolynomial.eval₂Hom`, sending
   variables `0,1,2` to `algebraMap _ L X * z⁻¹`,
   `algebraMap _ L Y * z⁻¹`, and the image of `MvPolynomial.X 0`.
   Multiplying the desired equality by `z^2` and using the helper relation
   proves `g (rationalSectionPolynomialRing A B C) = 0`.  Factor through
   `rationalSectionRing A B C` with `Ideal.Quotient.lift`; use
   `Ideal.Quotient.lift_mk` for both the relation and the base-map
   compatibility.
4. Apply `AlgebraicGeometry.Spec.map` to the quotient lift and precompose
   with `(basicOpenIsoSpecAway Z).hom`.  Assemble `HasOpenSection` using
   `PrimeSpectrum.basicOpen Z`; the point `⟨⊥, inferInstance⟩` witnesses its
   nonemptiness because `Z ≠ 0`.  The section equation is the calculation in
   `noSection_has_nonempty_open_section` above, with
   `basicOpenIsoSpecAway_hom_SpecMap` from
   `Mathlib/AlgebraicGeometry/Restrict.lean` and `Spec.map_comp`.
-/
theorem rationalSection_has_open_section
    (A B C : noSectionBaseRing)
    (hA : A ≠ 0) (hB : B ≠ 0) (hC : C ≠ 0) :
    HasOpenSection (rationalSectionMorphism A B C) := by
  sorry

/-! ## Remark `remark-tsen` -/

/-- The preceding conic statement is the special case of Tsen's theorem
recorded by the source. -/
theorem tsen_conic_special_case :
    ∀ (A B C : noSectionBaseRing), A ≠ 0 → B ≠ 0 → C ≠ 0 →
      HasOpenSection (rationalSectionMorphism A B C) := by
  exact fun A B C hA hB hC => rationalSection_has_open_section A B C hA hB hC

private lemma polynomial_cubic_no_solution
    (d p r : Polynomial ℂ) (hd : d ≠ 0) :
    d ^ 3 + Polynomial.X * p ^ 3 + Polynomial.X ^ 2 * r ^ 3 ≠ 0 := by
  intro h
  have htwo1 : ∀ d p : Polynomial ℂ, d ≠ 0 → p ≠ 0 →
      d ^ 3 + Polynomial.X * p ^ 3 ≠ 0 := by
    intro d p hd hp h
    have heq : d ^ 3 = -(Polynomial.X * p ^ 3) := by
      linear_combination h
    have hdeg := congrArg Polynomial.natDegree heq
    rw [Polynomial.natDegree_pow, Polynomial.natDegree_neg,
      Polynomial.natDegree_mul Polynomial.X_ne_zero (pow_ne_zero 3 hp),
      Polynomial.natDegree_pow, Polynomial.natDegree_X] at hdeg
    omega
  have htwo2 : ∀ d r : Polynomial ℂ, d ≠ 0 → r ≠ 0 →
      d ^ 3 + Polynomial.X ^ 2 * r ^ 3 ≠ 0 := by
    intro d r hd hr h
    have heq : d ^ 3 = -(Polynomial.X ^ 2 * r ^ 3) := by
      linear_combination h
    have hdeg := congrArg Polynomial.natDegree heq
    rw [Polynomial.natDegree_pow, Polynomial.natDegree_neg,
      Polynomial.natDegree_mul (pow_ne_zero 2 Polynomial.X_ne_zero)
        (pow_ne_zero 3 hr), Polynomial.natDegree_pow, Polynomial.natDegree_pow,
      Polynomial.natDegree_X] at hdeg
    omega
  have hP : p ≠ 0 := by
    intro hpz
    by_cases hrz : r = 0
    · have hz : d ^ 3 = 0 := by simpa [hpz, hrz] using h
      exact (pow_ne_zero 3 hd) hz
    · exact htwo2 d r hd hrz (by simpa [hpz] using h)
  have hR : r ≠ 0 := by
    intro hrz
    by_cases hpz : p = 0
    · exact hP hpz
    · exact htwo1 d p hd hpz (by simpa [hrz] using h)
  have hp : p ≠ 0 := hP
  have hr : r ≠ 0 := hR
  let A : Polynomial ℂ := d ^ 3
  let P : Polynomial ℂ := Polynomial.X * p ^ 3
  let R : Polynomial ℂ := Polynomial.X ^ 2 * r ^ 3
  have hh : A + P + R = 0 := by simpa [A, P, R] using h
  have hAdeg : A.natDegree = 3 * d.natDegree := by
    dsimp [A]
    rw [Polynomial.natDegree_pow]
  have hPdeg : P.natDegree = 1 + 3 * p.natDegree := by
    dsimp [P]
    rw [Polynomial.natDegree_mul Polynomial.X_ne_zero (pow_ne_zero 3 hp),
      Polynomial.natDegree_pow, Polynomial.natDegree_X]
  have hRdeg : R.natDegree = 2 + 3 * r.natDegree := by
    dsimp [R]
    rw [Polynomial.natDegree_mul (pow_ne_zero 2 Polynomial.X_ne_zero)
      (pow_ne_zero 3 hr), Polynomial.natDegree_pow, Polynomial.natDegree_pow,
      Polynomial.natDegree_X]
  have hneq : A.natDegree ≠ P.natDegree ∧
      A.natDegree ≠ R.natDegree ∧ P.natDegree ≠ R.natDegree := by
    rw [hAdeg, hPdeg, hRdeg]
    omega
  have hcases :
      (A.natDegree > P.natDegree ∧ A.natDegree > R.natDegree) ∨
      (P.natDegree > A.natDegree ∧ P.natDegree > R.natDegree) ∨
      (R.natDegree > A.natDegree ∧ R.natDegree > P.natDegree) := by
    omega
  rcases hcases with hD | hP | hR
  · have hsum : (P + R).natDegree < A.natDegree := by
      have hle := Polynomial.natDegree_add_le P R
      omega
    have heq : A = -(P + R) := by linear_combination hh
    have hdeg := congrArg Polynomial.natDegree heq
    rw [hAdeg, Polynomial.natDegree_neg] at hdeg
    have hsum' := hsum
    omega
  · have hsum : (A + R).natDegree < P.natDegree := by
      have hle := Polynomial.natDegree_add_le A R
      omega
    have heq : P = -(A + R) := by linear_combination hh
    have hdeg := congrArg Polynomial.natDegree heq
    rw [hPdeg, Polynomial.natDegree_neg] at hdeg
    have hsum' := hsum
    omega
  · have hsum : (A + P).natDegree < R.natDegree := by
      have hle := Polynomial.natDegree_add_le A P
      omega
    have heq : R = -(A + P) := by linear_combination hh
    have hdeg := congrArg Polynomial.natDegree heq
    rw [hRdeg, Polynomial.natDegree_neg] at hdeg
    have hsum' := hsum
    omega

/-! ## Exercise `exercise-no-section-curve` -/

/-- The cubic curve example has no rational section. -/
theorem noSectionCurve_has_no_open_section :
    ¬ HasOpenSection noSectionCurveMorphism := by
  intro h
  obtain ⟨U, hU, σ, hσ⟩ := h
  let x := genericPoint noSectionBase
  have hxU : x ∈ U := by
    exact ((genericPoint_spec noSectionBase).mem_open_set_iff U.isOpen).mpr
      (by simpa using hU)
  let hUN : Nonempty U := ⟨⟨x, hxU⟩⟩
  let htop : Nonempty (⊤ : Opens noSectionBase) := ⟨⟨x, trivial⟩⟩
  let τ : Γ(openSubscheme noSectionBase U, ⊤) ⟶
      Γ(noSectionBase, U) :=
    (Scheme.restrictFunctorΓ (X := noSectionBase)).hom.app (op U)
  let q : noSectionCurveRing →+* noSectionBase.functionField :=
    ((Scheme.ΓSpecIso (CommRingCat.of noSectionCurveRing)).inv ≫
      σ.appTop ≫ τ ≫
      @Scheme.germToFunctionField noSectionBase inferInstance U hUN).hom
  let f : noSectionCurvePolynomialRing →+* noSectionBase.functionField :=
    q.comp (quotientMap noSectionCurveIdeal)
  have hrel : f noSectionCurveRelation = 0 := by
    change q (quotientMap noSectionCurveIdeal noSectionCurveRelation) = 0
    have hzero : quotientMap noSectionCurveIdeal noSectionCurveRelation = 0 := by
      exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self _)
    calc
      q (quotientMap noSectionCurveIdeal noSectionCurveRelation) = q 0 := by rw [hzero]
      _ = 0 := q.map_zero
  have hcomp : noSectionCurveMorphism.appTop ≫ σ.appTop =
      (openSubschemeInclusion noSectionBase U).appTop := by
    simpa only [Scheme.Hom.comp_appTop] using
      congrArg (fun f : openSubscheme noSectionBase U ⟶ noSectionBase => f.appTop) hσ
  let b : noSectionBaseRing →+* noSectionBase.functionField :=
    ((Scheme.ΓSpecIso (CommRingCat.of noSectionBaseRing)).inv ≫
      @Scheme.germToFunctionField noSectionBase inferInstance
        (⊤ : Opens noSectionBase) htop).hom
  let alg : Algebra (CommRingCat.of noSectionBaseRing)
      noSectionBase.functionField := RingHom.toAlgebra b
  let fr : IsFractionRing (CommRingCat.of noSectionBaseRing)
      noSectionBase.functionField :=
    AlgebraicGeometry.functionField_isFractionRing_of_affine
      (CommRingCat.of noSectionBaseRing)
  have hbase : q.comp noSectionCurveBaseToSource = b := by
    change (CommRingCat.ofHom noSectionCurveBaseToSource ≫
        (Scheme.ΓSpecIso (CommRingCat.of noSectionCurveRing)).inv ≫
        σ.appTop ≫ τ ≫
        @Scheme.germToFunctionField noSectionBase inferInstance U hUN).hom =
      ((Scheme.ΓSpecIso (CommRingCat.of noSectionBaseRing)).inv ≫
        @Scheme.germToFunctionField noSectionBase inferInstance
          (⊤ : Opens noSectionBase) htop).hom
    have hcat0 : CommRingCat.ofHom noSectionCurveBaseToSource ≫
          (Scheme.ΓSpecIso (CommRingCat.of noSectionCurveRing)).inv =
        (Scheme.ΓSpecIso (CommRingCat.of noSectionBaseRing)).inv ≫
          noSectionCurveMorphism.appTop :=
      Scheme.ΓSpecIso_inv_naturality
        (f := CommRingCat.ofHom noSectionCurveBaseToSource)
    have hcat : CommRingCat.ofHom noSectionCurveBaseToSource ≫
          (Scheme.ΓSpecIso (CommRingCat.of noSectionCurveRing)).inv ≫
          σ.appTop ≫ τ ≫
          @Scheme.germToFunctionField noSectionBase inferInstance U hUN =
        (Scheme.ΓSpecIso (CommRingCat.of noSectionBaseRing)).inv ≫
          @Scheme.germToFunctionField noSectionBase inferInstance
            (⊤ : Opens noSectionBase) htop := by
      simp only [← Category.assoc]
      rw [hcat0]
      have hpost :
          ((noSectionCurveMorphism.appTop ≫ σ.appTop) ≫ τ) ≫
              @Scheme.germToFunctionField noSectionBase inferInstance U hUN =
            ((openSubschemeInclusion noSectionBase U).appTop ≫ τ) ≫
              @Scheme.germToFunctionField noSectionBase inferInstance U hUN := by
        exact congrArg (fun k => (k ≫ τ) ≫
          @Scheme.germToFunctionField noSectionBase inferInstance U hUN) hcomp
      calc
        (((Scheme.ΓSpecIso (CommRingCat.of noSectionBaseRing)).inv ≫
            noSectionCurveMorphism.appTop) ≫ σ.appTop ≫ τ) ≫
              @Scheme.germToFunctionField noSectionBase inferInstance U hUN =
            (Scheme.ΓSpecIso (CommRingCat.of noSectionBaseRing)).inv ≫
              (((noSectionCurveMorphism.appTop ≫ σ.appTop) ≫ τ) ≫
                @Scheme.germToFunctionField noSectionBase inferInstance U hUN) := by
                  simp only [Category.assoc]
        _ = (Scheme.ΓSpecIso (CommRingCat.of noSectionBaseRing)).inv ≫
              (((openSubschemeInclusion noSectionBase U).appTop ≫ τ) ≫
                @Scheme.germToFunctionField noSectionBase inferInstance U hUN) := by
                  rw [hpost]
        _ = (Scheme.ΓSpecIso (CommRingCat.of noSectionBaseRing)).inv ≫
              @Scheme.germToFunctionField noSectionBase inferInstance
                (⊤ : Opens noSectionBase) htop := by
                  simp [τ]
                  erw [← Functor.map_comp]
                  simp only [Functor.map_comp, Category.assoc, TopCat.Presheaf.germ_res']
    simpa only using congrArg CommRingCat.Hom.hom hcat
  have hmap : f.comp (polynomialBaseMap (K := ℂ) (n := 3) 2) = b := by
    simpa [f, noSectionCurveBaseToSource, RingHom.comp_assoc] using hbase
  let e0 : MvPolynomial (Fin 0) ℂ ≃ₐ[ℂ] ℂ :=
    MvPolynomial.isEmptyAlgEquiv ℂ (Fin 0)
  let e : noSectionBaseRing ≃ₐ[ℂ] Polynomial ℂ :=
    (MvPolynomial.finSuccEquiv ℂ 0).trans (Polynomial.mapAlgEquiv e0)
  let eg : noSectionBaseRing →+* FractionRing (Polynomial ℂ) :=
    (algebraMap (Polynomial ℂ) (FractionRing (Polynomial ℂ))).comp e.toRingHom
  have heg : Function.Injective eg := by
    exact (IsFractionRing.injective (Polynomial ℂ) (FractionRing (Polynomial ℂ))).comp
      e.injective
  let ℓ : noSectionBase.functionField →+* FractionRing (Polynomial ℂ) :=
    @IsFractionRing.lift (CommRingCat.of noSectionBaseRing) inferInstance
      noSectionBase.functionField inferInstance
      (FractionRing (Polynomial ℂ)) inferInstance alg fr eg heg
  have hX2 := congrArg (fun g : noSectionBaseRing →+*
      noSectionBase.functionField => g (MvPolynomial.X 0)) hmap
  have hX2' : f (MvPolynomial.X 2) = b (MvPolynomial.X 0) := by
    simpa [polynomialBaseMap] using hX2
  have hℓX2 : ℓ (f (MvPolynomial.X 2)) =
      algebraMap (Polynomial ℂ) (FractionRing (Polynomial ℂ)) Polynomial.X := by
    rw [hX2']
    change ℓ (algebraMap (CommRingCat.of noSectionBaseRing)
      noSectionBase.functionField (MvPolynomial.X 0)) = _
    have h := IsFractionRing.lift_algebraMap
      (A := CommRingCat.of noSectionBaseRing)
      (K := noSectionBase.functionField)
      (L := FractionRing (Polynomial ℂ)) (g := eg) heg (MvPolynomial.X 0)
    simp [ℓ, eg, e, e0, MvPolynomial.finSuccEquiv_X_zero] at h ⊢
  have heq : 1 +
      algebraMap (Polynomial ℂ) (FractionRing (Polynomial ℂ)) Polynomial.X *
        (ℓ (f (MvPolynomial.X 0))) ^ 3 +
      (algebraMap (Polynomial ℂ) (FractionRing (Polynomial ℂ)) Polynomial.X) ^ 2 *
        (ℓ (f (MvPolynomial.X 1))) ^ 3 = 0 := by
    have h := congrArg ℓ hrel
    simpa [noSectionCurveRelation, map_add, map_mul, map_pow, hℓX2] using h
  obtain ⟨p, q', hq', hpq⟩ :=
    IsFractionRing.div_surjective (Polynomial ℂ) (ℓ (f (MvPolynomial.X 0)))
  obtain ⟨r, s, hs, hrs⟩ :=
    IsFractionRing.div_surjective (Polynomial ℂ) (ℓ (f (MvPolynomial.X 1)))
  have hq0 : q' ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp hq'
  have hs0 : s ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp hs
  have hqK : algebraMap (Polynomial ℂ) (FractionRing (Polynomial ℂ)) q' ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hq'
  have hsK : algebraMap (Polynomial ℂ) (FractionRing (Polynomial ℂ)) s ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hs
  rw [← hpq, ← hrs] at heq
  field_simp [hqK, hsK] at heq
  have hpoly : (q' * s) ^ 3 + Polynomial.X * (p * s) ^ 3 +
      Polynomial.X ^ 2 * (q' * r) ^ 3 = 0 := by
    apply (IsFractionRing.injective (Polynomial ℂ) (FractionRing (Polynomial ℂ)))
    rw [map_zero]
    calc
      _ = ((algebraMap (Polynomial ℂ) (FractionRing (Polynomial ℂ))) q' ^ 3 +
          algebraMap (Polynomial ℂ) (FractionRing (Polynomial ℂ)) Polynomial.X *
            (algebraMap (Polynomial ℂ) (FractionRing (Polynomial ℂ)) p) ^ 3) *
          (algebraMap (Polynomial ℂ) (FractionRing (Polynomial ℂ)) s) ^ 3 +
        (algebraMap (Polynomial ℂ) (FractionRing (Polynomial ℂ)) Polynomial.X) ^ 2 *
          (algebraMap (Polynomial ℂ) (FractionRing (Polynomial ℂ)) q') ^ 3 *
            (algebraMap (Polynomial ℂ) (FractionRing (Polynomial ℂ)) r) ^ 3 := by
              simp only [map_add, map_mul, map_pow]
              ring
      _ = _ := by simpa using heq
  exact polynomial_cubic_no_solution (q' * s) (p * s) (q' * r)
    (mul_ne_zero hq0 hs0) hpoly

/-! ## Exercise `exercise-no-section-surface` -/

/-- The eight-variable cubic surface example has no rational section. -/
/-
Interface audit: the statement is sound.  Under
`MvPolynomial.finSuccEquiv ℂ 1`, base variable `0` is the outer polynomial
variable and base variable `1` is the inner polynomial variable, exactly
matching `noSectionSurfaceBaseMap`'s variables `8` and `9`.

Proof roadmap for the normal `prove` stage.

1. Reuse the generic-point construction in
   `noSectionCurve_has_no_open_section` above verbatim with
   `noSectionSurfaceBase`.  From a hypothetical open section obtain
   `q : noSectionSurfaceRing →+* noSectionSurfaceBase.functionField`, then
   `f := q.comp (quotientMap noSectionSurfaceIdeal)`, and prove
   `f noSectionSurfaceRelation = 0`.  The comparison of the base maps uses
   `Scheme.ΓSpecIso_inv_naturality`, `Scheme.restrictFunctorΓ`,
   `TopCat.Presheaf.germ_res'`, and
   `functionField_isFractionRing_of_affine`, all already used by the curve
   proof in this file.
2. Instantiate the base-ring equivalence at universe `0` explicitly as
   `e1 : MvPolynomial (Fin 1) ℂ ≃ₐ[ℂ] Polynomial ℂ :=
      (MvPolynomial.finSuccEquiv ℂ 0).trans
        (Polynomial.mapAlgEquiv
          (MvPolynomial.isEmptyAlgEquiv ℂ (Fin 0)))` and
   `e : noSectionSurfaceBaseRing ≃ₐ[ℂ] Polynomial (Polynomial ℂ) :=
      (MvPolynomial.finSuccEquiv ℂ 1).trans
        (Polynomial.mapAlgEquiv e1)`.
   Lift the induced injection to
   `ℓ : noSectionSurfaceBase.functionField →+*
     FractionRing (Polynomial (Polynomial ℂ))`
   with `IsFractionRing.lift`.  Use `IsFractionRing.lift_algebraMap` to show
   that source variables `8` and `9` map respectively to
   `Polynomial.X` and
   `Polynomial.C (Polynomial.X : Polynomial ℂ)` in the nested polynomial
   fraction field.  The simplification lemmas are
   `MvPolynomial.finSuccEquiv_X_zero` and `MvPolynomial.finSuccEquiv_X_succ`.
3. Add a private arithmetic helper with a concrete interface:
   `nested_cubic_residue_ne_zero
      (p : Fin 3 → Fin 3 → Polynomial (Polynomial ℂ))
      (h00 : p 0 0 ≠ 0) :
      (∑ i, ∑ j, Polynomial.X ^ (i : ℕ) *
        Polynomial.C (Polynomial.X ^ (j : ℕ)) * (p i j) ^ 3) ≠ 0`.
   Prove it by choosing, among the nonzero summands, the lexicographically
   maximal pair
   `(p i j).natDegree,
     (p i j).leadingCoeff.natDegree`.  The outer degree of its summand is
   `3 * (p i j).natDegree + i`; equality of outer degrees forces equal `i`
   modulo `3`.  For terms with that `i`, the inner degree of the outer
   leading coefficient is
   `3 * (p i j).leadingCoeff.natDegree + j`, so equality forces equal `j`.
   Thus the maximal bidegree occurs once and its coefficient is nonzero.
   Use `Polynomial.natDegree_pow`, `Polynomial.natDegree_mul`,
   `Polynomial.leadingCoeff_pow`, and `Polynomial.leadingCoeff_mul` from
   `Mathlib/Algebra/Polynomial/Degree/Operations.lean`; the domain instances
   discharge all nonzero products.  This two-level lemma, rather than eight
   separate applications of `polynomial_cubic_no_solution`, is the missing
   arithmetic deliverable.
4. Apply `IsFractionRing.div_surjective` to each of the eight values
   `ℓ (f (MvPolynomial.X i))`, obtaining numerators `a i` and nonzero
   denominators `b i`.  Define `d := ∏ i, b i` and
   `dWithout i := ∏ j ∈ Finset.univ.erase i, b j`; use
   `Finset.prod_erase_mul` to rewrite `d = b i * dWithout i`.  After applying
   `congrArg ℓ` to the relation and multiplying by `d^3`, set
   `p 0 0 := d` and place `a i * dWithout i` in the other eight slots.
   Then `nested_cubic_residue_ne_zero p (Finset.prod_ne_zero ...)`
   contradicts the cleared equation.
5. Expanding only `noSectionSurfaceRelation`, `map_add`, `map_mul`, and
   `map_pow` gives the nine inputs in the required order and closes the
   contradiction.

Do not repeat the former block-commented generic-point attempt: it stopped
after constructing the fraction-field equation.  Steps 3 and 4 are the
unresolved part.
-/
theorem noSectionSurface_has_no_open_section :
    ¬ HasOpenSection noSectionSurfaceMorphism := by
  sorry

/-! ## Exercise `exercise-for-number-theorists` -/

/-- A closed subscheme of the displayed localization has a finite
surjective map to `Spec(ℤ)`. -/
/-
Interface audit: the statement is sound.  The quadratic order below is free
of rank two over `ℤ`, so it supplies both finiteness and the flatness required
by the pinned spectrum-surjectivity API.

Proof roadmap for the normal `prove` stage.

1. Use the monic polynomial `P = X ^ 2 - C 3 * X + 1 : Polynomial ℤ`
   and put `B := AdjoinRoot P`.  For `r := AdjoinRoot.root P`,
   `AdjoinRoot.eval₂_root P` from
   `Mathlib/RingTheory/AdjoinRoot.lean` gives
   `r ^ 2 - 3 * r + 1 = 0`.  Consequently
   `r`, `r - 1`, and `2 * r - 1` are units, with respective inverses
   `3 - r`, `r - 2`, and `2 * r - 5` (the last two products reduce to `1`
   using the displayed quadratic relation).
2. Identify `numberTheoryPolynomialRing = MvPolynomial (Fin 1) ℤ` with
   `Polynomial ℤ` using
   `e0 : MvPolynomial (Fin 0) ℤ ≃ₐ[ℤ] ℤ :=
      MvPolynomial.isEmptyAlgEquiv ℤ (Fin 0)` and
   `e := (MvPolynomial.finSuccEquiv ℤ 0).trans
      (Polynomial.mapAlgEquiv e0)`.  Define
   `g : numberTheoryPolynomialRing →+* B :=
      (AdjoinRoot.mk P).comp e.toRingHom`.
   Its surjectivity is `AdjoinRoot.mk_surjective.comp e.surjective`, and
   `MvPolynomial.finSuccEquiv_X_zero` shows that it sends `numberTheoryX`
   to `r`.
   Step 1 makes `g numberTheoryInvertingElement` a unit, so
   `IsLocalization.Away.lift` produces
   `ψ : numberTheoryLocalizationRing →+* B`.  Prove `ψ` surjective
   by lifting a `g`-preimage and rewriting with
   `IsLocalization.Away.lift_eq` (equivalently use
   `IsLocalization.Away.lift_comp`).
3. Take `Z := affineScheme B` and
   `i := Spec.map (CommRingCat.ofHom ψ)`.  Its closed-immersion instance is
   `IsClosedImmersion.spec_of_surjective` from
   `Mathlib/AlgebraicGeometry/Morphisms/ClosedImmersion.lean`.
   Install `P.monic.finite_adjoinRoot : Module.Finite ℤ B`; after proving
   `ψ.comp numberTheoryBaseToSource = AdjoinRoot.of P` from `lift_comp`,
   convert this to finiteness of the composite with `IsFinite.SpecMap_iff`
   from
   `Mathlib/AlgebraicGeometry/Morphisms/Finite.lean`.
4. The map `algebraMap ℤ B` is injective by
   `AdjoinRoot.of.injective_of_degree_ne_zero` after `norm_num [P]` proves
   `P.degree ≠ 0`.  Also install
   `P.monic.free_adjoinRoot : Module.Free ℤ B`; this supplies the
   `Module.Flat ℤ B` hypothesis which
   `PrimeSpectrum.comap_surjective_iff_injective_of_finite` actually
   requires in addition to `Module.Finite`.  Apply that lemma from
   `Mathlib/RingTheory/Flat/Rank.lean`, transport its conclusion through the
   `Spec.map_comp` equality from step 3, and package finiteness and
   topological surjectivity as `IsFiniteSurjective`.
-/
theorem exists_numberTheory_finite_surjective_closed_subscheme :
    ∃ (Z : Scheme.{0}) (i : Z ⟶ numberTheoryScheme),
      IsClosedImmersion i ∧
        IsFiniteSurjective (i ≫ numberTheoryMorphism) := by
  sorry

/-! ## Exercise `exercise-quasi-section` -/

/-- The finite-field variant has a finite surjective closed subscheme over
the polynomial base. -/
/-
Interface audit: the statement is sound.  `[Fact p.Prime]` gives the domain
structure needed for the monic AdjoinRoot injection, including the case
distinction hidden in `ZMod p`'s instances.

Proof roadmap for the normal `prove` stage.

1. Let `R := finiteFieldPolynomialRing p`, `t := MvPolynomial.X 0 : R`, and
   `P := X ^ 2 - C t * X + 1 : Polynomial R`.  With
   `B := AdjoinRoot P` and `r := AdjoinRoot.root P`, the relation
   `r ^ 2 - algebraMap R B t * r + 1 = 0` shows that `r` is a unit with
   inverse `algebraMap R B t - r`; hence `r - t` is a unit, and
   `t * r - 1 = r ^ 2` is a unit.
2. Use the exact equivalence
   `e := MvPolynomial.finSuccEquiv (ZMod p) 1 :
      finiteFieldTwoVariableRing p ≃ₐ[ZMod p] Polynomial R` and define
   `g := (AdjoinRoot.mk P).comp e.toRingHom`.  The simp lemmas
   `MvPolynomial.finSuccEquiv_X_zero` and
   `MvPolynomial.finSuccEquiv_X_succ` say that variables `0` and `1` map to
   `r` and `algebraMap R B t`, respectively.  Moreover
   `AdjoinRoot.mk_surjective.comp e.surjective` proves `g` surjective
   directly.  The three unit calculations show that
   `g (finiteFieldInvertingElement p)` is a unit, so lift to
   `ψ : finiteFieldLocalizationRing p →+* B` with
   `IsLocalization.Away.lift`; `IsLocalization.Away.lift_eq` and the
   surjectivity of `g` prove `ψ` surjective.
3. Set `Z := affineScheme B` and `i := Spec.map (CommRingCat.ofHom ψ)`.
   Apply `IsClosedImmersion.spec_of_surjective` to step 2.  The polynomial is
   monic, so `P.monic.finite_adjoinRoot` gives finiteness over `R`.
   Prove `ψ.comp (finiteFieldBaseToSource p) = AdjoinRoot.of P` using
   `IsLocalization.Away.lift_comp` and the two `finSuccEquiv` simp lemmas;
   then `IsFinite.SpecMap_iff` transfers finiteness to
   `i ≫ finiteFieldMorphism p` after `Spec.map_comp` normalization.
4. `[Fact p.Prime]` makes `R` a domain.  Use
   `AdjoinRoot.of.injective_of_degree_ne_zero` (the quadratic has nonzero
   degree), and install `P.monic.free_adjoinRoot` as well as
   `P.monic.finite_adjoinRoot`.  The free instance is essential:
   `PrimeSpectrum.comap_surjective_iff_injective_of_finite` is in a section
   with both `[Module.Flat R B]` and `[Module.Finite R B]`.  Apply it and
   transport along the composite equality from step 3.  Package the result
   as `IsFiniteSurjective`.
-/
theorem exists_finiteField_finite_surjective_closed_subscheme
    (p : ℕ) [Fact p.Prime] :
    ∃ (Z : Scheme.{0}) (i : Z ⟶ finiteFieldScheme p),
      IsClosedImmersion i ∧
        IsFiniteSurjective (i ≫ finiteFieldMorphism p) := by
  sorry

/-! ## Remark `remark-interpretation-skolem-noether` -/

/-- The two preceding exercises have the source's common geometric
interpretation: a finite surjective base change admits a section after base
change. -/
/-
Interface audit: the statement is sound, and the equality in `hlift` has the
orientation required by `pullback.lift`.

Proof roadmap for the normal `prove` stage.  This is purely categorical and
does not depend on either construction above.  Run
`rcases hlift with ⟨S', g, i, hg, hi⟩` and return
`⟨S', g, hg, ?_⟩`.  For the remaining `HasSection`, use
`s : S' ⟶ pullback f g := pullback.lift i (𝟙 S') (by simpa using hi)` and
return `⟨s, pullback.lift_snd _ _ _⟩`.  The declaration
`CategoryTheory.Limits.pullback.lift_snd` is in
`Mathlib/CategoryTheory/Limits/Shapes/Pullback/HasPullback.lean` and its
conclusion is definitionally the required
`s ≫ pullback.snd f g = 𝟙 S'`.  Keep every object at `Scheme.{u}`; no
universe lift or scheme-theoretic instance is involved.
-/
theorem finite_surjective_lift_interprets_as_base_change_section
    {X S : Scheme.{u}} (f : X ⟶ S)
    (hlift : ∃ (S' : Scheme.{u}) (g : S' ⟶ S) (i : S' ⟶ X),
      IsFiniteSurjective g ∧ i ≫ f = g) :
    HasFiniteSurjectiveBaseChangeSection f := by
  sorry

/-! ## Exercise `exercise-no-quasi-section` -/

/-- Some polynomial localization over `ℂ[t]` admits no finite surjective
closed subscheme over the base, while its defining polynomial has no factor
`t - α`. -/
/-
Interface audit: the existential statement is sound, and
`noQuasiSectionCandidate` is a viable witness.  Topological surjectivity will
be used together with reducedness of `ℂ[t]`; it does not make a general finite
algebra flat.

Proof roadmap for the normal `prove` stage.

1. Use `noQuasiSectionCandidate` as the witness.  For each `α : ℂ`, apply
   `evα : noQuasiSectionPolynomialRing →+* Polynomial ℂ :=
      MvPolynomial.eval₂Hom Polynomial.C
        (Fin.cases Polynomial.X (fun _ => Polynomial.C α))`.
   Then `evα (noQuasiSectionLinearFactor α) = 0`, whereas the candidate maps
   to `(Polynomial.X * Polynomial.C α - 2) *
     (Polynomial.X - Polynomial.C α + 3)`.  Show each factor nonzero by
   comparing coefficient `0` or `1` (split on `α = 0` for the first), and
   use the domain instance.  Applying `evα` to a divisibility equation gives
   the contradiction.
2. Isolate the hard part as a private ring-theoretic lemma with the following
   interface (write `tD := algebraMap noSectionBaseRing D
   (MvPolynomial.X 0)`):
   `finite_faithful_candidate_not_unit
      (D : Type) [CommRing D] [Algebra noSectionBaseRing D]
      [Module.Finite noSectionBaseRing D]
      (hinj : Function.Injective (algebraMap noSectionBaseRing D)) (x : D) :
      ¬ IsUnit ((x * tD - 2) * (x - tD + 3))`.

   Install `FaithfulSMul noSectionBaseRing D` with
   `faithfulSMul_iff_algebraMap_injective`.  Use lying over
   (`Algebra.IsIntegral.comap_surjective` in
   `Mathlib/RingTheory/Spectrum/Prime/Topology.lean`) to choose a prime of
   `D` over `(0)` and `Ideal.exists_minimalPrimes_le` to choose a minimal
   prime `q` below it.  Its contraction is zero, so
   `D' := D ⧸ q` is a domain, finite over
   `A := noSectionBaseRing`, and its algebra map is injective.  Transport
   along the explicit `A ≃ₐ[ℂ] Polynomial ℂ` equivalence used earlier and
   install the PID torsion-free module structure.  Extract
   `⟨n, b : Basis (Fin n) (Polynomial ℂ) D'⟩` from
   `Module.basisOfFiniteTypeTorsionFree'` in
   `Mathlib/LinearAlgebra/FreeModule/PID.lean`.  Prove `0 < n` from the
   injective algebra map and nontriviality of `Polynomial ℂ`.

   For a finite basis `b` of `D'`, let `M := Algebra.leftMulMatrix b x`.
   Since each factor is a unit, the determinants of
   `t • M - 2 • 1` and `M - (t - 3) • 1` are units of `ℂ[t]`, hence
   nonzero constants by `Matrix.isUnit_iff_isUnit_det` from
   `Mathlib/LinearAlgebra/Determinant.lean` and `Polynomial.isUnit_iff` in
   `Mathlib/Algebra/Polynomial/Degree/Units.lean`; call them `c` and `d`.
   The matrix identities follow by applying the algebra hom
   `Algebra.leftMulMatrix` from
   `Mathlib/LinearAlgebra/Matrix/ToLin.lean`, rather than unfolding matrix
   entries.

   Specialize the matrices at each of the two real roots `β₊`, `β₋` of
   `T ^ 2 - 3*T - 2`.  Since `β * (β - 3) = 2`,
   `RingHom.map_det` and `Matrix.det_smul` give
   `c = β ^ n * d` at either root.  Thus
   `β₊ ^ n = β₋ ^ n`; but `n > 0` and the roots have unequal absolute
   values.  Take `β₊ = (3 + Real.sqrt 17) / 2` and
   `β₋ = (3 - Real.sqrt 17) / 2`, prove `3 < β₊` and `-1 < β₋ ∧ β₋ < 0`
   with `Real.sq_sqrt`, `norm_num`, and `nlinarith`, then apply
   `abs_pow` and strict monotonicity of positive powers.  This determinant
   comparison is the substantive private lemma.
3. Given a forbidden `Z` and `i`,
   install the `IsClosedImmersion i` instance and use
   `IsClosedImmersion.isAffine_surjective_of_isAffine i` from
   `Mathlib/AlgebraicGeometry/Morphisms/ClosedImmersion.lean` makes `Z`
   affine and makes `i.appTop` surjective.  Conjugate by `Scheme.isoSpec Z`
   and set `D := Γ(Z, ⊤)`.  The finite composite supplies
   `Module.Finite noSectionBaseRing D` through `Scheme.Hom.finite_appTop`;
   normalize the resulting base ring hom using `Scheme.ΓSpecIso` and
   `Scheme.Hom.comp_appTop`.

   To prove that this base algebra map is injective, transport the assumed
   surjectivity of `(i ≫ noQuasiSectionMorphism _).base` through
   `Scheme.isoSpec` to surjectivity of its `PrimeSpectrum.comap`.  Hence its
   range is dense; apply
   `PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical` from
   `Mathlib/RingTheory/Spectrum/Prime/Topology.lean` and then
   `nilradical_eq_bot` for the domain `noSectionBaseRing`.  This proves that
   the kernel is bottom and hence the algebra map is injective.  Finally the
   localization algebra map sends the candidate to a unit by
   `IsLocalization.Away.algebraMap_isUnit`, and `i.appTop` preserves units,
   contradicting step 2.

Do not try to deduce the contradiction merely because the two displayed
factors are units: finite faithful `ℂ[t]`-algebras can have nonconstant
units (the quadratic `AdjoinRoot` construction in the finite-field roadmap
is the model counterexample).  Also do not use
`PrimeSpectrum.comap_surjective_iff_injective_of_finite` in step 3: despite
its name it additionally assumes `Module.Flat`, which the hypothetical
closed subscheme does not provide.  Reducedness plus dense range is the
correct route.
-/
theorem exists_noQuasiSection_polynomial :
    ∃ f : noQuasiSectionPolynomialRing,
      (∀ α : ℂ, ¬ noQuasiSectionLinearFactor α ∣ f) ∧
        ¬ ∃ (Z : Scheme.{0}) (i : Z ⟶ noQuasiSectionSource f),
          IsClosedImmersion i ∧
            IsFiniteSurjective (i ≫ noQuasiSectionMorphism f) := by
  sorry

/-! The source proposes a particular candidate with the qualification “I
think”.  The proposition is named below without upgrading the suggestion to
an additional theorem. -/

/-- The unproved property which the source suggests for its parenthetical
candidate.  The exercise only asks for existence of some polynomial. -/
def NoQuasiSectionCandidateWorks : Prop :=
    (∀ α : ℂ,
      ¬ noQuasiSectionLinearFactor α ∣ noQuasiSectionCandidate) ∧
      ¬ ∃ (Z : Scheme.{0})
          (i : Z ⟶ noQuasiSectionSource noQuasiSectionCandidate),
        IsClosedImmersion i ∧
          IsFiniteSurjective
            (i ≫ noQuasiSectionMorphism noQuasiSectionCandidate)

/-! ## Exercise `exercise-finite` -/

/-- A finite-type algebra which factors through a closed subscheme of a
projective space is finite, under the Noetherian hypothesis used in the
source's hint. -/
/-
Interface audit: the statement is sound and the factorization equality has
the correct contravariant orientation.  The shorter proper-plus-affine proof
does not use `hfiniteType` or `[IsNoetherianRing A]`; retain them because they
record the hypotheses of the exercise.

Proof roadmap for the normal `prove` stage.

1. Add the focused imports
   `Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Proper` and
   `Mathlib.AlgebraicGeometry.Morphisms.Proper`.  Prove a local helper
   `projectiveSpaceStructureMap_isProper (A) (n) :
     IsProper (projectiveSpaceStructureMap A n)`.  Two small ring helpers
   keep the elaboration local:

   * `degreeZero_algebraMap_surjective` says that
     `algebraMap A (projectiveSpaceGrading (R := A) n 0)` is surjective.
     For `z` in the homogeneous submodule, rewrite
     `MvPolynomial.homogeneousSubmodule_zero`; `Submodule.mem_one` and
     `MvPolynomial.algebraMap_eq` express `z.1` as `MvPolynomial.C a`.
     Thus `RingHom.Finite.of_surjective` and `IsFinite.SpecMap_iff` make the
     second `Spec.map` in `projectiveSpaceStructureMap` finite, hence proper.
   * Install
     `Algebra.FiniteType (projectiveSpaceGrading (R := A) n 0)
       (MvPolynomial (Fin (n + 1)) A)`.  Use the finite generating set
     `Finset.univ.image MvPolynomial.X`; prove its `Algebra.adjoin` is top by
     `MvPolynomial.induction_on`, observing that every constant coefficient
     lifts through the degree-zero algebra map from the previous bullet.
     The relevant definition and constructors are in
     `Mathlib/RingTheory/FiniteType.lean`.

   With that instance, `Proj.toSpecZero` is proper by the instance in
   `Mathlib/AlgebraicGeometry/ProjectiveSpectrum/Proper.lean`.  Unfold
   `projectiveSpaceStructureMap` only once and use the composition instance
   for `IsProper` to prove the helper.
2. Unpack `hfactor` as `⟨n, i, hi, hcomp⟩`.  A closed immersion is finite
   by the existing low-priority instance following
   `IsClosedImmersion.iff_isFinite_and_mono` in
   `Mathlib/AlgebraicGeometry/Morphisms/Finite.lean`, and a finite morphism is
   proper after importing `Proper.lean`.  Install `hi` as the local
   `IsClosedImmersion i` instance, compose it with step 1, and rewrite by
   `hcomp` to obtain
   `IsProper (affineSchemeMap f)`.
3. Any morphism between the two affine schemes here is `IsAffineHom`.
   Apply `IsFinite.iff_isProper_and_isAffineHom` from
   `Mathlib/AlgebraicGeometry/Morphisms/Proper.lean`, then translate
   `IsFinite (affineSchemeMap f)` to `RingHom.Finite f` with
   `IsFinite.SpecMap_iff`; `affineSchemeMap` unfolds to exactly the required
   `Spec.map (CommRingCat.ofHom f)`.
-/
theorem finite_of_projective_factorization
    {A B : Type u} [CommRing A] [CommRing B] [IsNoetherianRing A]
    (f : A →+* B) (hfiniteType : RingHom.FiniteType f)
    (hfactor :
      ∃ n : ℕ, ∃ i : affineScheme B ⟶ projectiveSpace A n,
        IsClosedImmersion i ∧
          i ≫ projectiveSpaceStructureMap A n = affineSchemeMap f) :
    RingHom.Finite f := by
  sorry

/-! ## Exercise `exercise-projective-finite` -/

/-- A morphism between projective varieties over an algebraically closed field
with finite closed-point fibres is finite. -/
/-
Interface audit: the statement is sound.  The quantifier in `hfib` is
intentionally restricted to closed points; `hY` makes `Y` Jacobson, so
neighborhoods constructed around all closed points cover `Y`.

Proof roadmap for the normal `prove` stage.

1. Add the focused imports
   `Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Proper`,
   `Mathlib.AlgebraicGeometry.Morphisms.Proper`,
   `Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated`,
   `Mathlib.AlgebraicGeometry.Morphisms.Separated`,
   `Mathlib.Topology.JacobsonSpace`, and
   `Mathlib.Algebra.Module.Submodule.Union`.  Unpack the projective parts of
   `hX` and `hY` as closed immersions `iX : X ⟶ projectiveSpace k n` and
   `iY : Y ⟶ projectiveSpace k m`.  The helper
   `projectiveSpaceStructureMap_isProper` from the preceding roadmap and the
   closed-immersion instances make `pX` and `pY` proper; hence `pY` is
   separated.  Rewrite `hbase` as `f ≫ pY = pX`, install
   `IsProper (f ≫ pY)`, and apply `IsProper.of_comp f pY` from
   `Mathlib/AlgebraicGeometry/Morphisms/Proper.lean` to get `IsProper f`.
   Also install `LocallyOfFiniteType pY` from `hY.2.1`; since `Spec k` is
   Jacobson, `LocallyOfFiniteType.jacobsonSpace pY` gives `JacobsonSpace Y`.
2. Prove a private finite-chart helper at the explicit universe `u`:

   `exists_projective_basicOpen_of_finite
      (T : Set X) (hT : T.Finite) :
      ∃ l : projectiveSpaceGrading (R := k) n 1,
        iX.base '' T ⊆
          (AlgebraicGeometry.Proj.basicOpen
            (projectiveSpaceGrading (R := k) n) l :
              Set (projectiveSpace k n))`.

   For each `x ∈ T`, membership in the projective spectrum says that not all
   degree-one coordinates lie in the homogeneous prime `iX.base x`.  The
   degree-one linear forms lying in that prime form a proper `k`-submodule
   of `projectiveSpaceGrading n 1`.  Apply
   `Submodule.exists_forall_notMem_of_forall_ne_top` from
   `Mathlib/Algebra/Module/Submodule/Union.lean`; `k` is infinite because it
   is algebraically closed.  Convert nonmembership to chart membership with
   `AlgebraicGeometry.Proj.mem_basicOpen`.  The resulting chart is affine by
   `AlgebraicGeometry.Proj.isAffineOpen_basicOpen` from
   `Mathlib/AlgebraicGeometry/ProjectiveSpectrum/Basic.lean`.
3. Fix a closed point `y : Y` and apply step 2 to
   `T := {x : X | f.base x = y}` using `hfib y hy`.  Let `U` be the chosen
   projective basic open and put
   `C := (iX.base ⁻¹' (U : Set (projectiveSpace k n)))ᶜ`.  This is closed in
   `X`.  Since `f` is proper, `f.isClosedMap` makes `f.base '' C` closed;
   it does not contain `y`.  Let `V₀` be its open complement and choose an
   affine open `V ≤ V₀` containing `y` using
   `Y.isBasis_affineOpens.exists_subset_of_mem_open`.  By construction,
   every point of `f ⁻¹ᵁ V` maps under `iX` into `U`.
4. Prove a second private helper, local in `y`, that the restricted source
   `openSubscheme Y V ×_Y X` is affine.  Form
   `j : X ⟶ pullback (projectiveSpaceStructureMap k n) pY` with
   `pullback.lift iX f` and the equations from `hX` and `hbase`.  Factor `j`
   as the relative graph of `f` followed by the base change of `iX`.
   The graph is a closed immersion because `pY` is separated (use the
   diagonal definition in
   `Mathlib/AlgebraicGeometry/Morphisms/Separated.lean`), and the second map
   is a closed immersion by stability under base change from
   `Mathlib/AlgebraicGeometry/Morphisms/ClosedImmersion.lean`; hence `j` is a
   closed immersion.

   Restrict `j` to the open product `U × V`.  Its range containment is step
   3, and `IsOpenImmersion.lift` performs the restriction.  Both `U` and `V`
   are affine, so their fibre product over `Spec k` is affine; a closed
   subscheme of it is affine by
   `IsClosedImmersion.isAffine_surjective_of_isAffine`.  This identifies the
   closed source with the restriction `f ∣_ V`, so the latter is an affine
   morphism.  Properness is stable under restriction.  Therefore
   `IsFinite.iff_isProper_and_isAffineHom` gives `IsFinite (f ∣_ V)`.
5. Perform steps 3 and 4 for every `y ∈ closedPoints Y` and let `W` be the
   supremum of the resulting opens `V y`.  It contains `closedPoints Y`, so
   `closure_closedPoints` from `Mathlib/Topology/JacobsonSpace.lean` and the
   fact that `Wᶜ` is closed imply `W = ⊤`.  Apply
   `IsZariskiLocalAtTarget.of_iSup_eq_top` (the instance for `IsFinite` is in
   `Mathlib/AlgebraicGeometry/Morphisms/Finite.lean`) to the family `V y` and
   the local finite instances from step 4.  This yields `IsFinite f`.

Known dead end: do not apply
`locallyQuasiFinite_iff_finite_preimage_singleton` directly to `hfib`; that
lemma quantifies over every scheme point.  The closed-point chart cover above
uses the Jacobson hypothesis directly and avoids the missing specialization
bridge.
-/
theorem finite_morphism_of_projective_varieties
    (k : Type u) [Field k] [IsAlgClosed k]
    (X Y : Scheme.{u})
    (pX : X ⟶ affineScheme k) (pY : Y ⟶ affineScheme k)
    (f : X ⟶ Y)
    (hX : IsProjectiveVarietyOver k X pX)
    (hY : IsProjectiveVarietyOver k Y pY)
    (hbase : f ≫ pY = pX)
    (hfib : ∀ y : Y, IsClosed ({y} : Set Y) →
      Set.Finite {x : X | f.base x = y}) :
    IsFinite f := by
  sorry

end

end Formalization.Books.Exercises.Unit34
