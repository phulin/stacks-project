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
Proof roadmap for the normal `prove` stage.

1. First isolate the only genuinely geometric input as a private polynomial
   lemma
   `tsen_conic_polynomial_solution (A B C) (hA) (hB) (hC)`, returning
   `X Y Z : noSectionBaseRing` with `Z ≠ 0` and
   `A * Z ^ 2 + B * X ^ 2 + C * Y ^ 2 = 0`.  Prove it by the dimension-count
   argument in the exercise: first transport `A`, `B`, and `C` through the
   `MvPolynomial (Fin 1) ℂ ≃ₐ[ℂ] Polynomial ℂ` equivalence used later in
   this file; for sufficiently large `d`, write `X`, `Y`, and `Z` with
   `d + 1` unknown complex coefficients and equate the at most
   `2 * d + max (e A).natDegree (max (e B).natDegree (e C).natDegree) + 1`
   coefficients.  Encode those homogeneous quadrics as a finite family in
   `MvPolynomial (Fin (3 * (d + 1))) ℂ`.  If their only common zero were
   the origin, `MvPolynomial.vanishingIdeal_zeroLocus_eq_radical` from
   `Mathlib/RingTheory/Nullstellensatz.lean` would identify their radical
   with the coordinate maximal ideal.  Krull's height bound
   `Ideal.height_le_card_of_mem_minimalPrimes_span_finset` from
   `Mathlib/RingTheory/Ideal/KrullsHeightTheorem.lean`, together with the
   polynomial-ring dimension computation in
   `Mathlib/RingTheory/KrullDimension/Polynomial.lean`, contradicts the
   strict inequality between the number of equations and `3 * (d + 1)`.
   Use `Polynomial.toFinsupp`/`Polynomial.ofFinsupp` from
   `Mathlib/Algebra/Polynomial/Coeff.lean` to turn the resulting nonzero
   coefficient vector into `X`, `Y`, and `Z`.  There is no packaged Tsen
   lemma, so these ideal-height steps belong in the private helper.  If its
   first homogeneous point has `Z = 0`, use the usual line through that
   smooth conic point over the infinite field
   `FractionRing (Polynomial ℂ)`, then clear denominators with
   `IsFractionRing.div_surjective`, to obtain one with `Z ≠ 0`.
2. Put `L := Localization.Away Z`.  The image of `Z` in `L` is a unit by
   `IsLocalization.Away.algebraMap_isUnit` in
   `Mathlib/RingTheory/Localization/Away/Basic.lean`.  Send variables `0,1,2`
   of `complexPolynomialRing 3` to `X / Z`, `Y / Z`, and the image of
   `MvPolynomial.X 0`, respectively, using `MvPolynomial.eval₂Hom`.  The
   polynomial identity from step 1 shows that
   `rationalSectionPolynomialRing A B C` maps to zero, so factor this map
   through `rationalSectionRing A B C` with `Ideal.Quotient.lift` and
   `Ideal.Quotient.lift_mk`.
3. Apply `AlgebraicGeometry.Spec.map` to the lifted ring map and precompose
   with `(basicOpenIsoSpecAway Z).hom`.  Assemble `HasOpenSection` with the
   open `PrimeSpectrum.basicOpen Z`; its nonemptiness follows from `Z ≠ 0`
   and the zero prime of the domain `noSectionBaseRing`.  Prove the section
   equation exactly as in `noSection_has_nonempty_open_section` above, using
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
2. Instantiate the base-ring equivalence at universe `0` as
   `noSectionSurfaceBaseRing ≃ₐ[ℂ] Polynomial (Polynomial ℂ)` using
   `MvPolynomial.finSuccEquiv`, `MvPolynomial.isEmptyAlgEquiv`, and
   `Polynomial.mapAlgEquiv` from `Mathlib/Algebra/MvPolynomial/Equiv.lean`.
   Lift the induced injection to
   `ℓ : noSectionSurfaceBase.functionField →+*
     FractionRing (Polynomial (Polynomial ℂ))`
   with `IsFractionRing.lift`.  Use `IsFractionRing.lift_algebraMap` to show
   that base variables `8` and `9` map to the outer variable `S` and the
   constant inner variable `T`.
3. Add a private arithmetic lemma for the `3 × 3` diagonal cubic form:
   after eight applications of `IsFractionRing.div_surjective`, multiply by
   the cube of a common nonzero denominator and obtain in
   `Polynomial (Polynomial ℂ)` an equation
   `d^3 + S*p00^3 + S^2*p10^3 + T*p01^3 + ... + S^2*T^2*p22^3 = 0`
   with `d ≠ 0`.  Rule this out by the lexicographic leading term: outer
   `Polynomial.natDegree_pow` and `natDegree_mul` separate the three
   exponents modulo `3`; when outer degrees tie, apply the same argument to
   `Polynomial.leadingCoeff` in the inner polynomial.  The one-variable
   pattern is the proved helper `polynomial_cubic_no_solution` above; the
   required degree and leading-coefficient lemmas are in
   `Mathlib/Algebra/Polynomial/Degree/Operations.lean`.
4. Apply that arithmetic lemma to `congrArg ℓ` of the relation from step 1.
   Expanding only `noSectionSurfaceRelation`, `map_add`, `map_mul`, and
   `map_pow` gives its nine inputs in the required order and closes the
   contradiction.

The former block-commented attempt duplicated the entire generic-point
scaffold and stopped exactly before step 3.  Repeating that scaffold does not
address the blocker; the missing deliverable is the two-variable diagonal
cubic lemma.
-/
theorem noSectionSurface_has_no_open_section :
    ¬ HasOpenSection noSectionSurfaceMorphism := by
  sorry

/-! ## Exercise `exercise-for-number-theorists` -/

/-- A closed subscheme of the displayed localization has a finite
surjective map to `Spec(ℤ)`. -/
/-
Proof roadmap for the normal `prove` stage.

1. Use the monic polynomial `P = X ^ 2 - C 3 * X + 1 : Polynomial ℤ`
   and put `B := AdjoinRoot P`.  For `r := AdjoinRoot.root P`,
   `AdjoinRoot.eval₂_root` gives `r ^ 2 - 3 * r + 1 = 0`.  Consequently
   `r`, `r - 1`, and `2 * r - 1` are units, with respective inverses
   `3 - r`, `r - 2`, and `2 * r - 5` (the last two products reduce to `1`
   using the displayed quadratic relation).
2. Identify `numberTheoryPolynomialRing = MvPolynomial (Fin 1) ℤ` with
   `Polynomial ℤ` via `MvPolynomial.finSuccEquiv` followed by
   `MvPolynomial.isEmptyAlgEquiv`, both from
   `Mathlib/Algebra/MvPolynomial/Equiv.lean`.  Compose this equivalence with
   `AdjoinRoot.mk P` to get a surjective map
   `g : numberTheoryPolynomialRing →+* B` sending `numberTheoryX` to `r`.
   Step 1 makes `g numberTheoryInvertingElement` a unit, so
   `IsLocalization.Away.lift` produces
   `ψ : numberTheoryLocalizationRing →+* B`.  Prove `ψ` surjective
   from `AdjoinRoot.mk_surjective` and `IsLocalization.Away.lift_eq`.
3. Take `Z := affineScheme B` and
   `i := Spec.map (CommRingCat.ofHom ψ)`.  Its closed-immersion instance is
   `IsClosedImmersion.spec_of_surjective` from
   `Mathlib/AlgebraicGeometry/Morphisms/ClosedImmersion.lean`.
   `P.monic.finite_adjoinRoot` from `Mathlib/RingTheory/AdjoinRoot.lean`
   supplies `Module.Finite ℤ B`; convert it to finiteness of the composite
   with `AlgebraicGeometry.IsFinite.SpecMap_iff` from
   `Mathlib/AlgebraicGeometry/Morphisms/Finite.lean`.
4. The map `algebraMap ℤ B` is injective by
   `AdjoinRoot.of.injective_of_degree_ne_zero`; with the finite-module
   instance, `PrimeSpectrum.comap_surjective_iff_injective_of_finite` from
   `Mathlib/RingTheory/Flat/Rank.lean` gives surjectivity on underlying
   spectra.  Finally normalize the composite with `Spec.map_comp` and the
   defining equation for the localization lift, then package the two facts
   as `IsFiniteSurjective`.
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
Proof roadmap for the normal `prove` stage.

1. Let `R := finiteFieldPolynomialRing p`, `t := MvPolynomial.X 0 : R`, and
   `P := X ^ 2 - C t * X + 1 : Polynomial R`.  With
   `B := AdjoinRoot P` and `r := AdjoinRoot.root P`, the relation
   `r ^ 2 - algebraMap R B t * r + 1 = 0` shows that `r` is a unit with
   inverse `algebraMap R B t - r`; hence `r - t` is a unit, and
   `t * r - 1 = r ^ 2` is a unit.
2. Define `g : finiteFieldTwoVariableRing p →+* B` by
   `MvPolynomial.eval₂Hom`, sending variable `0` to `r` and variable `1`
   to `algebraMap R B t`.  The three unit calculations show that
   `g (finiteFieldInvertingElement p)` is a unit, so lift to
   `ψ : finiteFieldLocalizationRing p →+* B` with
   `IsLocalization.Away.lift`.  Prove `ψ` surjective using
   `AdjoinRoot.mk_surjective`: coefficients in `R` come from variable `1`
   through `polynomialBaseMap`, while `r` comes from variable `0`.
3. Set `Z := affineScheme B` and `i := Spec.map (CommRingCat.ofHom ψ)`.
   Apply `IsClosedImmersion.spec_of_surjective` to step 2.  The polynomial is
   monic, so `P.monic.finite_adjoinRoot` gives finiteness over `R`, and
   `AlgebraicGeometry.IsFinite.SpecMap_iff` transfers it to
   `i ≫ finiteFieldMorphism p` after `Spec.map_comp` normalization.
4. `[Fact p.Prime]` makes `R` a domain.  Use
   `AdjoinRoot.of.injective_of_degree_ne_zero` and then
   `PrimeSpectrum.comap_surjective_iff_injective_of_finite` (files and
   universe `0` as in the preceding roadmap) for surjectivity of the
   composite.  Package the result as `IsFiniteSurjective`.
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
Proof roadmap for the normal `prove` stage.  This is purely categorical and
does not depend on either construction above.  Unpack `hlift` as
`⟨S', g, i, hg, hi⟩`, return the same `S'`, `g`, and `hg`, and define
`s : S' ⟶ pullback f g := pullback.lift i (𝟙 S')` using `hi` (after
rewriting `𝟙 S' ≫ g` to `g`).  The second projection equation
`pullback.lift_snd` from
`Mathlib/CategoryTheory/Limits/Shapes/Pullback/HasPullback.lean`
is exactly `s ≫ pullback.snd f g = 𝟙 S'`, so `⟨s, ...⟩` is the
required `HasSection`.  Keep all schemes at the theorem's explicit universe
`Scheme.{u}`; no universe lift is needed.
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
Proof roadmap for the normal `prove` stage.

1. Use `noQuasiSectionCandidate` as the witness.  For each `α : ℂ`, apply
   the evaluation homomorphism which sends variable `1` to `α` and leaves
   variable `0` free.  If `noQuasiSectionLinearFactor α` divided the
   candidate, its evaluation would be zero, whereas the displayed product
   evaluates to `(α * X - 2) * (X - α + 3) ≠ 0` in `Polynomial ℂ`.
   Build the homomorphism with `MvPolynomial.eval₂Hom` and the
   `MvPolynomial (Fin 1) ℂ ≃ₐ[ℂ] Polynomial ℂ` equivalence from
   `Mathlib/Algebra/MvPolynomial/Equiv.lean`; finish nonvanishing with the
   domain instance and coefficient comparison.
2. Isolate the hard part as a private ring-theoretic lemma with the following
   interface: for every commutative `noSectionBaseRing`-algebra `D` which is
   finite as a module and whose algebra map is injective, there is no `x : D`
   for which the image of
   `(noQuasiSectionX * noQuasiSectionT - 2) *
    (noQuasiSectionX - noQuasiSectionT + 3)` is a unit.  Use lying over
   (`Algebra.IsIntegral.comap_surjective` in
   `Mathlib/RingTheory/Spectrum/Prime/Topology.lean`) to choose a prime of
   `D` over `(0)` and quotient by a minimal prime below it.  The resulting
   domain `D'` is still finite and faithful over `A := Polynomial ℂ`, and
   `Module.free_of_finite_type_torsion_free` from
   `Mathlib/LinearAlgebra/FreeModule/PID.lean` makes it finite free of some
   positive rank `n`.

   For a finite basis `b` of `D'`, let `M := Algebra.leftMulMatrix b x`.
   Since each factor is a unit, the determinants of
   `t • M - 2 • 1` and `M - (t - 3) • 1` are units of `ℂ[t]`, hence
   nonzero constants by `Polynomial.isUnit_iff` in
   `Mathlib/Algebra/Polynomial/Degree/Units.lean`; call them `c` and `d`.
   Specialize the matrices at each of the two real roots `β₊`, `β₋` of
   `T ^ 2 - 3*T - 2`.  Since `β * (β - 3) = 2`,
   `Matrix.det_smul` gives `c = β ^ n * d` at either root.  Thus
   `β₊ ^ n = β₋ ^ n`; but `n > 0` and the roots have unequal absolute
   values (one lies in `(3, 4)`, the other in `(-1, 0)`), a contradiction.
   This determinant argument is the substantive proof obligation; it avoids
   developing normalization and valuations.
3. Given a forbidden `Z` and `i`,
   `i.isAffine_surjective_of_isAffine` from
   `Mathlib/AlgebraicGeometry/Morphisms/ClosedImmersion.lean` makes `Z`
   affine and makes `i.appTop` surjective.  Conjugate by `Scheme.isoSpec Z`
   to set `D := Γ(Z, ⊤)`.  The finite composite supplies
   `Module.Finite noSectionBaseRing D` through `Scheme.Hom.finite_appTop`;
   its topological surjectivity and
   `PrimeSpectrum.comap_surjective_iff_injective_of_finite` make the base
   algebra map injective.  Since the localization map sends the candidate
   to a unit and `i.appTop` preserves units, step 2 yields the contradiction.

Do not try to deduce the contradiction merely because the two displayed
factors are units: finite faithful `ℂ[t]`-algebras can have nonconstant
units (the quadratic `AdjoinRoot` construction in the finite-field roadmap
is the model counterexample).  The determinant comparison at both roots is
essential.
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
Proof roadmap for the normal `prove` stage.

1. Add the focused imports
   `Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Proper` and
   `Mathlib.AlgebraicGeometry.Morphisms.Proper`.  Prove a local helper
   `projectiveSpaceStructureMap_isProper (A) (n) :
     IsProper (projectiveSpaceStructureMap A n)`.  Unfold the definition in
   `Unit34/Core.lean`: `Proj.toSpecZero` is proper by the instance in
   `Mathlib/AlgebraicGeometry/ProjectiveSpectrum/Proper.lean`.  The remaining
   `Spec.map` is induced by `A → (projectiveSpaceGrading n) 0`; rewrite
   `MvPolynomial.homogeneousSubmodule_zero` from
   `Mathlib/RingTheory/MvPolynomial/Homogeneous.lean` to identify this map
   with an isomorphism, hence a proper morphism.
2. Unpack `hfactor` as `⟨n, i, hi, hcomp⟩`.  A closed immersion is finite
   by `IsClosedImmersion.iff_isFinite_and_mono` in
   `Mathlib/AlgebraicGeometry/Morphisms/Finite.lean`, and therefore proper.
   Install `hi` as the local `IsClosedImmersion i` instance, compose this
   with step 1, and rewrite by `hcomp` to obtain
   `IsProper (affineSchemeMap f)`.
3. Any morphism between the two affine schemes here is `IsAffineHom`.
   Apply `AlgebraicGeometry.IsFinite.iff_isProper_and_isAffineHom` from
   `Mathlib/AlgebraicGeometry/Morphisms/Proper.lean`, then translate
   `IsFinite (affineSchemeMap f)` to `RingHom.Finite f` with
   `AlgebraicGeometry.IsFinite.SpecMap_iff`.

The factorization equation has the correct contravariant orientation and is
the hypothesis actually used.  `hfiniteType` and `[IsNoetherianRing A]`
match the textbook's hinted proof but are redundant for the shorter
proper-plus-affine argument; do not change or manufacture either hypothesis.
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
Proof roadmap for the normal `prove` stage.

1. Unpack `hX` and `hY`.  The projective presentations and the properness
   helper from `finite_of_projective_factorization` make `pX` and `pY`
   proper and make `pY` separated.  Rewrite `hbase` so that
   `f ≫ pY = pX`; then `AlgebraicGeometry.IsProper.of_comp` from
   `Mathlib/AlgebraicGeometry/Morphisms/Proper.lean` gives `IsProper f`.
   Likewise `locallyOfFiniteType_of_comp` from
   `Mathlib/AlgebraicGeometry/Morphisms/FiniteType.lean` and
   `QuasiCompact.of_comp` from
   `Mathlib/AlgebraicGeometry/Morphisms/QuasiSeparated.lean` supply the two
   components of finite type for `f`.
2. Prove a private closed-fibre bridge: for a finite-type morphism between
   these projective `k`-varieties, finiteness of the inverse image of every
   closed point implies finiteness over every scheme point.  Argue by
   contradiction: a positive-dimensional component of a nonclosed fibre has
   closure in `X` whose image contains a nonempty open of its closure in
   `Y`; since finite-type schemes over the algebraically closed field `k`
   are Jacobson, that open contains a closed point, where the fibre is still
   positive-dimensional and hence has infinitely many closed points.  The
   relevant Jacobson and closed-point results are in
   `Mathlib/RingTheory/Spectrum/Prime/Jacobson.lean`; fibre dimension
   machinery is in `Mathlib/AlgebraicGeometry/Morphisms/QuasiFinite.lean`.
   This bridge is not currently packaged under a single Mathlib declaration.
3. With step 2, use
   `AlgebraicGeometry.locallyQuasiFinite_iff_finite_preimage_singleton` from
   `Mathlib/AlgebraicGeometry/Morphisms/QuasiFinite.lean` to obtain
   `LocallyQuasiFinite f` (instantiate its required `LocallyOfFiniteType` and
   `QuasiCompact` instances from step 1).
4. Formalize the source's local reduction as a private helper saying that a
   proper, locally quasi-finite, finite-type morphism with a projective
   closed-immersion presentation is finite.  Over an affine open of `Y`, use
   the finite fibre to choose an affine projective chart containing it;
   properness makes the image of the complementary closed set closed, so
   shrink the base until the whole inverse image lies in that chart.  The
   restricted source is then affine and its map has the projective closed
   factorization required by `finite_of_projective_factorization`.  The
   coordinate ring of the affine base is Noetherian because the base is
   finite type over the field `k`; install that instance and the induced
   `RingHom.FiniteType` instance, apply the preceding theorem, and glue with
   the target-local characterization of `IsFinite` in
   `Mathlib/AlgebraicGeometry/Morphisms/Finite.lean`.
5. The relative closed immersion used in step 4 comes from the closed
   immersion in `hX`: pair it with `f` to map into
   `projectiveSpace k n ×_{affineScheme k} Y`.  Use stability of
   `IsClosedImmersion` under base change from
   `Mathlib/AlgebraicGeometry/Morphisms/ClosedImmersion.lean` and `hbase` to
   identify the second projection with `f`.  `hY` supplies separatedness, so
   the necessary graph is a closed immersion.

The assumptions are sound and match the exercise: `hfib` deliberately only
quantifies over closed points.  Applying
`locallyQuasiFinite_iff_finite_preimage_singleton` directly to `hfib` is a
dead end because that lemma quantifies over all scheme points; step 2 is the
required missing argument.
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
