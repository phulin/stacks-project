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
                  simp [τ, Scheme.restrictFunctorΓ] <;>
                    erw [← Functor.map_comp] <;>
                    simpa using (noRationalSectionBase.presheaf.germ_res
                      (homOfLE (x := U) (show U ≤ ⊤ from le_top))
                      (genericPoint noRationalSectionBase) hxU).symm
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
    simpa [ℓ, eg, e, e0, MvPolynomial.finSuccEquiv_X_zero] using h
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
  sorry

/-! ## Exercise `exercise-no-section-curve` -/

/-- The cubic curve example has no rational section. -/
theorem noSectionCurve_has_no_open_section :
    ¬ HasOpenSection noSectionCurveMorphism := by
  sorry

/-! ## Exercise `exercise-no-section-surface` -/

/-- The eight-variable cubic surface example has no rational section. -/
theorem noSectionSurface_has_no_open_section :
    ¬ HasOpenSection noSectionSurfaceMorphism := by
  sorry

/-! ## Exercise `exercise-for-number-theorists` -/

/-- A closed subscheme of the displayed localization has a finite
surjective map to `Spec(ℤ)`. -/
theorem exists_numberTheory_finite_surjective_closed_subscheme :
    ∃ (Z : Scheme.{0}) (i : Z ⟶ numberTheoryScheme),
      IsClosedImmersion i ∧
        IsFiniteSurjective (i ≫ numberTheoryMorphism) := by
  sorry

/-! ## Exercise `exercise-quasi-section` -/

/-- The finite-field variant has a finite surjective closed subscheme over
the polynomial base. -/
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
theorem exists_noQuasiSection_polynomial :
    ∃ f : noQuasiSectionPolynomialRing,
      (∀ α : ℂ, ¬ noQuasiSectionLinearFactor α ∣ f) ∧
        ¬ ∃ (Z : Scheme.{0}) (i : Z ⟶ noQuasiSectionSource f),
          IsClosedImmersion i ∧
            IsFiniteSurjective (i ≫ noQuasiSectionMorphism f) := by
  sorry

/-! The source proposes a particular candidate with the qualification “I
think”.  It is retained as a separate theorem interface rather than silently
upgrading that suggestion to an established fact. -/

/-- The candidate suggested parenthetically by the source has the claimed
non-quasi-section property. -/
theorem noQuasiSection_candidate_works :
    (∀ α : ℂ,
      ¬ noQuasiSectionLinearFactor α ∣ noQuasiSectionCandidate) ∧
      ¬ ∃ (Z : Scheme.{0})
          (i : Z ⟶ noQuasiSectionSource noQuasiSectionCandidate),
        IsClosedImmersion i ∧
          IsFiniteSurjective
            (i ≫ noQuasiSectionMorphism noQuasiSectionCandidate) := by
  sorry

/-! ## Exercise `exercise-finite` -/

/-- A finite-type algebra which factors through a closed subscheme of a
projective space is finite, under the Noetherian hypothesis used in the
source's hint. -/
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
