import Formalization.Books.Exercises.Unit24.Core
import Mathlib.Algebra.Polynomial.Bivariate
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.RingTheory.RingHom.Flat

/-!
# Exercises, Chapter 24: Going up and going down

This file records the source-facing interfaces for the definition and the
three numbered exercises.  Proposition proofs are deferred to the proving
stage; the underlying rings, maps, and answer sets are defined in `Core`.
-/

noncomputable section

universe u

open Set

namespace Formalization.Books.Exercises.Unit24

/-! ## Definition `GU-GD` -/

/-- The explicit prime-spectrum form of the going-up definition in the source.

`GoingUpProperty` itself reuses Mathlib's canonical algebraic predicate; this
equivalence exposes the source's quantifiers over prime spectra and its
"lying over" terminology. -/
theorem goingUpProperty_iff_primeSpectrum
    {A B : Type*} [CommRing A] [CommRing B] (φ : A →+* B) :
    GoingUpProperty φ ↔
      ∀ {p p' : PrimeSpectrum A}, p.asIdeal ≤ p'.asIdeal →
        ∀ {P : PrimeSpectrum B}, LiesOver φ p P →
          ∃ P' : PrimeSpectrum B,
            LiesOver φ p' P' ∧ P.asIdeal ≤ P'.asIdeal := by
  change @Algebra.HasGoingUp A B _ _ φ.toAlgebra ↔ _
  rw [@Algebra.HasGoingUp.iff_specializingMap_primeSpectrumComap A B _ _ φ.toAlgebra]
  simp only [SpecializingMap, Relation.Fibration, flip, LiesOver,
    RingHom.algebraMap_toAlgebra, ← PrimeSpectrum.le_iff_specializes,
    PrimeSpectrum.asIdeal_le_asIdeal]
  constructor <;> intro h
  · intro p p' hp P hP
    obtain ⟨P0, hPP0, hP0⟩ :=
      h (a := P) (b := p') (by simpa [hP] using hp)
    exact ⟨P0, hP0, hPP0⟩
  · intro a b hab
    obtain ⟨a0, hP0, hcomp⟩ := h hab rfl
    exact ⟨a0, hcomp, hP0⟩

/-- The explicit prime-spectrum form of the going-down definition in the
source. -/
theorem goingDownProperty_iff_primeSpectrum
    {A B : Type*} [CommRing A] [CommRing B] (φ : A →+* B) :
    GoingDownProperty φ ↔
      ∀ {p p' : PrimeSpectrum A}, p.asIdeal ≤ p'.asIdeal →
        ∀ {P' : PrimeSpectrum B}, LiesOver φ p' P' →
          ∃ P : PrimeSpectrum B,
            LiesOver φ p P ∧ P.asIdeal ≤ P'.asIdeal := by
  change @Algebra.HasGoingDown A B _ _ φ.toAlgebra ↔ _
  rw [@Algebra.HasGoingDown.iff_generalizingMap_primeSpectrumComap A B _ _ φ.toAlgebra]
  simp only [GeneralizingMap, Relation.Fibration, LiesOver,
    RingHom.algebraMap_toAlgebra, ← PrimeSpectrum.le_iff_specializes,
    PrimeSpectrum.asIdeal_le_asIdeal]
  constructor <;> intro h
  · intro p p' hp P' hP'
    obtain ⟨P, hP, hcomp⟩ :=
      h (a := P') (b := p) (by simpa [hP'] using hp)
    exact ⟨P, hcomp, hP⟩
  · intro a b hab
    obtain ⟨a0, hP0, hcomp⟩ := h hab rfl
    exact ⟨a0, hcomp, hP0⟩

/-! ## Exercise `GU-GD` -/

/- The seven declarations below preserve the hypotheses and record the
   determination requested for each item of the source exercise. -/

/-- Case (1): `k → k[x]` has both going-up and going-down. -/
theorem exercise_GU_GD_case_one (k : Type u) [Field k] :
    GoingUpProperty (fieldToPolynomialMap k) ∧
      GoingDownProperty (fieldToPolynomialMap k) := by
  constructor
  · rw [goingUpProperty_iff_primeSpectrum]
    intro p p' hp P hP
    have hpbot : p.asIdeal = ⊥ :=
      (Ideal.eq_bot_or_top p.asIdeal).resolve_right p.2.ne_top
    have hp'bot : p'.asIdeal = ⊥ :=
      (Ideal.eq_bot_or_top p'.asIdeal).resolve_right p'.2.ne_top
    have hpp' : p = p' := PrimeSpectrum.ext (hpbot.trans hp'bot.symm)
    subst p'
    exact ⟨P, hP, le_rfl⟩
  · change @Algebra.HasGoingDown k (Polynomial k) _ _
      (fieldToPolynomialMap k).toAlgebra
    let _ : Algebra k (Polynomial k) := (fieldToPolynomialMap k).toAlgebra
    infer_instance

/-- Case (2): `k[x] → k[x,y]` has going-down but not going-up. -/
theorem exercise_GU_GD_case_two (k : Type u) [Field k] :
    ¬ GoingUpProperty (polynomialToBivariateMap k) ∧
      GoingDownProperty (polynomialToBivariateMap k) := by
  let L := Localization.Away (Polynomial.X : Polynomial k)
  let ι : Polynomial k →+* L := algebraMap (Polynomial k) L
  let f : Formalization.Books.Exercises.Unit16.polynomialRing k 2 →+* L :=
    MvPolynomial.eval₂Hom
      (algebraMap k L)
      (fun i : Fin 2 =>
        if i = 0 then ι Polynomial.X
        else IsLocalization.Away.invSelf (Polynomial.X : Polynomial k))
  let _ : IsDomain L :=
    IsLocalization.Away.isDomain (S := L) (x := (Polynomial.X : Polynomial k))
      Polynomial.X_ne_zero
  have hcomp : f.comp (polynomialToBivariateMap k) = ι := by
    apply Polynomial.ringHom_ext'
    · ext a
      simp only [RingHom.comp_apply]
      simp [f, ι, polynomialToBivariateMap,
        Formalization.Books.Exercises.Unit16.polynomialRing]
      exact (IsScalarTower.algebraMap_apply k (Polynomial k) L a).symm
    · simp [f, ι, polynomialToBivariateMap,
        Formalization.Books.Exercises.Unit16.polynomialRing]
  have hrel : MvPolynomial.X (0 : Fin 2) * MvPolynomial.X (1 : Fin 2) - 1 ∈
      RingHom.ker f := by
    rw [RingHom.mem_ker]
    simp [f]
    rw [IsLocalization.Away.mul_invSelf]
    simp
  have hιinj : Function.Injective ι := by
    exact IsLocalization.injective L
      (powers_le_nonZeroDivisors_of_noZeroDivisors Polynomial.X_ne_zero)
  let p : PrimeSpectrum (Polynomial k) := ⊥
  let q : PrimeSpectrum (Polynomial k) :=
    ⟨RingHom.ker (Polynomial.evalRingHom (0 : k)), RingHom.ker_isPrime _⟩
  let P : PrimeSpectrum (Formalization.Books.Exercises.Unit16.polynomialRing k 2) :=
    ⟨RingHom.ker f, RingHom.ker_isPrime _⟩
  have hP : LiesOver (polynomialToBivariateMap k) p P := by
    apply PrimeSpectrum.ext
    rw [PrimeSpectrum.comap_asIdeal]
    change Ideal.comap (polynomialToBivariateMap k) (RingHom.ker f) =
      (⊥ : Ideal (Polynomial k))
    apply le_antisymm
    · intro a ha
      have hzero : f (polynomialToBivariateMap k a) = 0 :=
        RingHom.mem_ker.mp ha
      change (f.comp (polynomialToBivariateMap k)) a = 0 at hzero
      rw [hcomp] at hzero
      have hzero' : ι a = ι 0 := by simpa using hzero
      simpa using hιinj hzero'
    · exact bot_le
  have hnot : ¬ GoingUpProperty (polynomialToBivariateMap k) := by
    intro hgu
    rw [goingUpProperty_iff_primeSpectrum] at hgu
    obtain ⟨Q, hQover, hPQ⟩ :=
      hgu (p := p) (p' := q) (by simp [p]) (P := P) hP
    have hxq : Polynomial.X ∈ q.asIdeal := by
      change Polynomial.X ∈ RingHom.ker (Polynomial.evalRingHom (0 : k))
      simp
    have hQcomap : Ideal.comap (polynomialToBivariateMap k) Q.asIdeal = q.asIdeal := by
      simpa only [PrimeSpectrum.comap_asIdeal] using
        congrArg PrimeSpectrum.asIdeal hQover
    have hxQ' : Polynomial.X ∈ Ideal.comap (polynomialToBivariateMap k) Q.asIdeal := by
      rw [hQcomap]
      exact hxq
    have hxQ : polynomialToBivariateMap k Polynomial.X ∈ Q.asIdeal := hxQ'
    have hmul : MvPolynomial.X (0 : Fin 2) * MvPolynomial.X (1 : Fin 2) ∈
        Q.asIdeal := by
      simpa [polynomialToBivariateMap] using
        Q.asIdeal.mul_mem_right (MvPolynomial.X (1 : Fin 2)) hxQ
    have hrelQ : MvPolynomial.X (0 : Fin 2) * MvPolynomial.X (1 : Fin 2) - 1 ∈
        Q.asIdeal := hPQ hrel
    have hone : (1 : Formalization.Books.Exercises.Unit16.polynomialRing k 2) ∈
        Q.asIdeal := by
      simpa using Q.asIdeal.sub_mem hmul hrelQ
    exact Q.2.one_notMem hone
  have hmap : polynomialToBivariateMap k =
      (Polynomial.Bivariate.equivMvPolynomial k).toRingHom.comp
        (Polynomial.C : Polynomial k →+* Polynomial (Polynomial k)) := by
    ext a <;> simp [polynomialToBivariateMap, Polynomial.Bivariate.equivMvPolynomial]
  have hC : RingHom.Flat
      (Polynomial.C : Polynomial k →+* Polynomial (Polynomial k)) := by
    rw [show (Polynomial.C : Polynomial k →+* Polynomial (Polynomial k)) =
      algebraMap (Polynomial k) (Polynomial (Polynomial k)) by rfl]
    exact RingHom.flat_algebraMap_iff.mpr (by infer_instance)
  have hflat : RingHom.Flat (polynomialToBivariateMap k) := by
    rw [hmap]
    exact RingHom.Flat.comp hC
      (RingHom.Flat.of_bijective (Polynomial.Bivariate.equivMvPolynomial k).bijective)
  constructor
  · exact hnot
  · change @Algebra.HasGoingDown (Polynomial k)
      (Formalization.Books.Exercises.Unit16.polynomialRing k 2) _ _
      (polynomialToBivariateMap k).toAlgebra
    let _ : Algebra (Polynomial k)
        (Formalization.Books.Exercises.Unit16.polynomialRing k 2) :=
      (polynomialToBivariateMap k).toAlgebra
    have _ : Module.Flat (Polynomial k)
        (Formalization.Books.Exercises.Unit16.polynomialRing k 2) := hflat
    exact Algebra.HasGoingDown.of_flat

/-- Case (3): `ℤ → ℤ[1/11]` has going-down but not going-up. -/
theorem exercise_GU_GD_case_three :
    ¬ GoingUpProperty integerToLocalizationAt11 ∧
      GoingDownProperty integerToLocalizationAt11 := by
  sorry

/-- Case (4): the displayed integral polynomial tower has going-up but not
going-down; its map has kernel `(y-x²)`. -/
theorem exercise_GU_GD_case_four (k : Type u) [Field k] [IsAlgClosed k] :
    GoingUpProperty (algebraicTowerMap k) ∧
      ¬ GoingDownProperty (algebraicTowerMap k) := by
  sorry

/-- Case (5): `ℤ → ℤ[i,1/(2+i)]` has both properties. -/
theorem exercise_GU_GD_case_five :
    GoingUpProperty integerToGaussianLocalizationAtTwoPlusI ∧
      GoingDownProperty integerToGaussianLocalizationAtTwoPlusI := by
  sorry

/-- Case (6): `ℤ → ℤ[i,1/(14+7i)]` has going-down but not going-up. -/
theorem exercise_GU_GD_case_six :
    ¬ GoingUpProperty integerToGaussianLocalizationAtFourteenPlusSevenI ∧
      GoingDownProperty integerToGaussianLocalizationAtFourteenPlusSevenI := by
  sorry

/-- Case (7): the idempotent-localized quotient has going-down but not
going-up. -/
theorem exercise_GU_GD_case_seven (k : Type u) [Field k] [IsAlgClosed k] :
    ¬ GoingUpProperty (idempotentLocalizationMap k) ∧
      GoingDownProperty (idempotentLocalizationMap k) := by
  sorry

/-! ## Exercise `image` -/

/-- The image of `D(f)` under `Spec(A[X]) → Spec(A)` is the union of the
basic opens of all coefficients of `f`.  Coefficients outside the finite
support are zero, so the indexed union is the source's finite union
`D(a₀) ∪ ⋯ ∪ D(aᵣ)`. -/
theorem image_basicOpen_polynomial_eq_iUnion_coefficients
    {A : Type*} [CommRing A] (f : Polynomial A) :
    PrimeSpectrum.comap (Polynomial.C : A →+* Polynomial A) ''
        (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum (Polynomial A))) =
      ⋃ i : ℕ,
        (PrimeSpectrum.basicOpen (f.coeff i) : Set (PrimeSpectrum A)) := by
  rw [Polynomial.image_comap_C_basicOpen]
  ext p
  simp only [Set.mem_compl_iff, PrimeSpectrum.mem_zeroLocus,
    Set.mem_iUnion]
  rw [Set.not_subset]
  simp

/-! ## Exercise `images` -/

/-- Image computation (1): `Spec(k[x,yx⁻¹]) → Spec(k[x,y])`. -/
theorem exercise_images_case_one (k : Type u) [Field k] [IsAlgClosed k] :
    Set.range (PrimeSpectrum.comap (reciprocalImageMap k)) =
      reciprocalImageAnswer k := by
  sorry

/-- Image computation (2): `Spec(k[x,y,a,b]/(ax-by-1)) → Spec(k[x,y])`. -/
theorem exercise_images_case_two (k : Type u) [Field k] [IsAlgClosed k] :
    Set.range (PrimeSpectrum.comap (unitEquationMap k)) =
      unitEquationImageAnswer k := by
  sorry

/-- Image computation (3): the localized cusp parameterization. -/
theorem exercise_images_case_three (k : Type u) [Field k] [IsAlgClosed k] :
    Set.range (PrimeSpectrum.comap (cuspParameterMap k)) =
      cuspImageAnswer k := by
  sorry

/-- Image computation (4): the complex cubic curve mapped by squaring both
coordinates. -/
theorem exercise_images_case_four :
    Set.range (PrimeSpectrum.comap cubicSquareMap) = cubicImageAnswer := by
  sorry

end Formalization.Books.Exercises.Unit24

end
