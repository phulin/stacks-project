import Formalization.Books.Exercises.Unit24.Core
import Mathlib.Algebra.Polynomial.Bivariate
import Mathlib.Algebra.Polynomial.SpecificDegree
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.ZMod.QuotientRing
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.RingTheory.RingHom.Flat
import Mathlib.RingTheory.Flat.Localization
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.RingTheory.Ideal.Int

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
  have hιinj : Function.Injective integerToLocalizationAt11 := by
    exact IsLocalization.injective integerLocalizationAt11
      (powers_le_nonZeroDivisors_of_noZeroDivisors
        (by norm_num : (11 : ℤ) ≠ 0))
  let _ : IsDomain integerLocalizationAt11 :=
    IsLocalization.Away.isDomain (S := integerLocalizationAt11) (x := (11 : ℤ))
      (by norm_num)
  letI : Fact (Nat.Prime 11) := ⟨by decide⟩
  letI : NeZero (11 : ℕ) := ⟨by decide⟩
  constructor
  · intro hgu
    rw [goingUpProperty_iff_primeSpectrum] at hgu
    let p : PrimeSpectrum ℤ := ⊥
    let p' : PrimeSpectrum ℤ :=
      ⟨RingHom.ker (Int.castRingHom (ZMod 11)), RingHom.ker_isPrime _⟩
    let P : PrimeSpectrum integerLocalizationAt11 := ⊥
    have hP : LiesOver integerToLocalizationAt11 p P := by
      apply PrimeSpectrum.ext
      rw [PrimeSpectrum.comap_asIdeal]
      dsimp [p, P]
      change Ideal.comap integerToLocalizationAt11 (⊥ : Ideal integerLocalizationAt11) =
        (⊥ : Ideal ℤ)
      apply le_antisymm
      · intro a ha
        have hzero : integerToLocalizationAt11 a = 0 :=
          RingHom.mem_ker.mp ha
        have hzero' : integerToLocalizationAt11 a =
            integerToLocalizationAt11 0 := by simpa using hzero
        simpa using hιinj hzero'
      · exact bot_le
    obtain ⟨Q, hQover, _⟩ :=
      hgu (p := p) (p' := p') (by simp [p]) (P := P) hP
    have h11p' : (11 : ℤ) ∈ p'.asIdeal := by
      change (11 : ℤ) ∈ RingHom.ker (Int.castRingHom (ZMod 11))
      apply CharP.cast_eq_zero
    have hQcomap : Ideal.comap integerToLocalizationAt11 Q.asIdeal = p'.asIdeal := by
      simpa only [PrimeSpectrum.comap_asIdeal] using
        congrArg PrimeSpectrum.asIdeal hQover
    have h11Q' : (11 : ℤ) ∈
        Ideal.comap integerToLocalizationAt11 Q.asIdeal := by
      rw [hQcomap]
      exact h11p'
    have h11Q : integerToLocalizationAt11 11 ∈ Q.asIdeal := h11Q'
    have hmul : integerToLocalizationAt11 11 *
        IsLocalization.Away.invSelf (11 : ℤ) ∈ Q.asIdeal := by
      exact Q.asIdeal.mul_mem_right _ h11Q
    have hone : (1 : integerLocalizationAt11) ∈ Q.asIdeal := by
      change (algebraMap ℤ integerLocalizationAt11) 11 *
          IsLocalization.Away.invSelf (11 : ℤ) ∈ Q.asIdeal at hmul
      rw [IsLocalization.Away.mul_invSelf] at hmul
      exact hmul
    exact Q.2.one_notMem hone
  · change @Algebra.HasGoingDown ℤ integerLocalizationAt11 _ _
      integerToLocalizationAt11.toAlgebra
    have hflat : RingHom.Flat integerToLocalizationAt11 := by
      letI : IsLocalization (Submonoid.powers (11 : ℤ))
          (Localization (Submonoid.powers (11 : ℤ))) :=
        Localization.isLocalization (R := ℤ)
          (M := Submonoid.powers (11 : ℤ))
      change RingHom.Flat (algebraMap ℤ integerLocalizationAt11)
      rw [RingHom.flat_algebraMap_iff]
      exact IsLocalization.flat (Localization (Submonoid.powers (11 : ℤ)))
        (Submonoid.powers (11 : ℤ))
    have halg : integerToLocalizationAt11.toAlgebra =
        (inferInstance : Algebra ℤ integerLocalizationAt11) := by
      ext a
      simp only [Algebra.smul_def]
      change integerToLocalizationAt11 a * _ =
        (algebraMap ℤ integerLocalizationAt11) a * _
      rfl
    let _ : Module ℤ integerLocalizationAt11 := Algebra.toModule
    have hflat' : Module.Flat ℤ integerLocalizationAt11 := by
      rw [← RingHom.flat_algebraMap_iff]
      exact hflat
    have hgdcan : @Algebra.HasGoingDown ℤ integerLocalizationAt11 _ _
        (inferInstance : Algebra ℤ integerLocalizationAt11) := by
      let _ : Module.Flat ℤ integerLocalizationAt11 := hflat'
      exact Algebra.HasGoingDown.of_flat
    let _ : Algebra ℤ integerLocalizationAt11 :=
      integerToLocalizationAt11.toAlgebra
    rw [halg]
    exact hgdcan

/-- Case (4): the displayed integral polynomial tower has going-up but not
going-down; its map has kernel `(y-x²)`. -/
theorem exercise_GU_GD_case_four (k : Type u) [Field k] [IsAlgClosed k] :
    GoingUpProperty (algebraicTowerMap k) ∧
      ¬ GoingDownProperty (algebraicTowerMap k) := by
  constructor
  · change @Algebra.HasGoingUp _ _ _ _ (algebraicTowerMap k).toAlgebra
    let _ : Algebra
        (Formalization.Books.Exercises.Unit16.polynomialRing k 2)
        (algebraicTowerRing k) := (algebraicTowerMap k).toAlgebra
    let z : algebraicTowerRing k :=
      Ideal.Quotient.mk (algebraicTowerIdeal k) (MvPolynomial.X (2 : Fin 3))
    have hz : IsIntegral
        (Formalization.Books.Exercises.Unit16.polynomialRing k 2) z := by
      let p : Polynomial
          (Formalization.Books.Exercises.Unit16.polynomialRing k 2) :=
        Polynomial.X ^ 2 - Polynomial.C (MvPolynomial.X (0 : Fin 2))
      refine ⟨p, ?_, ?_⟩
      · exact Polynomial.monic_X_pow_sub_C
          (MvPolynomial.X (0 : Fin 2)) (by norm_num)
      · have hzmem : MvPolynomial.X (2 : Fin 3) ^ 2 -
            MvPolynomial.X (0 : Fin 3) ∈ algebraicTowerIdeal k := by
          exact Ideal.subset_span (by simp [algebraicTowerIdeal])
        have hzero : Ideal.Quotient.mk (algebraicTowerIdeal k)
            (MvPolynomial.X (2 : Fin 3) ^ 2 - MvPolynomial.X (0 : Fin 3)) = 0 := by
          rw [Ideal.Quotient.eq_zero_iff_mem]
          exact hzmem
        have hmap0 : algebraMap
              (Formalization.Books.Exercises.Unit16.polynomialRing k 2)
              (algebraicTowerRing k) (MvPolynomial.X (0 : Fin 2)) =
            Ideal.Quotient.mk (algebraicTowerIdeal k)
              (MvPolynomial.X (0 : Fin 3)) := by
          simp [RingHom.algebraMap_toAlgebra, algebraicTowerMap]
        simpa [p, z, hmap0] using hzero
    let A : Subalgebra
        (Formalization.Books.Exercises.Unit16.polynomialRing k 2)
        (algebraicTowerRing k) :=
      Algebra.adjoin _ ({z} : Set (algebraicTowerRing k))
    have hA : Algebra.IsIntegral
        (Formalization.Books.Exercises.Unit16.polynomialRing k 2) A := by
      apply Algebra.IsIntegral.adjoin
      intro x hx
      rcases hx with rfl
      exact hz
    have hmem : ∀ y : algebraicTowerRing k, y ∈ A := by
      intro y
      obtain ⟨q, rfl⟩ := Ideal.Quotient.mk_surjective y
      induction q using MvPolynomial.induction_on with
      | C a =>
          have hmapC : algebraMap
                (Formalization.Books.Exercises.Unit16.polynomialRing k 2)
                (algebraicTowerRing k) (MvPolynomial.C a) =
              Ideal.Quotient.mk (algebraicTowerIdeal k) (MvPolynomial.C a) := by
            simp [RingHom.algebraMap_toAlgebra, algebraicTowerMap]
          rw [← hmapC]
          exact A.algebraMap_mem (MvPolynomial.C a)
      | add p q hp hq =>
          simpa [map_add] using A.add_mem hp hq
      | mul_X p i hp =>
          have hi : i = 0 ∨ i = 1 ∨ i = 2 := by
            fin_cases i <;> simp
          rcases hi with rfl | rfl | rfl
          · have hx :
                Ideal.Quotient.mk (algebraicTowerIdeal k)
                    (MvPolynomial.X (0 : Fin 3)) ∈ A := by
              have hmap0 : algebraMap
                    (Formalization.Books.Exercises.Unit16.polynomialRing k 2)
                    (algebraicTowerRing k) (MvPolynomial.X (0 : Fin 2)) =
                  Ideal.Quotient.mk (algebraicTowerIdeal k)
                    (MvPolynomial.X (0 : Fin 3)) := by
                simp [RingHom.algebraMap_toAlgebra, algebraicTowerMap]
              rw [← hmap0]
              exact A.algebraMap_mem (MvPolynomial.X (0 : Fin 2))
            simpa [map_mul] using A.mul_mem hp hx
          · have hx :
                Ideal.Quotient.mk (algebraicTowerIdeal k)
                    (MvPolynomial.X (1 : Fin 3)) ∈ A := by
              have hmap1 : algebraMap
                    (Formalization.Books.Exercises.Unit16.polynomialRing k 2)
                    (algebraicTowerRing k) (MvPolynomial.X (1 : Fin 2)) =
                  Ideal.Quotient.mk (algebraicTowerIdeal k)
                    (MvPolynomial.X (1 : Fin 3)) := by
                simp [RingHom.algebraMap_toAlgebra, algebraicTowerMap]
              rw [← hmap1]
              exact A.algebraMap_mem (MvPolynomial.X (1 : Fin 2))
            simpa [map_mul] using A.mul_mem hp hx
          · have hzA :
                Ideal.Quotient.mk (algebraicTowerIdeal k)
                    (MvPolynomial.X (2 : Fin 3)) ∈ A := by
              change z ∈ A
              exact Algebra.subset_adjoin (by simp)
            simpa [map_mul, z] using A.mul_mem hp hzA
    have hsurj : Function.Surjective A.val := by
      intro y
      exact ⟨⟨y, hmem y⟩, rfl⟩
    have hfull : Algebra.IsIntegral
        (Formalization.Books.Exercises.Unit16.polynomialRing k 2)
        (algebraicTowerRing k) := by
      exact hA.of_surjective A.val hsurj
    let _ : Algebra.IsIntegral
        (Formalization.Books.Exercises.Unit16.polynomialRing k 2)
        (algebraicTowerRing k) := hfull
    infer_instance
  · intro hgd
    rw [goingDownProperty_iff_primeSpectrum] at hgd
    let ev : Formalization.Books.Exercises.Unit16.polynomialRing k 3 →+* k :=
      MvPolynomial.eval₂Hom (RingHom.id k) (fun _ : Fin 3 => 0)
    have hI : algebraicTowerIdeal k ≤ RingHom.ker ev := by
      refine Ideal.span_le.2 ?_
      intro r hr
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hr
      rcases hr with rfl | rfl
      · change ev (MvPolynomial.X (0 : Fin 3) ^ 2 -
          MvPolynomial.X (1 : Fin 3)) = 0
        simp [ev]
      · change ev (MvPolynomial.X (2 : Fin 3) ^ 2 -
          MvPolynomial.X (0 : Fin 3)) = 0
        simp [ev]
    let e : algebraicTowerRing k →+* k :=
      Ideal.Quotient.lift (algebraicTowerIdeal k) ev hI
    let P' : PrimeSpectrum (algebraicTowerRing k) :=
      ⟨RingHom.ker e, RingHom.ker_isPrime _⟩
    let p : PrimeSpectrum
        (Formalization.Books.Exercises.Unit16.polynomialRing k 2) := ⊥
    let p' : PrimeSpectrum
        (Formalization.Books.Exercises.Unit16.polynomialRing k 2) :=
      PrimeSpectrum.comap (algebraicTowerMap k) P'
    let g : Formalization.Books.Exercises.Unit16.polynomialRing k 2 :=
      MvPolynomial.X (1 : Fin 2) - MvPolynomial.X (0 : Fin 2) ^ 2
    have hpg : g ≠ 0 := by
      let ev₂ : Formalization.Books.Exercises.Unit16.polynomialRing k 2 →+* k :=
        MvPolynomial.eval₂Hom (RingHom.id k)
          (fun i : Fin 2 => if i = 0 then 0 else 1)
      intro hg
      have hg' := congrArg ev₂ hg
      simpa [g, ev₂] using hg'
    have hgen : MvPolynomial.X (0 : Fin 3) ^ 2 -
        MvPolynomial.X (1 : Fin 3) ∈ algebraicTowerIdeal k := by
      exact Ideal.subset_span (by simp [algebraicTowerIdeal])
    have hrelmem : MvPolynomial.X (1 : Fin 3) -
        MvPolynomial.X (0 : Fin 3) ^ 2 ∈ algebraicTowerIdeal k := by
      simpa using (algebraicTowerIdeal k).neg_mem hgen
    have hrel : algebraicTowerMap k g = 0 := by
      have hmk : Ideal.Quotient.mk (algebraicTowerIdeal k)
          (MvPolynomial.X (1 : Fin 3) - MvPolynomial.X (0 : Fin 3) ^ 2) = 0 := by
        rw [Ideal.Quotient.eq_zero_iff_mem]
        exact hrelmem
      simpa [g, algebraicTowerMap] using hmk
    obtain ⟨P, hPover, _⟩ :=
      hgd (p := p) (p' := p') (by simp [p]) (P' := P') rfl
    have hgcomap : g ∈ Ideal.comap (algebraicTowerMap k) P.asIdeal := by
      change algebraicTowerMap k g ∈ P.asIdeal
      rw [hrel]
      exact P.asIdeal.zero_mem
    have hcomap : Ideal.comap (algebraicTowerMap k) P.asIdeal = p.asIdeal := by
      simpa only [PrimeSpectrum.comap_asIdeal] using
        congrArg PrimeSpectrum.asIdeal hPover
    have hgp : g ∈ p.asIdeal := by
      rw [← hcomap]
      exact hgcomap
    exact hpg (by simpa [p] using hgp)

/-- Case (5): `ℤ → ℤ[i,1/(2+i)]` has both properties. -/
theorem exercise_GU_GD_case_five :
    GoingUpProperty integerToGaussianLocalizationAtTwoPlusI ∧
      GoingDownProperty integerToGaussianLocalizationAtTwoPlusI := by
  have hmonic : gaussianPolynomial.Monic := by
    change (Polynomial.X ^ 2 + Polynomial.C (1 : ℤ)).Monic
    exact Polynomial.monic_X_pow_add_C (a := (1 : ℤ)) (by norm_num)
  have hdeg : gaussianPolynomial.natDegree = 2 := by
    change (Polynomial.X ^ 2 + Polynomial.C (1 : ℤ)).natDegree = 2
    rw [Polynomial.natDegree_add_C, Polynomial.natDegree_X_pow]
  have hprime : Prime gaussianPolynomial := by
    apply (UniqueFactorizationMonoid.irreducible_iff_prime).mp
    rw [hmonic.irreducible_iff_roots_eq_zero_of_degree_le_three (by omega) (by omega)]
    apply Multiset.eq_zero_of_forall_notMem
    intro x hx
    have hx' := (Polynomial.isRoot_of_mem_roots hx).eq_zero
    simp [gaussianPolynomial] at hx'
    nlinarith [sq_nonneg x]
  let _ : IsDomain gaussianIntegerModel := AdjoinRoot.isDomain_of_prime hprime
  let _ : Module.Finite ℤ gaussianIntegerModel := hmonic.finite_adjoinRoot
  let _ : Algebra.IsIntegral ℤ gaussianIntegerModel :=
    Algebra.IsIntegral.of_finite ℤ gaussianIntegerModel
  have hinjG : Function.Injective (algebraMap ℤ gaussianIntegerModel) := by
    simpa [AdjoinRoot.algebraMap_eq] using
      (AdjoinRoot.of.injective_of_degree_ne_zero
        (f := gaussianPolynomial) (by
          rw [Polynomial.degree_eq_natDegree hmonic.ne_zero, hdeg]
          norm_num))
  have ha0 : gaussianTwoPlusI ≠ 0 := by
    intro h
    have hi : gaussianImaginaryUnit = -(algebraMap ℤ gaussianIntegerModel 2) := by
      change algebraMap ℤ gaussianIntegerModel 2 + gaussianImaginaryUnit = 0 at h
      linear_combination h
    have hrel : gaussianImaginaryUnit ^ 2 + 1 = 0 := by
      simpa [gaussianPolynomial, gaussianImaginaryUnit] using
        (AdjoinRoot.eval₂_root gaussianPolynomial)
    rw [hi] at hrel
    have h5 : (algebraMap ℤ gaussianIntegerModel) 5 = 0 := by
      calc
        (algebraMap ℤ gaussianIntegerModel) 5 =
            (-(algebraMap ℤ gaussianIntegerModel 2)) ^ 2 + 1 := by norm_num
        _ = 0 := hrel
    have h5' : (algebraMap ℤ gaussianIntegerModel) 5 =
        (algebraMap ℤ gaussianIntegerModel) 0 := by
      simpa using h5
    have hzero : (5 : ℤ) = 0 := by simpa using hinjG h5'
    norm_num at hzero
  let _ : IsDomain gaussianLocalizationAtTwoPlusI :=
    IsLocalization.Away.isDomain (S := gaussianLocalizationAtTwoPlusI)
      (x := gaussianTwoPlusI) ha0
  letI : Fact (Nat.Prime 5) := ⟨by decide⟩
  letI : NeZero (5 : ℕ) := ⟨by decide⟩
  have hInt0 : ∀ x : gaussianIntegerModel,
      (algebraMap ℤ gaussianIntegerModel).IsIntegralElem x := by
    intro x
    exact Algebra.IsIntegral.isIntegral x
  have hGU0 : GoingUpProperty (algebraMap ℤ gaussianIntegerModel) := by
    letI : Algebra ℤ gaussianIntegerModel :=
      (algebraMap ℤ gaussianIntegerModel).toAlgebra
    letI : Algebra.IsIntegral ℤ gaussianIntegerModel := ⟨by
      intro x
      change (algebraMap ℤ gaussianIntegerModel).IsIntegralElem x
      exact hInt0 x⟩
    change @Algebra.HasGoingUp ℤ gaussianIntegerModel _ _
      (algebraMap ℤ gaussianIntegerModel).toAlgebra
    infer_instance
  have hGU0' := hGU0
  rw [goingUpProperty_iff_primeSpectrum] at hGU0'
  constructor
  · change @Algebra.HasGoingUp ℤ _ _ _
      integerToGaussianLocalizationAtTwoPlusI.toAlgebra
    change GoingUpProperty integerToGaussianLocalizationAtTwoPlusI
    rw [goingUpProperty_iff_primeSpectrum]
    intro p q hpq P hP
    let Q : PrimeSpectrum gaussianIntegerModel :=
      PrimeSpectrum.comap (algebraMap gaussianIntegerModel
        gaussianLocalizationAtTwoPlusI) P
    have hQover : LiesOver (algebraMap ℤ gaussianIntegerModel) p Q := by
      change PrimeSpectrum.comap (algebraMap ℤ gaussianIntegerModel) Q = p
      change PrimeSpectrum.comap
        ((algebraMap gaussianIntegerModel gaussianLocalizationAtTwoPlusI).comp
          (algebraMap ℤ gaussianIntegerModel)) P = p
      exact hP
    have hQdisj : Disjoint (Submonoid.powers gaussianTwoPlusI : Set gaussianIntegerModel)
        Q.asIdeal := by
      have h := (IsLocalization.isPrime_iff_isPrime_disjoint
        (Submonoid.powers gaussianTwoPlusI) gaussianLocalizationAtTwoPlusI P.asIdeal).mp P.2
      simpa [Q] using h.2
    by_cases hpq' : p = q
    · subst q
      exact ⟨P, hP, le_rfl⟩
    by_cases h5q : (5 : ℤ) ∈ q.asIdeal
    · have hpbot : p = (⊥ : PrimeSpectrum ℤ) := by
        by_contra hpbot
        letI : p.asIdeal.IsPrime := p.2
        have hpbotI : p.asIdeal ≠ (⊥ : Ideal ℤ) := by
          intro hpbotI
          exact hpbot (PrimeSpectrum.ext hpbotI)
        have hpmax : p.asIdeal.IsMaximal :=
          IsPrime.to_maximal_ideal hpbotI
        have heq : p.asIdeal = q.asIdeal :=
          hpmax.eq_of_le q.2.ne_top hpq
        exact hpq' (PrimeSpectrum.ext heq)
      have hspanle : Ideal.span ({(5 : ℤ)} : Set ℤ) ≤ q.asIdeal := by
        exact Ideal.span_le.2 (by simpa using h5q)
      have hqeq : Ideal.span ({(5 : ℤ)} : Set ℤ) = q.asIdeal :=
        (Int.ideal_span_isMaximal_of_prime 5).eq_of_le q.2.ne_top hspanle
      have hroot5 : gaussianPolynomial.eval₂ (Int.castRingHom (ZMod 5))
          (2 : ZMod 5) = 0 := by
        rw [Polynomial.eval₂_add, Polynomial.eval₂_X_pow, Polynomial.eval₂_C]
        change (5 : ZMod 5) = 0
        exact CharP.cast_eq_zero (R := ZMod 5) 5
      let e : gaussianIntegerModel →+* ZMod 5 :=
        AdjoinRoot.lift (Int.castRingHom (ZMod 5)) (2 : ZMod 5) hroot5
      let Q5 : PrimeSpectrum gaussianIntegerModel :=
        ⟨RingHom.ker e, RingHom.ker_isPrime _⟩
      have hek5 : RingHom.ker (Int.castRingHom (ZMod 5)) =
          Ideal.span ({(5 : ℤ)} : Set ℤ) := by
        ext a
        simp [Ideal.mem_span_singleton, ZMod.intCast_zmod_eq_zero_iff_dvd]
      have hQ5over : LiesOver (algebraMap ℤ gaussianIntegerModel) q Q5 := by
        apply PrimeSpectrum.ext
        rw [PrimeSpectrum.comap_asIdeal]
        change RingHom.ker (e.comp (algebraMap ℤ gaussianIntegerModel)) = q.asIdeal
        have hecomp : e.comp (algebraMap ℤ gaussianIntegerModel) =
            Int.castRingHom (ZMod 5) := by
          ext a
          simp [e]
        rw [hecomp, hek5, hqeq]
      have hQbot : Q.asIdeal = (⊥ : Ideal gaussianIntegerModel) := by
        apply Ideal.eq_bot_of_comap_eq_bot (R := ℤ)
        have hQcomap := congrArg PrimeSpectrum.asIdeal hQover
        rw [hpbot] at hQcomap
        exact hQcomap
      have haQ5 : gaussianTwoPlusI ∉ Q5.asIdeal := by
        change e gaussianTwoPlusI ≠ 0
        change e ((algebraMap ℤ gaussianIntegerModel) 2 +
          AdjoinRoot.root gaussianPolynomial) ≠ 0
        rw [map_add, AdjoinRoot.algebraMap_eq, AdjoinRoot.lift_of,
          AdjoinRoot.lift_root]
        norm_num
        exact (by
          intro h
          have h' := (ZMod.natCast_eq_natCast_iff 4 0 5).mp h
          have hd := (Nat.modEq_iff_dvd).mp h'
          norm_num at hd)
      have hQ5disj : Disjoint
          (Submonoid.powers gaussianTwoPlusI : Set gaussianIntegerModel) Q5.asIdeal := by
        rw [Set.disjoint_left]
        rintro x ⟨n, rfl⟩ hx
        by_cases hn : n = 0
        · subst n
          exact Q5.2.one_notMem hx
        · exact haQ5 (Q5.2.mem_of_pow_mem n hx)
      let P5 : PrimeSpectrum gaussianLocalizationAtTwoPlusI :=
        ⟨Ideal.map (algebraMap gaussianIntegerModel gaussianLocalizationAtTwoPlusI)
            Q5.asIdeal,
          IsLocalization.isPrime_of_isPrime_disjoint
            (Submonoid.powers gaussianTwoPlusI) gaussianLocalizationAtTwoPlusI
            Q5.asIdeal Q5.2 hQ5disj⟩
      have hP5overQ : LiesOver (algebraMap gaussianIntegerModel
          gaussianLocalizationAtTwoPlusI) Q5 P5 := by
        apply PrimeSpectrum.ext
        rw [PrimeSpectrum.comap_asIdeal]
        simpa [P5] using
          (IsLocalization.under_map_of_isPrime_disjoint
            (Submonoid.powers gaussianTwoPlusI) gaussianLocalizationAtTwoPlusI
            Q5.2 hQ5disj)
      have hP5over : LiesOver integerToGaussianLocalizationAtTwoPlusI q P5 := by
        change PrimeSpectrum.comap integerToGaussianLocalizationAtTwoPlusI P5 = q
        change PrimeSpectrum.comap
          ((algebraMap gaussianIntegerModel gaussianLocalizationAtTwoPlusI).comp
            (algebraMap ℤ gaussianIntegerModel)) P5 = q
        rw [PrimeSpectrum.comap_comp]
        change PrimeSpectrum.comap (algebraMap ℤ gaussianIntegerModel)
          (PrimeSpectrum.comap (algebraMap gaussianIntegerModel
            gaussianLocalizationAtTwoPlusI) P5) = q
        rw [hP5overQ, hQ5over]
      have hle : P.asIdeal ≤ P5.asIdeal := by
        rw [← IsLocalization.map_under (Submonoid.powers gaussianTwoPlusI)
          gaussianLocalizationAtTwoPlusI P.asIdeal]
        apply Ideal.map_mono
        change Q.asIdeal ≤ Q5.asIdeal
        rw [hQbot]
        exact bot_le
      exact ⟨P5, hP5over, hle⟩
    · obtain ⟨Q', hQ'over, hQQ'⟩ :=
        hGU0' (p := p) (p' := q) hpq (P := Q) hQover
      have h5Q' : (5 : ℤ) ∉
          Ideal.comap (algebraMap ℤ gaussianIntegerModel) Q'.asIdeal := by
        intro h5Q'
        have hcomapQ' : Ideal.comap (algebraMap ℤ gaussianIntegerModel)
            Q'.asIdeal = q.asIdeal := by
          simpa only [PrimeSpectrum.comap_asIdeal] using
            congrArg PrimeSpectrum.asIdeal hQ'over
        exact h5q (hcomapQ' ▸ h5Q')
      have haQ' : gaussianTwoPlusI ∉ Q'.asIdeal := by
        intro haQ'
        have hnorm : gaussianTwoPlusI *
            (algebraMap ℤ gaussianIntegerModel 2 - gaussianImaginaryUnit) =
            algebraMap ℤ gaussianIntegerModel 5 := by
          have hrel : gaussianImaginaryUnit ^ 2 + 1 = 0 := by
            simpa [gaussianPolynomial, gaussianImaginaryUnit] using
              (AdjoinRoot.eval₂_root gaussianPolynomial)
          change (2 + gaussianImaginaryUnit) *
              (2 - gaussianImaginaryUnit) = 5
          calc
            (2 + gaussianImaginaryUnit) * (2 - gaussianImaginaryUnit) =
                4 - gaussianImaginaryUnit ^ 2 := by ring
            _ = 5 := by
              have hi2 : gaussianImaginaryUnit ^ 2 = -1 := by
                linear_combination hrel
              rw [hi2]
              norm_num
        have h5mem : algebraMap ℤ gaussianIntegerModel 5 ∈ Q'.asIdeal := by
          rw [← hnorm]
          exact Q'.asIdeal.mul_mem_right _ haQ'
        exact h5Q' (by exact h5mem)
      have hQ'disj : Disjoint
          (Submonoid.powers gaussianTwoPlusI : Set gaussianIntegerModel) Q'.asIdeal := by
        rw [Set.disjoint_left]
        rintro x ⟨n, rfl⟩ hx
        by_cases hn : n = 0
        · subst n
          exact Q'.2.one_notMem hx
        · exact haQ' (Q'.2.mem_of_pow_mem n hx)
      let P' : PrimeSpectrum gaussianLocalizationAtTwoPlusI :=
        ⟨Ideal.map (algebraMap gaussianIntegerModel gaussianLocalizationAtTwoPlusI)
            Q'.asIdeal,
          IsLocalization.isPrime_of_isPrime_disjoint
            (Submonoid.powers gaussianTwoPlusI) gaussianLocalizationAtTwoPlusI
            Q'.asIdeal Q'.2 hQ'disj⟩
      have hP'overQ : LiesOver (algebraMap gaussianIntegerModel
          gaussianLocalizationAtTwoPlusI) Q' P' := by
        apply PrimeSpectrum.ext
        rw [PrimeSpectrum.comap_asIdeal]
        simpa [P'] using
          (IsLocalization.under_map_of_isPrime_disjoint
            (Submonoid.powers gaussianTwoPlusI) gaussianLocalizationAtTwoPlusI
            Q'.2 hQ'disj)
      have hP'over : LiesOver integerToGaussianLocalizationAtTwoPlusI q P' := by
        change PrimeSpectrum.comap integerToGaussianLocalizationAtTwoPlusI P' = q
        change PrimeSpectrum.comap
          ((algebraMap gaussianIntegerModel gaussianLocalizationAtTwoPlusI).comp
            (algebraMap ℤ gaussianIntegerModel)) P' = q
        rw [PrimeSpectrum.comap_comp]
        change PrimeSpectrum.comap (algebraMap ℤ gaussianIntegerModel)
          (PrimeSpectrum.comap (algebraMap gaussianIntegerModel
            gaussianLocalizationAtTwoPlusI) P') = q
        rw [hP'overQ, hQ'over]
      have hle : P.asIdeal ≤ P'.asIdeal := by
        rw [← IsLocalization.map_under (Submonoid.powers gaussianTwoPlusI)
          gaussianLocalizationAtTwoPlusI P.asIdeal]
        exact Ideal.map_mono hQQ'
      exact ⟨P', hP'over, hle⟩
  · change @Algebra.HasGoingDown ℤ _ _ _
      integerToGaussianLocalizationAtTwoPlusI.toAlgebra
    have hmonic : gaussianPolynomial.Monic := by
      dsimp [gaussianPolynomial]
      exact Polynomial.monic_X_pow_add_C (a := (1 : ℤ)) (by norm_num)
    let _ : Module.Free ℤ gaussianIntegerModel := hmonic.free_adjoinRoot
    have hgd0 : @Algebra.HasGoingDown ℤ gaussianIntegerModel _ _
        (inferInstance : Algebra ℤ gaussianIntegerModel) := by
      let _ : Module.Flat ℤ gaussianIntegerModel := inferInstance
      exact Algebra.HasGoingDown.of_flat
    have hflat : RingHom.Flat
        (algebraMap gaussianIntegerModel gaussianLocalizationAtTwoPlusI) := by
      letI : IsLocalization (Submonoid.powers gaussianTwoPlusI)
          gaussianLocalizationAtTwoPlusI :=
        Localization.isLocalization (R := gaussianIntegerModel)
          (M := Submonoid.powers gaussianTwoPlusI)
      rw [RingHom.flat_algebraMap_iff]
      exact IsLocalization.flat gaussianLocalizationAtTwoPlusI
        (Submonoid.powers gaussianTwoPlusI)
    have hgd1 : @Algebra.HasGoingDown gaussianIntegerModel
        gaussianLocalizationAtTwoPlusI _ _
        (inferInstance : Algebra gaussianIntegerModel gaussianLocalizationAtTwoPlusI) := by
      let _ : Module gaussianIntegerModel gaussianLocalizationAtTwoPlusI := Algebra.toModule
      have : Module.Flat gaussianIntegerModel gaussianLocalizationAtTwoPlusI := by
        rw [← RingHom.flat_algebraMap_iff]
        exact hflat
      exact Algebra.HasGoingDown.of_flat
    have hgdcomp : @Algebra.HasGoingDown ℤ gaussianLocalizationAtTwoPlusI _ _
        (inferInstance : Algebra ℤ gaussianLocalizationAtTwoPlusI) := by
      exact Algebra.HasGoingDown.trans ℤ gaussianIntegerModel
        gaussianLocalizationAtTwoPlusI
    have halg : integerToGaussianLocalizationAtTwoPlusI.toAlgebra =
        (inferInstance : Algebra ℤ gaussianLocalizationAtTwoPlusI) := by
      ext a
      simp only [Algebra.smul_def]
      change integerToGaussianLocalizationAtTwoPlusI a * _ =
        (algebraMap ℤ gaussianLocalizationAtTwoPlusI) a * _
      rfl
    rw [halg]
    exact hgdcomp

/-- Case (6): `ℤ → ℤ[i,1/(14+7i)]` has going-down but not going-up. -/
theorem exercise_GU_GD_case_six :
    ¬ GoingUpProperty integerToGaussianLocalizationAtFourteenPlusSevenI ∧
      GoingDownProperty integerToGaussianLocalizationAtFourteenPlusSevenI := by
  have hmonic : gaussianPolynomial.Monic := by
    change (Polynomial.X ^ 2 + Polynomial.C (1 : ℤ)).Monic
    exact Polynomial.monic_X_pow_add_C (a := (1 : ℤ)) (by norm_num)
  have hdeg : gaussianPolynomial.natDegree = 2 := by
    change (Polynomial.X ^ 2 + Polynomial.C (1 : ℤ)).natDegree = 2
    rw [Polynomial.natDegree_add_C, Polynomial.natDegree_X_pow]
  have hprime : Prime gaussianPolynomial := by
    apply (UniqueFactorizationMonoid.irreducible_iff_prime).mp
    rw [hmonic.irreducible_iff_roots_eq_zero_of_degree_le_three (by omega) (by omega)]
    · apply Multiset.eq_zero_of_forall_notMem
      intro x hx
      have hx' := (Polynomial.isRoot_of_mem_roots hx).eq_zero
      simp [gaussianPolynomial] at hx'
      nlinarith [sq_nonneg x]
  let _ : IsDomain gaussianIntegerModel := AdjoinRoot.isDomain_of_prime hprime
  have ha0 : gaussianFourteenPlusSevenI ≠ 0 := by
    intro h
    have h' : (7 : gaussianIntegerModel) * gaussianTwoPlusI = 0 := by
      calc
        (7 : gaussianIntegerModel) * gaussianTwoPlusI =
            gaussianFourteenPlusSevenI := by
              simp [gaussianFourteenPlusSevenI, gaussianTwoPlusI]
              ring
        _ = 0 := h
    have h7 : (7 : gaussianIntegerModel) ≠ 0 := by
      intro h7
      have h7' : (algebraMap ℤ gaussianIntegerModel) 7 = 0 := by
        simpa using h7
      have h7'' : AdjoinRoot.of gaussianPolynomial 7 =
          AdjoinRoot.of gaussianPolynomial 0 := by
        simpa [AdjoinRoot.algebraMap_eq] using h7'
      have hzero : (7 : ℤ) = 0 :=
        (AdjoinRoot.of.injective_of_degree_ne_zero
          (f := gaussianPolynomial) (by
            rw [Polynomial.degree_eq_natDegree hmonic.ne_zero, hdeg]
            norm_num)) h7''
      norm_num at hzero
    have hb : gaussianTwoPlusI = 0 := (mul_eq_zero.mp h').resolve_left h7
    have hi : gaussianImaginaryUnit = -(algebraMap ℤ gaussianIntegerModel 2) := by
      change algebraMap ℤ gaussianIntegerModel 2 + gaussianImaginaryUnit = 0 at hb
      linear_combination hb
    have hrel : gaussianImaginaryUnit ^ 2 + 1 = 0 := by
      simpa [gaussianPolynomial, gaussianImaginaryUnit] using
        (AdjoinRoot.eval₂_root gaussianPolynomial)
    rw [hi] at hrel
    have h5 : (algebraMap ℤ gaussianIntegerModel) 5 = 0 := by
      calc
        (algebraMap ℤ gaussianIntegerModel) 5 =
            (-(algebraMap ℤ gaussianIntegerModel 2)) ^ 2 + 1 := by norm_num
        _ = 0 := hrel
    have h5' : AdjoinRoot.of gaussianPolynomial 5 =
        AdjoinRoot.of gaussianPolynomial 0 := by
      simpa [AdjoinRoot.algebraMap_eq] using h5
    have hzero : (5 : ℤ) = 0 :=
      (AdjoinRoot.of.injective_of_degree_ne_zero
        (f := gaussianPolynomial) (by
          rw [Polynomial.degree_eq_natDegree hmonic.ne_zero, hdeg]
          norm_num)) h5'
    norm_num at hzero
  let _ : IsDomain gaussianLocalizationAtFourteenPlusSevenI :=
    IsLocalization.Away.isDomain (S := gaussianLocalizationAtFourteenPlusSevenI)
      (x := gaussianFourteenPlusSevenI) ha0
  letI : Fact (Nat.Prime 7) := ⟨by decide⟩
  letI : NeZero (7 : ℕ) := ⟨by decide⟩
  constructor
  · intro hgu
    rw [goingUpProperty_iff_primeSpectrum] at hgu
    let p : PrimeSpectrum ℤ := ⊥
    let p' : PrimeSpectrum ℤ :=
      ⟨RingHom.ker (Int.castRingHom (ZMod 7)), RingHom.ker_isPrime _⟩
    let P : PrimeSpectrum gaussianLocalizationAtFourteenPlusSevenI := ⊥
    have hP : LiesOver integerToGaussianLocalizationAtFourteenPlusSevenI p P := by
      apply PrimeSpectrum.ext
      rw [PrimeSpectrum.comap_asIdeal]
      dsimp [p, P]
      change Ideal.comap integerToGaussianLocalizationAtFourteenPlusSevenI
          (⊥ : Ideal gaussianLocalizationAtFourteenPlusSevenI) = (⊥ : Ideal ℤ)
      have hinjG : Function.Injective (algebraMap ℤ gaussianIntegerModel) :=
        by
          simpa [AdjoinRoot.algebraMap_eq] using
            (AdjoinRoot.of.injective_of_degree_ne_zero
              (f := gaussianPolynomial) (by
                rw [Polynomial.degree_eq_natDegree hmonic.ne_zero, hdeg]
                norm_num))
      have hinjL : Function.Injective integerToGaussianLocalizationAtFourteenPlusSevenI :=
        (IsLocalization.injective gaussianLocalizationAtFourteenPlusSevenI
          (powers_le_nonZeroDivisors_of_noZeroDivisors ha0)).comp hinjG
      exact Ideal.comap_bot_of_injective _ hinjL
    obtain ⟨Q, hQover, _⟩ :=
      hgu (p := p) (p' := p') (by simp [p]) (P := P) hP
    have h7p' : (7 : ℤ) ∈ p'.asIdeal := by
      change (7 : ℤ) ∈ RingHom.ker (Int.castRingHom (ZMod 7))
      apply CharP.cast_eq_zero
    have hQcomap : Ideal.comap integerToGaussianLocalizationAtFourteenPlusSevenI
        Q.asIdeal = p'.asIdeal := by
      simpa only [PrimeSpectrum.comap_asIdeal] using
        congrArg PrimeSpectrum.asIdeal hQover
    have h7Q' : (7 : ℤ) ∈
        Ideal.comap integerToGaussianLocalizationAtFourteenPlusSevenI Q.asIdeal := by
      rw [hQcomap]
      exact h7p'
    have h7Q : integerToGaussianLocalizationAtFourteenPlusSevenI 7 ∈ Q.asIdeal := h7Q'
    have hmul : integerToGaussianLocalizationAtFourteenPlusSevenI 7 *
        ((algebraMap gaussianIntegerModel gaussianLocalizationAtFourteenPlusSevenI)
          gaussianTwoPlusI *
          IsLocalization.Away.invSelf gaussianFourteenPlusSevenI) ∈ Q.asIdeal := by
      exact Q.asIdeal.mul_mem_right _ h7Q
    have hone : (1 : gaussianLocalizationAtFourteenPlusSevenI) ∈ Q.asIdeal := by
      change (algebraMap ℤ gaussianLocalizationAtFourteenPlusSevenI) 7 *
          ((algebraMap gaussianIntegerModel gaussianLocalizationAtFourteenPlusSevenI)
            gaussianTwoPlusI *
            IsLocalization.Away.invSelf gaussianFourteenPlusSevenI) ∈ Q.asIdeal at hmul
      rw [IsScalarTower.algebraMap_apply ℤ gaussianIntegerModel
        gaussianLocalizationAtFourteenPlusSevenI] at hmul
      have hmul' :
          (algebraMap gaussianIntegerModel gaussianLocalizationAtFourteenPlusSevenI)
              ((algebraMap ℤ gaussianIntegerModel) 7 * gaussianTwoPlusI) *
            IsLocalization.Away.invSelf gaussianFourteenPlusSevenI ∈ Q.asIdeal := by
        simpa only [map_mul, mul_assoc] using hmul
      rw [show (algebraMap ℤ gaussianIntegerModel) 7 * gaussianTwoPlusI =
          gaussianFourteenPlusSevenI by
            simp [gaussianFourteenPlusSevenI, gaussianTwoPlusI]
            ring] at hmul'
      rw [IsLocalization.Away.mul_invSelf] at hmul'
      exact hmul'
    exact Q.2.one_notMem hone
  · change @Algebra.HasGoingDown ℤ _ _ _
      integerToGaussianLocalizationAtFourteenPlusSevenI.toAlgebra
    have hmonic : gaussianPolynomial.Monic := by
      dsimp [gaussianPolynomial]
      exact Polynomial.monic_X_pow_add_C (a := (1 : ℤ)) (by norm_num)
    let _ : Module.Free ℤ gaussianIntegerModel := hmonic.free_adjoinRoot
    have hgd0 : @Algebra.HasGoingDown ℤ gaussianIntegerModel _ _
        (inferInstance : Algebra ℤ gaussianIntegerModel) := by
      let _ : Module.Flat ℤ gaussianIntegerModel := inferInstance
      exact Algebra.HasGoingDown.of_flat
    have hflat : RingHom.Flat
        (algebraMap gaussianIntegerModel gaussianLocalizationAtFourteenPlusSevenI) := by
      letI : IsLocalization (Submonoid.powers gaussianFourteenPlusSevenI)
          gaussianLocalizationAtFourteenPlusSevenI :=
        Localization.isLocalization (R := gaussianIntegerModel)
          (M := Submonoid.powers gaussianFourteenPlusSevenI)
      rw [RingHom.flat_algebraMap_iff]
      exact IsLocalization.flat gaussianLocalizationAtFourteenPlusSevenI
        (Submonoid.powers gaussianFourteenPlusSevenI)
    have hgd1 : @Algebra.HasGoingDown gaussianIntegerModel
        gaussianLocalizationAtFourteenPlusSevenI _ _
        (inferInstance : Algebra gaussianIntegerModel
          gaussianLocalizationAtFourteenPlusSevenI) := by
      let _ : Module gaussianIntegerModel gaussianLocalizationAtFourteenPlusSevenI :=
        Algebra.toModule
      have : Module.Flat gaussianIntegerModel
          gaussianLocalizationAtFourteenPlusSevenI := by
        rw [← RingHom.flat_algebraMap_iff]
        exact hflat
      exact Algebra.HasGoingDown.of_flat
    have hgdcomp : @Algebra.HasGoingDown ℤ gaussianLocalizationAtFourteenPlusSevenI _ _
        (inferInstance : Algebra ℤ gaussianLocalizationAtFourteenPlusSevenI) := by
      exact Algebra.HasGoingDown.trans ℤ gaussianIntegerModel
        gaussianLocalizationAtFourteenPlusSevenI
    have halg : integerToGaussianLocalizationAtFourteenPlusSevenI.toAlgebra =
        (inferInstance : Algebra ℤ gaussianLocalizationAtFourteenPlusSevenI) := by
      ext a
      simp only [Algebra.smul_def]
      change integerToGaussianLocalizationAtFourteenPlusSevenI a * _ =
        (algebraMap ℤ gaussianLocalizationAtFourteenPlusSevenI) a * _
      rfl
    rw [halg]
    exact hgdcomp

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
