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
import Mathlib.RingTheory.Nullstellensatz

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
  let : Fact (Nat.Prime 11) := ⟨by decide⟩
  let : NeZero (11 : ℕ) := ⟨by decide⟩
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
      let : IsLocalization (Submonoid.powers (11 : ℤ))
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
          exact Ideal.subset_span (by simp)
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
      simp [g, ev₂] at hg'
    have hgen : MvPolynomial.X (0 : Fin 3) ^ 2 -
        MvPolynomial.X (1 : Fin 3) ∈ algebraicTowerIdeal k := by
      exact Ideal.subset_span (by simp)
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
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  let : NeZero (5 : ℕ) := ⟨by decide⟩
  have hInt0 : ∀ x : gaussianIntegerModel,
      (algebraMap ℤ gaussianIntegerModel).IsIntegralElem x := by
    intro x
    exact Algebra.IsIntegral.isIntegral x
  have hGU0 : GoingUpProperty (algebraMap ℤ gaussianIntegerModel) := by
    let : Algebra ℤ gaussianIntegerModel :=
      (algebraMap ℤ gaussianIntegerModel).toAlgebra
    let : Algebra.IsIntegral ℤ gaussianIntegerModel := ⟨by
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
        let : p.asIdeal.IsPrime := p.2
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
      let : IsLocalization (Submonoid.powers gaussianTwoPlusI)
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
  let : Fact (Nat.Prime 7) := ⟨by decide⟩
  let : NeZero (7 : ℕ) := ⟨by decide⟩
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
      let : IsLocalization (Submonoid.powers gaussianFourteenPlusSevenI)
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
  let A := Polynomial k
  let R₂ := Formalization.Books.Exercises.Unit16.polynomialRing k 2
  let I := idempotentPolynomialIdeal k
  let C := idempotentQuotientRing k
  let B := idempotentLocalizationRing k
  let s := idempotentLocalizationElement k
  let K := Localization.Away (Polynomial.X - Polynomial.C 1 : Polynomial k)
  have hsne : (Polynomial.X - Polynomial.C 1 : Polynomial k) ≠ 0 := by
    intro h
    have h' := congrArg (fun f : Polynomial k => f.eval 0) h
    simpa using h'
  let _ : IsDomain K :=
    IsLocalization.Away.isDomain (S := K)
      (x := (Polynomial.X - Polynomial.C 1 : Polynomial k)) hsne
  let r : R₂ →+* K :=
    MvPolynomial.eval₂Hom (algebraMap k K)
      (fun i : Fin 2 => if i = 0 then
        algebraMap (Polynomial k) K Polynomial.X else 1)
  have hr0 : r (MvPolynomial.X (0 : Fin 2)) =
      algebraMap (Polynomial k) K Polynomial.X := by
    change MvPolynomial.eval₂Hom (algebraMap k K)
      (fun i : Fin 2 => if i = 0 then
        algebraMap (Polynomial k) K Polynomial.X else 1)
      (MvPolynomial.X (0 : Fin 2)) = _
    rw [MvPolynomial.eval₂Hom_X']
    simp
  have hr1 : r (MvPolynomial.X (1 : Fin 2)) = 1 := by
    change MvPolynomial.eval₂Hom (algebraMap k K)
      (fun i : Fin 2 => if i = 0 then
        algebraMap (Polynomial k) K Polynomial.X else 1)
      (MvPolynomial.X (1 : Fin 2)) = _
    rw [MvPolynomial.eval₂Hom_X']
    simp
  have hr : I ≤ RingHom.ker r := by
    apply Ideal.span_le.2
    rintro z (rfl : z = _)
    change r (MvPolynomial.X (1 : Fin 2) ^ 2 - MvPolynomial.X (1 : Fin 2)) = 0
    rw [map_sub, map_pow, hr1]
    simp
  let c : C →+* K := Ideal.Quotient.lift I r hr
  have hc : c s = algebraMap (Polynomial k) K
      (Polynomial.X - Polynomial.C 1) := by
    change r (MvPolynomial.X (0 : Fin 2) * MvPolynomial.X (1 : Fin 2) - 1) = _
    have hC : (algebraMap (Polynomial k) K) (Polynomial.C 1) = 1 := by
      change (algebraMap (Polynomial k) K)
        ((algebraMap k (Polynomial k)) (1 : k)) = 1
      rw [← IsScalarTower.algebraMap_apply k (Polynomial k) K]
      simp
    calc
      r (MvPolynomial.X (0 : Fin 2) * MvPolynomial.X (1 : Fin 2) - 1) =
          r (MvPolynomial.X (0 : Fin 2)) * r (MvPolynomial.X (1 : Fin 2)) - r 1 := by
            simp only [map_sub, map_mul, map_one]
      _ = (algebraMap (Polynomial k) K) Polynomial.X - 1 := by
        rw [hr0, hr1]
        simp
      _ = (algebraMap (Polynomial k) K) Polynomial.X -
          (algebraMap (Polynomial k) K) (Polynomial.C 1) := by rw [hC]
      _ = (algebraMap (Polynomial k) K)
          (Polynomial.X - Polynomial.C 1) :=
        (map_sub (algebraMap (Polynomial k) K) _ _).symm
  have hunit : IsUnit (c s) := by
    rw [hc]
    exact IsLocalization.Away.algebraMap_isUnit _
  let bmap : B →+* K := IsLocalization.Away.lift s hunit
  let P : PrimeSpectrum B := ⟨RingHom.ker bmap, RingHom.ker_isPrime _⟩
  have hcomp : bmap.comp (idempotentLocalizationMap k) =
      algebraMap (Polynomial k) K := by
    apply Polynomial.ringHom_ext'
    · ext z
      simp only [RingHom.comp_apply]
      rw [show idempotentLocalizationMap k (Polynomial.C z) =
          (algebraMap C B) ((Ideal.Quotient.mk I) (MvPolynomial.C z)) by
            simp [idempotentLocalizationMap,
              idempotentLocalizationCoefficientMap, C, B, I]]
      rw [IsLocalization.Away.lift_eq]
      change r (MvPolynomial.C z) = _
      have hrC : r (MvPolynomial.C z) = algebraMap k K z := by
        change MvPolynomial.eval₂Hom (algebraMap k K)
          (fun i : Fin 2 => if i = 0 then
            algebraMap (Polynomial k) K Polynomial.X else 1)
          (MvPolynomial.C z) = _
        rw [MvPolynomial.eval₂Hom_C]
      rw [hrC]
      exact IsScalarTower.algebraMap_apply k (Polynomial k) K z
    · simp only [RingHom.comp_apply]
      rw [show idempotentLocalizationMap k Polynomial.X =
          (algebraMap C B) ((Ideal.Quotient.mk I)
            (MvPolynomial.X (0 : Fin 2))) by
            simp [idempotentLocalizationMap,
              idempotentLocalizationCoefficientMap, C, B, I]]
      rw [IsLocalization.Away.lift_eq]
      change r (MvPolynomial.X (0 : Fin 2)) = _
      exact hr0
  have hinj : Function.Injective (algebraMap (Polynomial k) K) := by
    exact IsLocalization.injective K
      (powers_le_nonZeroDivisors_of_noZeroDivisors hsne)
  have hP : LiesOver (idempotentLocalizationMap k) (⊥ : PrimeSpectrum (Polynomial k)) P := by
    apply PrimeSpectrum.ext
    rw [PrimeSpectrum.comap_asIdeal]
    change Ideal.comap (idempotentLocalizationMap k) (RingHom.ker bmap) = ⊥
    apply le_antisymm
    · intro a ha
      change bmap (idempotentLocalizationMap k a) = 0 at ha
      have ha' : algebraMap (Polynomial k) K a = 0 := by
        rw [← hcomp]
        exact ha
      have ha'' : a = 0 := hinj (by simpa using ha')
      simpa using ha''
    · exact bot_le
  constructor
  · intro hgu
    rw [goingUpProperty_iff_primeSpectrum] at hgu
    let p' : PrimeSpectrum (Polynomial k) :=
      ⟨RingHom.ker (Polynomial.evalRingHom (1 : k)), RingHom.ker_isPrime _⟩
    obtain ⟨Q, hQover, hPQ⟩ :=
      hgu (p := (⊥ : PrimeSpectrum (Polynomial k))) (p' := p')
        (by simp) (P := P) hP
    have hx : (Polynomial.X - Polynomial.C 1 : Polynomial k) ∈ p'.asIdeal := by
      change (Polynomial.X - Polynomial.C 1) ∈
        RingHom.ker (Polynomial.evalRingHom (1 : k))
      simp
    have hQcomap : Ideal.comap (idempotentLocalizationMap k) Q.asIdeal =
        p'.asIdeal := by
      simpa only [PrimeSpectrum.comap_asIdeal] using
        congrArg PrimeSpectrum.asIdeal hQover
    have hxQ : idempotentLocalizationMap k
        (Polynomial.X - Polynomial.C 1) ∈ Q.asIdeal := by
      have hx' : (Polynomial.X - Polynomial.C 1) ∈
          Ideal.comap (idempotentLocalizationMap k) Q.asIdeal := by
        rw [hQcomap]
        exact hx
      exact hx'
    have hyP : (algebraMap C B)
        (Ideal.Quotient.mk I (MvPolynomial.X (1 : Fin 2))) - 1 ∈ P.asIdeal := by
      change bmap ((algebraMap C B)
        (Ideal.Quotient.mk I (MvPolynomial.X (1 : Fin 2))) - 1) = 0
      rw [map_sub]
      simp only [map_one]
      rw [IsLocalization.Away.lift_eq]
      change r (MvPolynomial.X (1 : Fin 2)) - 1 = 0
      rw [hr1]
      simp
    have hyQ : (algebraMap C B)
        (Ideal.Quotient.mk I (MvPolynomial.X (1 : Fin 2))) - 1 ∈ Q.asIdeal :=
      hPQ hyP
    have hxQ' : (algebraMap C B)
        (Ideal.Quotient.mk I (MvPolynomial.X (0 : Fin 2))) - 1 ∈ Q.asIdeal := by
      simpa [idempotentLocalizationMap] using hxQ
    have hsQ : (algebraMap C B) s ∈ Q.asIdeal := by
      have hmul := Q.asIdeal.mul_mem_right
        ((algebraMap C B) (Ideal.Quotient.mk I
          (MvPolynomial.X (0 : Fin 2)))) hyQ
      have hadd := Q.asIdeal.add_mem hxQ' hmul
      change (algebraMap C B) (Ideal.Quotient.mk I
          (MvPolynomial.X (0 : Fin 2) * MvPolynomial.X (1 : Fin 2) - 1)) ∈
        Q.asIdeal
      simp only [map_sub, map_mul, map_one, map_add, map_neg]
      convert hadd using 1 <;> ring
    have hone := Q.asIdeal.mul_mem_right (IsLocalization.Away.invSelf s) hsQ
    rw [IsLocalization.Away.mul_invSelf] at hone
    exact Q.2.one_notMem hone
  · let aToR : A →+* R₂ :=
      Polynomial.eval₂RingHom (MvPolynomial.C : k →+* R₂)
        (MvPolynomial.X (0 : Fin 2))
    let _ : Algebra A R₂ := aToR.toAlgebra
    let aToC : A →+* C := (Ideal.Quotient.mk I).comp aToR
    let _ : Algebra A C := aToC.toAlgebra
    let f : Polynomial A := Polynomial.X ^ 2 - Polynomial.X
    let D := AdjoinRoot f
    let rootC : C := Ideal.Quotient.mk I (MvPolynomial.X (1 : Fin 2))
    have hroot : f.eval₂ (algebraMap A C) rootC = 0 := by
      simp [f, Polynomial.eval₂_sub, Polynomial.eval₂_pow]
      change (Ideal.Quotient.mk I)
        (MvPolynomial.X (1 : Fin 2) ^ 2 - MvPolynomial.X (1 : Fin 2)) = 0
      rw [Ideal.Quotient.eq_zero_iff_mem]
      exact Ideal.subset_span (by simp [I])
    let e : D →ₐ[A] C :=
      AdjoinRoot.liftAlgHom f (Algebra.ofId A C) rootC hroot
    let q : R₂ →+* D :=
      MvPolynomial.eval₂Hom
        ((AdjoinRoot.of f).comp (Polynomial.C : k →+* A))
        (fun i : Fin 2 => if i = 0 then
          AdjoinRoot.of f Polynomial.X else AdjoinRoot.root f)
    have hq : I ≤ RingHom.ker q := by
      apply Ideal.span_le.2
      rintro z (rfl : z = _)
      change q (MvPolynomial.X (1 : Fin 2) ^ 2 - MvPolynomial.X (1 : Fin 2)) = 0
      rw [map_sub, map_pow]
      have hq1 : q (MvPolynomial.X (1 : Fin 2)) = AdjoinRoot.root f := by
        change MvPolynomial.eval₂Hom
          ((AdjoinRoot.of f).comp (Polynomial.C : k →+* A))
          (fun i : Fin 2 => if i = 0 then
            AdjoinRoot.of f Polynomial.X else AdjoinRoot.root f)
          (MvPolynomial.X (1 : Fin 2)) = _
        rw [MvPolynomial.eval₂Hom_X']
        simp
      rw [hq1]
      simpa [f] using (AdjoinRoot.eval₂_root f)
    let gRing : C →+* D := Ideal.Quotient.lift I q hq
    have hqC : ∀ z : k, q (MvPolynomial.C z) = AdjoinRoot.of f (Polynomial.C z) := by
      intro z
      change MvPolynomial.eval₂Hom
        ((AdjoinRoot.of f).comp (Polynomial.C : k →+* A))
        (fun i : Fin 2 => if i = 0 then
          AdjoinRoot.of f Polynomial.X else AdjoinRoot.root f)
        (MvPolynomial.C z) = _
      rw [MvPolynomial.eval₂Hom_C]
      rfl
    have hqX : q (MvPolynomial.X (0 : Fin 2)) = AdjoinRoot.of f Polynomial.X := by
      change MvPolynomial.eval₂Hom
        ((AdjoinRoot.of f).comp (Polynomial.C : k →+* A))
        (fun i : Fin 2 => if i = 0 then
          AdjoinRoot.of f Polynomial.X else AdjoinRoot.root f)
        (MvPolynomial.X (0 : Fin 2)) = _
      rw [MvPolynomial.eval₂Hom_X']
      simp
    have hqY : q (MvPolynomial.X (1 : Fin 2)) = AdjoinRoot.root f := by
      change MvPolynomial.eval₂Hom
        ((AdjoinRoot.of f).comp (Polynomial.C : k →+* A))
        (fun i : Fin 2 => if i = 0 then
          AdjoinRoot.of f Polynomial.X else AdjoinRoot.root f)
        (MvPolynomial.X (1 : Fin 2)) = _
      rw [MvPolynomial.eval₂Hom_X']
      simp
    have haC : ∀ z : k, aToR (Polynomial.C z) = MvPolynomial.C z := by
      intro z
      change Polynomial.eval₂ (MvPolynomial.C : k →+* R₂)
        (MvPolynomial.X (0 : Fin 2)) (Polynomial.C z) = _
      rw [Polynomial.eval₂_C]
    have haX : aToR Polynomial.X = MvPolynomial.X (0 : Fin 2) := by
      change Polynomial.eval₂ (MvPolynomial.C : k →+* R₂)
        (MvPolynomial.X (0 : Fin 2)) Polynomial.X = _
      rw [Polynomial.eval₂_X]
    have hcompA : gRing.comp aToC = AdjoinRoot.of f := by
      apply Polynomial.ringHom_ext'
      · ext z
        change q (aToR (Polynomial.C z)) = AdjoinRoot.of f (Polynomial.C z)
        rw [haC z, hqC z]
      · change q (aToR Polynomial.X) = AdjoinRoot.of f Polynomial.X
        rw [haX, hqX]
    let g : C →ₐ[A] D :=
      { gRing with
        commutes' := by
          intro a
          change gRing (aToC a) = AdjoinRoot.of f a
          exact congrArg (fun h => h a) hcompA }
    have heof : ∀ a : A, e (AdjoinRoot.of f a) = aToC a := by
      intro a
      exact AdjoinRoot.liftAlgHom_of f (Algebra.ofId A C) rootC hroot a
    have heroot : e (AdjoinRoot.root f) = rootC := by
      exact AdjoinRoot.liftAlgHom_root f (Algebra.ofId A C) rootC hroot
    have heg : e.comp g = AlgHom.id A C := by
      apply Ideal.Quotient.algHom_ext A
      apply AlgHom.coe_ringHom_injective
      apply MvPolynomial.ringHom_ext'
      · ext z
        change e (gRing ((Ideal.Quotient.mk I) (MvPolynomial.C z))) =
          (Ideal.Quotient.mk I) (MvPolynomial.C z)
        change e (q (MvPolynomial.C z)) = _
        rw [hqC z]
        rw [heof]
        change (Ideal.Quotient.mk I) (aToR (Polynomial.C z)) = _
        rw [haC z]
      · intro z
        fin_cases z
        · change e (gRing ((Ideal.Quotient.mk I)
              (MvPolynomial.X (0 : Fin 2)))) =
            (Ideal.Quotient.mk I) (MvPolynomial.X (0 : Fin 2))
          change e (q (MvPolynomial.X (0 : Fin 2))) = _
          rw [hqX]
          rw [heof]
          change (Ideal.Quotient.mk I) (aToR Polynomial.X) = _
          rw [haX]
        · change e (gRing ((Ideal.Quotient.mk I)
              (MvPolynomial.X (1 : Fin 2)))) =
            (Ideal.Quotient.mk I) (MvPolynomial.X (1 : Fin 2))
          change e (q (MvPolynomial.X (1 : Fin 2))) = _
          rw [hqY, heroot]
    have hgroot : g (rootC) = AdjoinRoot.root f := by
      change gRing ((Ideal.Quotient.mk I) (MvPolynomial.X (1 : Fin 2))) = _
      change q (MvPolynomial.X (1 : Fin 2)) = _
      exact hqY
    have hge : g.comp e = AlgHom.id A D := by
      apply AdjoinRoot.algHom_ext
      change g (e (AdjoinRoot.root f)) = AdjoinRoot.root f
      rw [heroot]
      exact hgroot
    let ee : D ≃ₐ[A] C := AlgEquiv.ofAlgHom e g heg hge
    have hmonic0 :
        (Polynomial.X ^ 2 - Polynomial.X : Polynomial A).Monic := by
      apply Polynomial.monic_X_pow_sub
      rw [Polynomial.degree_X]
      norm_num
    have hmonic : f.Monic := by
      simpa [f] using hmonic0
    let _ : Module.Free A D := hmonic.free_adjoinRoot
    have hflatC : RingHom.Flat aToC := by
      change RingHom.Flat (algebraMap A C)
      rw [RingHom.flat_algebraMap_iff]
      exact Module.Flat.of_linearEquiv ee.toLinearEquiv.symm
    let aToB : A →+* B := (algebraMap C B).comp aToC
    have hflatB : RingHom.Flat (algebraMap C B) := by
      change RingHom.Flat (algebraMap C (Localization.Away s))
      rw [RingHom.flat_algebraMap_iff]
      exact IsLocalization.flat B (Submonoid.powers s)
    have hflatAB : RingHom.Flat aToB :=
      RingHom.Flat.comp hflatC hflatB
    have hmap : idempotentLocalizationMap k = aToB := by
      apply Polynomial.ringHom_ext'
      · ext z
        simp [idempotentLocalizationMap,
          idempotentLocalizationCoefficientMap, aToB, aToC, aToR,
          R₂, C, B, I]
      · simp [idempotentLocalizationMap,
          idempotentLocalizationCoefficientMap, aToB, aToC, aToR,
          R₂, C, B, I]
    rw [hmap]
    change @Algebra.HasGoingDown A B _ _ aToB.toAlgebra
    let _ : Algebra A B := aToB.toAlgebra
    let _ : Module A B := Algebra.toModule
    have _ : Module.Flat A B := by
      rw [← RingHom.flat_algebraMap_iff]
      exact hflatAB
    exact Algebra.HasGoingDown.of_flat

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
  classical
  ext p
  constructor
  · rintro ⟨P, rfl⟩
    simp only [reciprocalImageAnswer, Set.mem_union, PrimeSpectrum.mem_basicOpen,
      PrimeSpectrum.mem_zeroLocus]
    by_contra h
    push_neg at h
    rcases h with ⟨hxneg, hsubneg⟩
    have hx : MvPolynomial.X (0 : Fin 2) ∈
        (PrimeSpectrum.comap (reciprocalImageMap k) P).asIdeal := by
      change ¬ (MvPolynomial.X (0 : Fin 2) ∉
        (PrimeSpectrum.comap (reciprocalImageMap k) P).asIdeal) at hxneg
      exact not_not.mp hxneg
    have hxP : reciprocalImageMap k (MvPolynomial.X (0 : Fin 2)) ∈ P.asIdeal := hx
    have hyP : reciprocalImageMap k (MvPolynomial.X (1 : Fin 2)) ∈ P.asIdeal := by
      simpa [reciprocalImageMap] using
        P.asIdeal.mul_mem_right (MvPolynomial.X (1 : Fin 2)) hxP
    have hy : MvPolynomial.X (1 : Fin 2) ∈
        (PrimeSpectrum.comap (reciprocalImageMap k) P).asIdeal := hyP
    apply hsubneg
    intro z hz
    rcases Set.mem_insert_iff.mp hz with rfl | hz
    · exact hx
    · rcases Set.mem_singleton_iff.mp hz with rfl
      exact hy
  · simp only [reciprocalImageAnswer, Set.mem_union, PrimeSpectrum.mem_basicOpen,
      PrimeSpectrum.mem_zeroLocus]
    intro hp
    rcases hp with hp | hp
    · let S := Localization.Away (MvPolynomial.X (R := k) (0 : Fin 2))
      let q : Formalization.Books.Exercises.Unit16.polynomialRing k 2 →+* S :=
        MvPolynomial.eval₂Hom (algebraMap k S)
          (fun i : Fin 2 => if i = 0 then
              algebraMap (Formalization.Books.Exercises.Unit16.polynomialRing k 2) S
                (MvPolynomial.X (0 : Fin 2))
            else
              algebraMap (Formalization.Books.Exercises.Unit16.polynomialRing k 2) S
                (MvPolynomial.X (1 : Fin 2)) *
                IsLocalization.Away.invSelf (MvPolynomial.X (R := k) (0 : Fin 2)))
      have hcomp : q.comp (reciprocalImageMap k) = algebraMap _ S := by
        ext z
        · simp [q, reciprocalImageMap]
          exact (IsScalarTower.algebraMap_apply k
            (Formalization.Books.Exercises.Unit16.polynomialRing k 2) S z).symm
        · fin_cases z
          · simp [q, reciprocalImageMap]
          · simp [q, reciprocalImageMap]
            calc
              (algebraMap (Formalization.Books.Exercises.Unit16.polynomialRing k 2) S
                  (MvPolynomial.X (0 : Fin 2))) *
                  ((algebraMap (Formalization.Books.Exercises.Unit16.polynomialRing k 2) S
                    (MvPolynomial.X (1 : Fin 2))) *
                  IsLocalization.Away.invSelf (MvPolynomial.X (R := k) (0 : Fin 2))) =
                (algebraMap (Formalization.Books.Exercises.Unit16.polynomialRing k 2) S
                  (MvPolynomial.X (1 : Fin 2))) *
                  ((algebraMap (Formalization.Books.Exercises.Unit16.polynomialRing k 2) S
                    (MvPolynomial.X (0 : Fin 2))) *
                    IsLocalization.Away.invSelf (MvPolynomial.X (R := k) (0 : Fin 2))) := by ring
              _ = (algebraMap (Formalization.Books.Exercises.Unit16.polynomialRing k 2) S
                  (MvPolynomial.X (1 : Fin 2))) * 1 := by
                rw [IsLocalization.Away.mul_invSelf]
              _ = (algebraMap (Formalization.Books.Exercises.Unit16.polynomialRing k 2) S
                  (MvPolynomial.X (1 : Fin 2))) := by simp
      have hp' : p ∈ (PrimeSpectrum.basicOpen
          (MvPolynomial.X (R := k) (0 : Fin 2)) :
          Set (PrimeSpectrum (Formalization.Books.Exercises.Unit16.polynomialRing k 2))) := hp
      rw [← PrimeSpectrum.localization_away_comap_range S
        (MvPolynomial.X (R := k) (0 : Fin 2))] at hp'
      obtain ⟨P, hP⟩ := hp'
      refine ⟨PrimeSpectrum.comap q P, ?_⟩
      apply PrimeSpectrum.ext
      change Ideal.comap (reciprocalImageMap k)
          (Ideal.comap q P.asIdeal) = p.asIdeal
      rw [Ideal.comap_comap, hcomp]
      exact congrArg PrimeSpectrum.asIdeal hP
    · have hx : MvPolynomial.X (0 : Fin 2) ∈ p.asIdeal := hp (by simp)
      have hy : MvPolynomial.X (1 : Fin 2) ∈ p.asIdeal := hp (by simp)
      let q : Formalization.Books.Exercises.Unit16.polynomialRing k 2 →+*
          (Formalization.Books.Exercises.Unit16.polynomialRing k 2 ⧸ p.asIdeal) :=
        Ideal.Quotient.mk p.asIdeal
      have hq : q.comp (reciprocalImageMap k) = q := by
        have hyq : q (MvPolynomial.X (1 : Fin 2)) = 0 := by
          change Ideal.Quotient.mk p.asIdeal (MvPolynomial.X (1 : Fin 2)) = 0
          rw [Ideal.Quotient.eq_zero_iff_mem]
          exact hy
        ext z
        · simp [q, reciprocalImageMap]
        · fin_cases z
          · simp [q, reciprocalImageMap]
          · simp [q, reciprocalImageMap, hyq]
      refine ⟨p, ?_⟩
      apply PrimeSpectrum.ext
      rw [PrimeSpectrum.comap_asIdeal]
      apply le_antisymm
      · intro z hz
        change reciprocalImageMap k z ∈ p.asIdeal at hz
        have hz' : q (reciprocalImageMap k z) = 0 := by
          change Ideal.Quotient.mk p.asIdeal (reciprocalImageMap k z) = 0
          rw [Ideal.Quotient.eq_zero_iff_mem]
          exact hz
        have hqz := congrArg (fun r => r z) hq
        have hz'' : q z = 0 := by
          rw [← hqz]
          exact hz'
        change Ideal.Quotient.mk p.asIdeal z = 0 at hz''
        exact Ideal.Quotient.eq_zero_iff_mem.mp hz''
      · intro z hz
        have hz' : q z = 0 := by
          change Ideal.Quotient.mk p.asIdeal z = 0
          rw [Ideal.Quotient.eq_zero_iff_mem]
          exact hz
        have hqz := congrArg (fun r => r z) hq
        have hz'' : q (reciprocalImageMap k z) = 0 := by
          change (q.comp (reciprocalImageMap k)) z = 0
          rw [hqz]
          exact hz'
        change Ideal.Quotient.mk p.asIdeal (reciprocalImageMap k z) = 0 at hz''
        rw [Ideal.Quotient.eq_zero_iff_mem] at hz''
        exact hz''
/-- Image computation (2): `Spec(k[x,y,a,b]/(ax-by-1)) → Spec(k[x,y])`. -/
theorem exercise_images_case_two (k : Type u) [Field k] [IsAlgClosed k] :
    Set.range (PrimeSpectrum.comap (unitEquationMap k)) =
      unitEquationImageAnswer k := by
  classical
  ext p
  constructor
  · rintro ⟨P, rfl⟩
    simp only [unitEquationImageAnswer, Set.mem_union, PrimeSpectrum.mem_basicOpen]
    by_contra h
    push_neg at h
    rcases h with ⟨hxneg, hyneg⟩
    have hx0 : MvPolynomial.X (0 : Fin 2) ∈
        (PrimeSpectrum.comap (unitEquationMap k) P).asIdeal := by
      change ¬ (MvPolynomial.X (0 : Fin 2) ∉
        (PrimeSpectrum.comap (unitEquationMap k) P).asIdeal) at hxneg
      exact not_not.mp hxneg
    have hy0 : MvPolynomial.X (1 : Fin 2) ∈
        (PrimeSpectrum.comap (unitEquationMap k) P).asIdeal := by
      change ¬ (MvPolynomial.X (1 : Fin 2) ∉
        (PrimeSpectrum.comap (unitEquationMap k) P).asIdeal) at hyneg
      exact not_not.mp hyneg
    have hx : Ideal.Quotient.mk (unitEquationIdeal k)
        (MvPolynomial.X (0 : Fin 4)) ∈ P.asIdeal := by
      change unitEquationMap k (MvPolynomial.X (0 : Fin 2)) ∈ P.asIdeal at hx0
      simpa [unitEquationMap] using hx0
    have hy : Ideal.Quotient.mk (unitEquationIdeal k)
        (MvPolynomial.X (1 : Fin 4)) ∈ P.asIdeal := by
      change unitEquationMap k (MvPolynomial.X (1 : Fin 2)) ∈ P.asIdeal at hy0
      simpa [unitEquationMap] using hy0
    have hxa : Ideal.Quotient.mk (unitEquationIdeal k)
          (MvPolynomial.X (0 : Fin 4)) *
        Ideal.Quotient.mk (unitEquationIdeal k) (MvPolynomial.X (2 : Fin 4)) ∈
          P.asIdeal := by
      exact P.asIdeal.mul_mem_right _ hx
    have hyb : Ideal.Quotient.mk (unitEquationIdeal k)
          (MvPolynomial.X (1 : Fin 4)) *
        Ideal.Quotient.mk (unitEquationIdeal k) (MvPolynomial.X (3 : Fin 4)) ∈
          P.asIdeal := by
      exact P.asIdeal.mul_mem_right _ hy
    have hrel : Ideal.Quotient.mk (unitEquationIdeal k)
          (MvPolynomial.X (0 : Fin 4) * MvPolynomial.X (2 : Fin 4) -
            MvPolynomial.X (1 : Fin 4) * MvPolynomial.X (3 : Fin 4) - 1) ∈ P.asIdeal := by
      rw [show Ideal.Quotient.mk (unitEquationIdeal k)
          (MvPolynomial.X (0 : Fin 4) * MvPolynomial.X (2 : Fin 4) -
            MvPolynomial.X (1 : Fin 4) * MvPolynomial.X (3 : Fin 4) - 1) = 0 by
        rw [Ideal.Quotient.eq_zero_iff_mem]
        exact Ideal.subset_span (by simp)]
      exact P.asIdeal.zero_mem
    have hone : (1 : unitEquationRing k) ∈ P.asIdeal := by
      have hsub : Ideal.Quotient.mk (unitEquationIdeal k)
            (MvPolynomial.X (0 : Fin 4) * MvPolynomial.X (2 : Fin 4)) -
          Ideal.Quotient.mk (unitEquationIdeal k)
            (MvPolynomial.X (1 : Fin 4) * MvPolynomial.X (3 : Fin 4)) ∈
          P.asIdeal := by
        rw [map_mul, map_mul]
        exact P.asIdeal.sub_mem hxa hyb
      have := P.asIdeal.sub_mem hsub hrel
      have heq :
          (Ideal.Quotient.mk (unitEquationIdeal k)) (MvPolynomial.X (0 : Fin 4)) *
              Ideal.Quotient.mk (unitEquationIdeal k) (MvPolynomial.X (2 : Fin 4)) -
            Ideal.Quotient.mk (unitEquationIdeal k) (MvPolynomial.X (1 : Fin 4)) *
              Ideal.Quotient.mk (unitEquationIdeal k) (MvPolynomial.X (3 : Fin 4)) -
            Ideal.Quotient.mk (unitEquationIdeal k)
              (MvPolynomial.X (0 : Fin 4) * MvPolynomial.X (2 : Fin 4) -
                MvPolynomial.X (1 : Fin 4) * MvPolynomial.X (3 : Fin 4) - 1) = 1 := by
        rw [map_sub, map_sub, map_mul, map_mul, map_one]
        ring
      have this' :
          (Ideal.Quotient.mk (unitEquationIdeal k)) (MvPolynomial.X (0 : Fin 4)) *
              Ideal.Quotient.mk (unitEquationIdeal k) (MvPolynomial.X (2 : Fin 4)) -
            Ideal.Quotient.mk (unitEquationIdeal k) (MvPolynomial.X (1 : Fin 4)) *
              Ideal.Quotient.mk (unitEquationIdeal k) (MvPolynomial.X (3 : Fin 4)) -
            (Ideal.Quotient.mk (unitEquationIdeal k))
              (MvPolynomial.X (0 : Fin 4) * MvPolynomial.X (2 : Fin 4) -
                MvPolynomial.X (1 : Fin 4) * MvPolynomial.X (3 : Fin 4) - 1) ∈ P.asIdeal := by
        convert this using 1 <;> simp only [map_sub, map_mul, map_one]
      rw [heq] at this'
      exact this'
    exact P.2.one_notMem hone
  · simp only [unitEquationImageAnswer, Set.mem_union, PrimeSpectrum.mem_basicOpen]
    intro hp
    rcases hp with hp | hp
    · let S := Localization.Away (MvPolynomial.X (R := k) (0 : Fin 2))
      let sourceToS : Formalization.Books.Exercises.Unit16.polynomialRing k 2 →+* S :=
        algebraMap _ S
      let q : Formalization.Books.Exercises.Unit16.polynomialRing k 4 →+* S :=
        MvPolynomial.eval₂Hom (algebraMap k S)
          (fun i : Fin 4 => if i = 0 then sourceToS (MvPolynomial.X 0)
            else if i = 1 then sourceToS (MvPolynomial.X 1)
            else if i = 2 then IsLocalization.Away.invSelf
              (MvPolynomial.X (R := k)
                (0 : Fin 2))
            else 0)
      have hq : unitEquationIdeal k ≤ RingHom.ker q := by
        apply Ideal.span_le.2
        rintro z (rfl : z = _)
        change q (MvPolynomial.X (0 : Fin 4) * MvPolynomial.X (2 : Fin 4) -
          MvPolynomial.X (1 : Fin 4) * MvPolynomial.X (3 : Fin 4) - 1) = 0
        rw [map_sub, map_sub, map_mul, map_mul, map_one]
        simp only [q, MvPolynomial.eval₂Hom_X', if_pos, if_neg, map_one]
        simp only [if_neg (by decide : (2 : Fin 4) ≠ 0),
          if_neg (by decide : (2 : Fin 4) ≠ 1),
          if_neg (by decide : (3 : Fin 4) ≠ 0),
          if_neg (by decide : (3 : Fin 4) ≠ 1),
          if_neg (by decide : (3 : Fin 4) ≠ 2),
          if_neg (by decide : (1 : Fin 4) ≠ 0), mul_zero, sub_zero]
        change sourceToS (MvPolynomial.X (0 : Fin 2)) *
            IsLocalization.Away.invSelf (MvPolynomial.X (R := k) (0 : Fin 2)) - 1 = 0
        rw [show sourceToS (MvPolynomial.X (0 : Fin 2)) =
            algebraMap (Formalization.Books.Exercises.Unit16.polynomialRing k 2) S
              (MvPolynomial.X (0 : Fin 2)) by rfl,
          IsLocalization.Away.mul_invSelf]
        simp
      let h : unitEquationRing k →+* S :=
        Ideal.Quotient.lift (unitEquationIdeal k) q hq
      have hcomp : h.comp (unitEquationMap k) = sourceToS := by
        ext z
        · simp [h, unitEquationMap, sourceToS, q]
          exact (IsScalarTower.algebraMap_apply k
            (Formalization.Books.Exercises.Unit16.polynomialRing k 2) S z).symm
        · fin_cases z <;>
            simp [h, unitEquationMap, sourceToS, q]
      have hp' : p ∈ (PrimeSpectrum.basicOpen
          (MvPolynomial.X (R := k) (0 : Fin 2)) :
          Set (PrimeSpectrum (Formalization.Books.Exercises.Unit16.polynomialRing k 2))) := hp
      rw [← PrimeSpectrum.localization_away_comap_range S
        (MvPolynomial.X (R := k) (0 : Fin 2))] at hp'
      obtain ⟨P, hP⟩ := hp'
      refine ⟨PrimeSpectrum.comap h P, ?_⟩
      apply PrimeSpectrum.ext
      change Ideal.comap (unitEquationMap k)
          (Ideal.comap h P.asIdeal) = p.asIdeal
      rw [Ideal.comap_comap, hcomp]
      exact congrArg PrimeSpectrum.asIdeal hP
    · let S := Localization.Away (MvPolynomial.X (R := k) (1 : Fin 2))
      let sourceToS : Formalization.Books.Exercises.Unit16.polynomialRing k 2 →+* S :=
        algebraMap _ S
      let q : Formalization.Books.Exercises.Unit16.polynomialRing k 4 →+* S :=
        MvPolynomial.eval₂Hom (algebraMap k S)
          (fun i : Fin 4 => if i = 0 then sourceToS (MvPolynomial.X 0)
            else if i = 1 then sourceToS (MvPolynomial.X 1)
            else if i = 2 then 0
            else -(IsLocalization.Away.invSelf
              (MvPolynomial.X (R := k)
                (1 : Fin 2))))
      have hq : unitEquationIdeal k ≤ RingHom.ker q := by
        apply Ideal.span_le.2
        rintro z (rfl : z = _)
        change q (MvPolynomial.X (0 : Fin 4) * MvPolynomial.X (2 : Fin 4) -
          MvPolynomial.X (1 : Fin 4) * MvPolynomial.X (3 : Fin 4) - 1) = 0
        rw [map_sub, map_sub, map_mul, map_mul, map_one]
        simp only [q, MvPolynomial.eval₂Hom_X', if_pos, if_neg, map_one]
        simp only [if_neg (by decide : (2 : Fin 4) ≠ 0),
          if_neg (by decide : (2 : Fin 4) ≠ 1),
          if_neg (by decide : (3 : Fin 4) ≠ 0),
          if_neg (by decide : (3 : Fin 4) ≠ 1),
          if_neg (by decide : (3 : Fin 4) ≠ 2),
          if_neg (by decide : (1 : Fin 4) ≠ 0), zero_mul, mul_zero]
        rw [mul_neg,
          show sourceToS (MvPolynomial.X (1 : Fin 2)) =
            algebraMap (Formalization.Books.Exercises.Unit16.polynomialRing k 2) S
              (MvPolynomial.X (1 : Fin 2)) by rfl,
          IsLocalization.Away.mul_invSelf]
        ring
      let h : unitEquationRing k →+* S :=
        Ideal.Quotient.lift (unitEquationIdeal k) q hq
      have hcomp : h.comp (unitEquationMap k) = sourceToS := by
        ext z
        · simp [h, unitEquationMap, sourceToS, q]
          exact (IsScalarTower.algebraMap_apply k
            (Formalization.Books.Exercises.Unit16.polynomialRing k 2) S z).symm
        · fin_cases z <;>
            simp [h, unitEquationMap, sourceToS, q]
      have hp' : p ∈ (PrimeSpectrum.basicOpen
          (MvPolynomial.X (R := k) (1 : Fin 2)) :
          Set (PrimeSpectrum (Formalization.Books.Exercises.Unit16.polynomialRing k 2))) := hp
      rw [← PrimeSpectrum.localization_away_comap_range S
        (MvPolynomial.X (R := k) (1 : Fin 2))] at hp'
      obtain ⟨P, hP⟩ := hp'
      refine ⟨PrimeSpectrum.comap h P, ?_⟩
      apply PrimeSpectrum.ext
      change Ideal.comap (unitEquationMap k)
          (Ideal.comap h P.asIdeal) = p.asIdeal
      rw [Ideal.comap_comap, hcomp]
      exact congrArg PrimeSpectrum.asIdeal hP

/-- Image computation (3): the localized cusp parameterization. -/
theorem exercise_images_case_three (k : Type u) [Field k] [IsAlgClosed k] :
    Set.range (PrimeSpectrum.comap (cuspParameterMap k)) =
      cuspImageAnswer k := by
  classical
  let R₂ := Formalization.Books.Exercises.Unit16.polynomialRing k 2
  let B := cuspParameterRing k
  let x₀ : R₂ := MvPolynomial.X (0 : Fin 2)
  let x₁ : R₂ := MvPolynomial.X (1 : Fin 2)
  let d : Polynomial k := cuspParameterPolynomial k
  let α : Fin 2 → k := fun _ => 0
  ext p
  constructor
  · rintro ⟨P, rfl⟩
    simp only [cuspImageAnswer, Set.mem_diff, PrimeSpectrum.mem_zeroLocus]
    constructor
    · intro z hz
      rcases Set.mem_singleton_iff.mp hz with rfl
      have hzero : cuspParameterMap k (cuspEquation k) = 0 := by
        simp [cuspParameterMap, cuspEquation]
        ring
      change cuspParameterMap k (cuspEquation k) ∈ P.asIdeal
      rw [hzero]
      exact P.asIdeal.zero_mem
    · intro h
      have hx : cuspParameterMap k (x₀ - 1) ∈ P.asIdeal := h (by simp [x₀])
      have hy : cuspParameterMap k (x₁ - 1) ∈ P.asIdeal := h (by simp [x₁])
      have hx' :
          (algebraMap (Polynomial k) B Polynomial.X) ^ 2 - 1 ∈ P.asIdeal := by
        rw [map_sub] at hx
        simpa [x₀, cuspParameterMap, cuspParameterCoefficientMap, B] using hx
      have hy' :
          (algebraMap (Polynomial k) B Polynomial.X) ^ 3 - 1 ∈ P.asIdeal := by
        rw [map_sub] at hy
        simpa [x₁, cuspParameterMap, cuspParameterCoefficientMap, B] using hy
      have hmul :
          (algebraMap (Polynomial k) B Polynomial.X) *
              ((algebraMap (Polynomial k) B Polynomial.X) ^ 2 - 1) ∈
            P.asIdeal :=
        P.asIdeal.mul_mem_left (algebraMap (Polynomial k) B Polynomial.X) hx'
      have ht : algebraMap (Polynomial k) B Polynomial.X - 1 ∈ P.asIdeal := by
        have hsub := P.asIdeal.sub_mem hy' hmul
        convert hsub using 1 <;> ring
      have hd : (algebraMap (Polynomial k) B) d ∈ P.asIdeal := by
        simpa [d, cuspParameterPolynomial] using ht
      have hone := P.asIdeal.mul_mem_right
        (IsLocalization.Away.invSelf d) hd
      rw [IsLocalization.Away.mul_invSelf] at hone
      exact P.2.one_notMem hone
  · simp only [cuspImageAnswer, Set.mem_diff, PrimeSpectrum.mem_zeroLocus]
    intro hp
    have heq : cuspEquation k ∈ p.asIdeal := hp.1 (by simp)
    have hnot : ¬ (x₀ - 1 ∈ p.asIdeal ∧ x₁ - 1 ∈ p.asIdeal) := by
      intro hboth
      apply hp.2
      intro z hz
      rcases Set.mem_insert_iff.mp hz with rfl | hz
      · exact hboth.1
      · rcases Set.mem_singleton_iff.mp hz with rfl
        exact hboth.2
    by_cases hx0 : x₀ ∈ p.asIdeal
    · have heq' : x₁ ^ 2 - x₀ ^ 3 ∈ p.asIdeal := by
        simpa [cuspEquation, x₀, x₁] using heq
      have hx03 : x₀ ^ 3 ∈ p.asIdeal :=
        p.asIdeal.pow_mem_of_mem hx0 3 (by norm_num)
      have hx1sq : x₁ ^ 2 ∈ p.asIdeal := by
        convert p.asIdeal.add_mem heq' hx03 using 1 <;> ring
      have hx1 : x₁ ∈ p.asIdeal := p.2.mem_of_pow_mem 2 hx1sq
      let J : Ideal R₂ := Ideal.span ({x₀, x₁} : Set R₂)
      have hJp : J ≤ p.asIdeal := by
        rw [Ideal.span_le]
        rintro z hz
        rcases Set.mem_insert_iff.mp hz with rfl | hz
        · exact hx0
        · rcases Set.mem_singleton_iff.mp hz with rfl
          exact hx1
      have hrep : ∀ f : R₂,
          f - MvPolynomial.C (MvPolynomial.aeval α f) ∈ J := by
        intro f
        induction f using MvPolynomial.induction_on with
        | C a => simp
        | add f g hf hg =>
            rw [map_add, MvPolynomial.C_add]
            convert J.add_mem hf hg using 1 <;> abel
        | mul_X f i hf =>
            have hgen' : MvPolynomial.X i - MvPolynomial.C (α i) ∈ J := by
              apply Ideal.subset_span
              fin_cases i <;> simp [J, x₀, x₁, α]
            have h₁ := J.mul_mem_left (MvPolynomial.X i) hf
            have h₂ := J.mul_mem_left
              (MvPolynomial.C (MvPolynomial.aeval α f)) hgen'
            convert J.add_mem h₁ h₂ using 1
            simp only [map_mul, MvPolynomial.aeval_X]
            ring
      let m₀ : Ideal R₂ := MvPolynomial.vanishingIdeal k ({α} : Set (Fin 2 → k))
      have hm₀J : m₀ ≤ J := by
        intro f hf
        have hfzero : MvPolynomial.aeval α f = 0 := by
          apply (MvPolynomial.mem_vanishingIdeal_singleton_iff α f).mp
          exact hf
        simpa [hfzero] using hrep f
      have hJm₀ : J ≤ m₀ := by
        rw [Ideal.span_le]
        rintro z hz
        rcases Set.mem_insert_iff.mp hz with rfl | hz
        · change x₀ ∈ MvPolynomial.vanishingIdeal k ({α} : Set (Fin 2 → k))
          exact (MvPolynomial.mem_vanishingIdeal_singleton_iff α x₀).2 (by
            simp [x₀, α])
        · rcases Set.mem_singleton_iff.mp hz with rfl
          change x₁ ∈ MvPolynomial.vanishingIdeal k ({α} : Set (Fin 2 → k))
          exact (MvPolynomial.mem_vanishingIdeal_singleton_iff α x₁).2 (by
            simp [x₁, α])
      have hm₀p : m₀ ≤ p.asIdeal := hm₀J.trans hJp
      have hp_eq : m₀ = p.asIdeal :=
        (inferInstance : m₀.IsMaximal).eq_of_le p.2.ne_top hm₀p
      let e : Polynomial k →+* k := Polynomial.evalRingHom 0
      have hunit : IsUnit (e d) := by
        rw [show e d = -1 by simp [e, d, cuspParameterPolynomial]]
        exact isUnit_iff_ne_zero.mpr (by simp)
      let bmap : B →+* k := IsLocalization.Away.lift d hunit
      let aeval₀ : R₂ →+* k := (MvPolynomial.aeval α).toRingHom
      let P : PrimeSpectrum B := ⟨RingHom.ker bmap, RingHom.ker_isPrime _⟩
      have hcomp : bmap.comp (cuspParameterMap k) = aeval₀ := by
        apply MvPolynomial.ringHom_ext'
        · ext z
          simp [bmap, cuspParameterMap, cuspParameterCoefficientMap, e, α, d, B,
            aeval₀]
        · intro i
          fin_cases i <;>
            simp [bmap, cuspParameterMap, cuspParameterCoefficientMap, e, α, d, B,
              aeval₀]
      refine ⟨P, ?_⟩
      apply PrimeSpectrum.ext
      change Ideal.comap (cuspParameterMap k) (RingHom.ker bmap) = p.asIdeal
      rw [← hp_eq]
      apply le_antisymm
      · intro f hf
        change (bmap.comp (cuspParameterMap k)) f = 0 at hf
        rw [hcomp] at hf
        exact (MvPolynomial.mem_vanishingIdeal_singleton_iff α f).2 hf
      · intro f hf
        change (bmap.comp (cuspParameterMap k)) f = 0
        rw [hcomp]
        exact (MvPolynomial.mem_vanishingIdeal_singleton_iff α f).1 hf
    · letI : p.asIdeal.IsPrime := p.2
      let Q := R₂ ⧸ p.asIdeal
      let F := FractionRing Q
      let mkP : R₂ →+* Q := Ideal.Quotient.mk p.asIdeal
      let q : R₂ →+* F := (algebraMap Q F).comp mkP
      let qx : F := q x₀
      let qy : F := q x₁
      have hqinj : Function.Injective (algebraMap Q F) :=
        IsFractionRing.injective Q F
      have hmkx : mkP x₀ ≠ 0 := by
        intro h
        apply hx0
        exact Ideal.Quotient.eq_zero_iff_mem.mp h
      have hqxne : qx ≠ 0 := by
        intro h
        apply hmkx
        apply hqinj
        simpa [q, qx] using h
      have hmkrel : mkP (cuspEquation k) = 0 := by
        rw [Ideal.Quotient.eq_zero_iff_mem]
        exact heq
      have hrel : qy ^ 2 = qx ^ 3 := by
        have hrel0 : q (cuspEquation k) = 0 := by
          change algebraMap Q F (mkP (cuspEquation k)) = 0
          rw [hmkrel]
          simp
        simpa [q, qx, qy, cuspEquation, x₀, x₁] using
          (sub_eq_zero.mp (show qy ^ 2 - qx ^ 3 = 0 by
            simpa [cuspEquation, x₀, x₁] using hrel0))
      let u : F := qy / qx
      have hu2 : u ^ 2 = qx := by
        dsimp [u]
        rw [div_pow]
        apply (div_eq_iff (pow_ne_zero 2 hqxne)).2
        convert hrel using 1 <;> ring
      have hu3 : u ^ 3 = qy := by
        calc
          u ^ 3 = u * u ^ 2 := by ring
          _ = (qy / qx) * qx := by rw [hu2]
          _ = qy := div_mul_cancel₀ qy hqxne
      let evalT : Polynomial k →+* F :=
        Polynomial.eval₂RingHom (algebraMap k F) u
      have hdn : evalT d ≠ 0 := by
        intro hd
        have hu1 : u = 1 := by
          apply sub_eq_zero.mp
          simpa [evalT, d, cuspParameterPolynomial] using hd
        have hqx1 : qx = 1 := by
          rw [← hu2, hu1]
          simp
        have hqy1 : qy = 1 := by
          rw [← hu3, hu1]
          simp
        have hxm : x₀ - 1 ∈ p.asIdeal := by
          apply Ideal.Quotient.eq_zero_iff_mem.mp
          apply hqinj
          simpa [q] using (show q (x₀ - 1) = 0 by
            rw [map_sub, map_one]
            change qx - 1 = 0
            rw [hqx1]
            simp)
        have hym : x₁ - 1 ∈ p.asIdeal := by
          apply Ideal.Quotient.eq_zero_iff_mem.mp
          apply hqinj
          simpa [q] using (show q (x₁ - 1) = 0 by
            rw [map_sub, map_one]
            change qy - 1 = 0
            rw [hqy1]
            simp)
        exact hnot ⟨hxm, hym⟩
      have hunit : IsUnit (evalT d) := isUnit_iff_ne_zero.mpr hdn
      let bmap : B →+* F := IsLocalization.Away.lift d hunit
      have hqC : ∀ z : k, q (MvPolynomial.C z) = algebraMap k F z := by
        intro z
        change algebraMap Q F (mkP (MvPolynomial.C z)) = algebraMap k F z
        rw [show mkP (MvPolynomial.C z) = algebraMap k Q z by
          change (Ideal.Quotient.mk p.asIdeal) ((algebraMap k R₂) z) = _
          exact Ideal.Quotient.mk_algebraMap k p.asIdeal z]
        exact IsScalarTower.algebraMap_apply k Q F z
      have hcomp : bmap.comp (cuspParameterMap k) = q := by
        apply MvPolynomial.ringHom_ext'
        · ext z
          simp only [RingHom.comp_apply]
          simp only [cuspParameterMap, MvPolynomial.eval₂Hom_C]
          change bmap ((algebraMap (Polynomial k) B) (Polynomial.C z)) =
            q (MvPolynomial.C z)
          change (IsLocalization.Away.lift d hunit)
              ((algebraMap (Polynomial k) B) (Polynomial.C z)) =
            q (MvPolynomial.C z)
          rw [IsLocalization.Away.lift_eq]
          change evalT (Polynomial.C z) = q (MvPolynomial.C z)
          rw [hqC z]
          simp [evalT]
        · intro i
          fin_cases i
          ·
            change bmap (cuspParameterMap k x₀) = q x₀
            rw [show cuspParameterMap k x₀ =
              (algebraMap (Polynomial k) B) (Polynomial.X ^ 2) by
                simp [cuspParameterMap, x₀, B]]
            change (IsLocalization.Away.lift d hunit)
                ((algebraMap (Polynomial k) B) (Polynomial.X ^ 2)) = q x₀
            rw [IsLocalization.Away.lift_eq]
            change evalT (Polynomial.X ^ 2) = qx
            simpa [evalT] using hu2
          ·
            change bmap (cuspParameterMap k x₁) = q x₁
            rw [show cuspParameterMap k x₁ =
              (algebraMap (Polynomial k) B) (Polynomial.X ^ 3) by
                simp [cuspParameterMap, x₁, B]]
            change (IsLocalization.Away.lift d hunit)
                ((algebraMap (Polynomial k) B) (Polynomial.X ^ 3)) = q x₁
            rw [IsLocalization.Away.lift_eq]
            change evalT (Polynomial.X ^ 3) = qy
            simpa [evalT] using hu3
      let P : PrimeSpectrum B := ⟨RingHom.ker bmap, RingHom.ker_isPrime _⟩
      refine ⟨P, ?_⟩
      apply PrimeSpectrum.ext
      change Ideal.comap (cuspParameterMap k) (RingHom.ker bmap) = p.asIdeal
      apply le_antisymm
      · intro f hf
        change (bmap.comp (cuspParameterMap k)) f = 0 at hf
        rw [hcomp] at hf
        have hmk : mkP f = 0 := by
          apply hqinj
          simpa [q] using hf
        exact Ideal.Quotient.eq_zero_iff_mem.mp hmk
      · intro f hf
        change (bmap.comp (cuspParameterMap k)) f = 0
        rw [hcomp]
        change algebraMap Q F (mkP f) = 0
        rw [show mkP f = 0 by
          rw [Ideal.Quotient.eq_zero_iff_mem]
          exact hf]
        simp

/-- Image computation (4): the complex cubic curve mapped by squaring both
coordinates. -/
theorem exercise_images_case_four :
    Set.range (PrimeSpectrum.comap cubicSquareMap) = cubicImageAnswer := by
  sorry

end Formalization.Books.Exercises.Unit24

end
