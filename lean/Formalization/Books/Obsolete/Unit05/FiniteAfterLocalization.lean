import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.RingHom.Finite
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.RingTheory.FiniteType
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
import Mathlib.RingTheory.Localization.Integral
import Mathlib.RingTheory.Ideal.Quotient.Operations

namespace Formalization.Books.Obsolete.Unit05

universe u v w

noncomputable section

/-- The solid part of the localization diagram used in the finite-after-localization lemma.

 The two localization targets are represented by Mathlib's canonical `Localization.Away`
 constructions, and the map from `R_f` to `S_f` is Mathlib's canonical `Localization.awayMap`.
-/
structure FiniteAfterLocalizationDiagram
    (R : Type u) (S : Type v) (S' : Type w)
    [CommRing R] [CommRing S] [CommRing S'] (f : R) where
  rS : R →+* S
  rfS' : Localization.Away f →+* S'
  s'Sf : S' →+* Localization.Away (rS f)
  commute_lower : s'Sf.comp rfS' = Localization.awayMap rS f
  finite : RingHom.Finite rfS'

/-- A finite map over `R_f` extends to a finite `R`-algebra whose localization is `S'`. -/
theorem finite_after_localization
    {R : Type u} {S : Type v} {S' : Type w}
    [CommRing R] [CommRing S] [CommRing S']
    (f : R) (D : FiniteAfterLocalizationDiagram R S S' f) :
    ∃ (S'' : Type u) (hS'' : CommRing S''),
      letI : CommRing S'' := hS''
      ∃ (rS'' : R →+* S''),
        RingHom.Finite rS'' ∧
          ∃ (s''S : S'' →+* S) (s''S' : S'' →+* S'),
            s''S.comp rS'' = D.rS ∧
              s''S'.comp rS'' = D.rfS'.comp (algebraMap R (Localization.Away f)) ∧
                (algebraMap S (Localization.Away (D.rS f))).comp s''S =
                  D.s'Sf.comp s''S' ∧
                    (letI : Algebra S'' S' := s''S'.toAlgebra;
                IsLocalization.Away (rS'' f) S') := by
  classical
  let Rf := Localization.Away f
  let Sf := Localization.Away (D.rS f)
  let _ : Algebra R Rf := inferInstance
  let : Algebra Rf S' := D.rfS'.toAlgebra
  let : Algebra R S' := (D.rfS'.comp (algebraMap R Rf)).toAlgebra
  let : IsScalarTower R Rf S' := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let : Algebra R S := D.rS.toAlgebra
  let : Algebra S Sf := inferInstance
  let : Algebra R Sf := ((algebraMap S Sf).comp D.rS).toAlgebra
  have hft : Algebra.FiniteType Rf S' := D.finite.to_finiteType
  obtain ⟨n, φ, hφ⟩ := (Algebra.FiniteType.iff_quotient_mvPolynomial''
    (R := Rf) (S := S')).mp hft
  let x : Fin n → S' := fun i => φ (MvPolynomial.X i)
  have hx : ∀ i, IsIntegral Rf (x i) := fun i => D.finite.to_isIntegral (x i)
  have hclear : ∀ i, ∃ e : ℕ, IsIntegral R (algebraMap R S' (f ^ e) * x i) := by
    intro i
    obtain ⟨m, hm⟩ := IsIntegral.exists_multiple_integral_of_isLocalization
      (M := Submonoid.powers f) (x i) (hx i)
    obtain ⟨e, he⟩ := (Submonoid.mem_powers_iff (m : R) f).mp m.property
    exact ⟨e, by simpa [Submonoid.smul_def, Algebra.smul_def, he] using hm⟩
  choose e he using hclear
  let a : Fin n → S' := fun i => algebraMap R S' (f ^ e i) * x i
  have ha : ∀ i, IsIntegral R (a i) := fun i => he i
  have hbase : ∀ r : R,
      D.s'Sf (algebraMap R S' r) = algebraMap S Sf (D.rS r) := by
    intro r
    have h := congrArg (fun g => g (algebraMap R Rf r)) D.commute_lower
    have hmap : Localization.awayMap D.rS f (algebraMap R Rf r) =
        algebraMap S Sf (D.rS r) := by
      change IsLocalization.map Sf D.rS _ (algebraMap R Rf r) = _
      rw [IsLocalization.map_eq]
    rw [hmap] at h
    change D.s'Sf (D.rfS' (algebraMap R Rf r)) = algebraMap S Sf (D.rS r)
    exact h
  have hden : ∀ i, ∃ k : ℕ, ∃ s : S,
      algebraMap S Sf s = (algebraMap S Sf (D.rS f)) ^ k * D.s'Sf (a i) := by
    intro i
    obtain ⟨m, hm⟩ := IsLocalization.exists_integer_multiple
      (Submonoid.powers (D.rS f)) (D.s'Sf (a i))
    rcases hm with ⟨s, hs⟩
    obtain ⟨k, hk⟩ := (Submonoid.mem_powers_iff (m : S) (D.rS f)).mp m.property
    refine ⟨k, s, ?_⟩
    simpa [Algebra.smul_def, ← hk, map_pow] using hs
  choose k s hs using hden
  let b : Fin n → S' := fun i => algebraMap R S' (f ^ k i) * a i
  have hb : ∀ i, IsIntegral R (b i) := by
    intro i
    exact (isIntegral_algebraMap (R := R) (A := S')).mul (ha i)
  have hbs : ∀ i, algebraMap S Sf (s i) = D.s'Sf (b i) := by
    intro i
    rw [show D.s'Sf (b i) =
      algebraMap S Sf (D.rS (f ^ k i)) * D.s'Sf (a i) by
        simp only [b, map_mul, hbase]]
    simpa using (hs i)
  choose p hp hpa using hb
  let p₀ : Fin n → Polynomial R := fun i => Polynomial.X * p i
  have hp₀ : ∀ i, (p₀ i).Monic := fun i => Polynomial.monic_X.mul (hp i)
  have hpa₀ : ∀ i, Polynomial.aeval (b i) (p₀ i) = 0 := by
    intro i
    simp [p₀, Polynomial.aeval_def, hpa i]
  have hcomp : (algebraMap R Sf).comp (RingHom.id R) =
      D.s'Sf.comp (algebraMap R S') := by
    ext r
    exact (hbase r).symm
  have hrel : ∀ i, Polynomial.aeval (algebraMap S Sf (s i)) (p₀ i) = 0 := by
    intro i
    have hh := Polynomial.map_aeval_eq_aeval_map (R := R) (φ := RingHom.id R)
      (ψ := D.s'Sf) hcomp (p₀ i) (b i)
    have hh0 : D.s'Sf (Polynomial.aeval (b i) (p₀ i)) = 0 := by
      simpa [Polynomial.aeval_def] using congrArg D.s'Sf (hpa₀ i)
    have hh1 : Polynomial.aeval (D.s'Sf (b i)) (p₀ i) = 0 := by
      calc
        Polynomial.aeval (D.s'Sf (b i)) (p₀ i) =
            D.s'Sf (Polynomial.aeval (b i) (p₀ i)) := by simpa using hh.symm
        _ = 0 := hh0
    simpa [← hbs i] using hh1
  have hcompS : (algebraMap R Sf).comp (RingHom.id R) =
      (algebraMap S Sf).comp (algebraMap R S) := by
    ext r
    rfl
  have hkill : ∀ i, ∃ l : ℕ,
      (D.rS f) ^ l * Polynomial.aeval (s i) (p₀ i) = 0 := by
    intro i
    have heval : algebraMap S Sf (Polynomial.aeval (s i) (p₀ i)) =
        Polynomial.aeval (algebraMap S Sf (s i)) (p₀ i) := by
      simpa using Polynomial.map_aeval_eq_aeval_map (R := R) (φ := RingHom.id R)
        (ψ := algebraMap S Sf) hcompS (p₀ i) (s i)
    have hrel' : algebraMap S Sf (Polynomial.aeval (s i) (p₀ i)) =
        algebraMap S Sf 0 := by
      rw [heval, hrel i, map_zero]
    obtain ⟨l, hl⟩ := IsLocalization.Away.exists_of_eq (D.rS f) hrel'
    exact ⟨l, by simpa using hl⟩
  choose l hl using hkill
  let c : Fin n → S' := fun i => algebraMap R S' (f ^ l i) * b i
  let t : Fin n → S := fun i => D.rS (f ^ l i) * s i
  let q : Fin n → Polynomial R := fun i => (p₀ i).scaleRoots (f ^ l i)
  have hq : ∀ i, (q i).Monic := fun i =>
    (Polynomial.monic_scaleRoots_iff _).mpr (hp₀ i)
  have hqc : ∀ i, Polynomial.aeval (c i) (q i) = 0 := by
    intro i
    simpa [c, q] using (Polynomial.scaleRoots_aeval_eq_zero (p := p₀ i)
      (a := b i) (r := f ^ l i) (hpa₀ i))
  have hqt : ∀ i, Polynomial.aeval (t i) (q i) = 0 := by
    intro i
    rcases subsingleton_or_nontrivial R with hR | hR
    · let _ := hR
      have : Subsingleton S := D.rS.codomain_trivial
      exact Subsingleton.elim _ _
    · let _ := hR
      have hdeg : 1 ≤ (p₀ i).natDegree := by
        change 1 ≤ (Polynomial.X * p i).natDegree
        rw [Polynomial.monic_X.natDegree_mul' (hp i).ne_zero,
          Polynomial.natDegree_X]
        omega
      obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hdeg
      have hpow : (D.rS f) ^ (l i * (p₀ i).natDegree) *
          Polynomial.aeval (s i) (p₀ i) = 0 := by
        calc
          (D.rS f) ^ (l i * (p₀ i).natDegree) *
                Polynomial.aeval (s i) (p₀ i) =
              (D.rS f) ^ (l i * d) *
                ((D.rS f) ^ l i * Polynomial.aeval (s i) (p₀ i)) := by
                  simp [hd, Nat.mul_add, pow_add, mul_assoc, mul_comm, mul_left_comm]
          _ = 0 := by rw [hl i, mul_zero]
      change Polynomial.eval₂ (algebraMap R S) (algebraMap R S (f ^ l i) * s i)
        ((p₀ i).scaleRoots (f ^ l i)) = 0
      rw [Polynomial.scaleRoots_eval₂_mul (p := p₀ i) (f := algebraMap R S)
        (r := s i) (s := f ^ l i)]
      simpa [Polynomial.aeval_def, RingHom.algebraMap_toAlgebra, map_pow, ← pow_mul,
        ← hd, pow_add, mul_add, mul_assoc] using hpow
  let B := MvPolynomial (Fin n) R
  let rel : Fin n → B := fun i =>
    Polynomial.eval₂ (algebraMap R B) (MvPolynomial.X i) (q i)
  let I : Ideal B := Ideal.span (Set.range rel)
  let S'' := B ⧸ I
  let : CommRing S'' := Ideal.Quotient.commRing I
  let mk : B →ₐ[R] S'' := Ideal.Quotient.mkₐ R I
  let α₀ : B →+* S := MvPolynomial.eval₂Hom (algebraMap R S) t
  let β₀ : B →+* S' := MvPolynomial.eval₂Hom (algebraMap R S') c
  have hαrel : ∀ i, α₀ (rel i) = 0 := by
    intro i
    have hcompα : (algebraMap R S).comp (RingHom.id R) =
        α₀.comp (algebraMap R B) := by
      ext r
      change algebraMap R S r = α₀ (MvPolynomial.C r)
      change algebraMap R S r =
        MvPolynomial.eval₂ (algebraMap R S) t (MvPolynomial.C r)
      rw [MvPolynomial.eval₂_C]
    have hh := Polynomial.map_aeval_eq_aeval_map (R := R) (φ := RingHom.id R)
      (ψ := α₀) hcompα (q i) (MvPolynomial.X i)
    calc
      α₀ (rel i) = Polynomial.aeval (α₀ (MvPolynomial.X i)) (q i) := by
        simpa [rel, Polynomial.aeval_def] using hh
      _ = 0 := by
        have hX : α₀ (MvPolynomial.X i) = t i := by
          change MvPolynomial.eval₂ (algebraMap R S) t (MvPolynomial.X i) = t i
          simp
        rw [hX]
        exact hqt i
  have hβrel : ∀ i, β₀ (rel i) = 0 := by
    intro i
    have hcompβ : (algebraMap R S').comp (RingHom.id R) =
        β₀.comp (algebraMap R B) := by
      ext r
      change algebraMap R S' r = β₀ (MvPolynomial.C r)
      change algebraMap R S' r =
        MvPolynomial.eval₂ (algebraMap R S') c (MvPolynomial.C r)
      rw [MvPolynomial.eval₂_C]
    have hh := Polynomial.map_aeval_eq_aeval_map (R := R) (φ := RingHom.id R)
      (ψ := β₀) hcompβ (q i) (MvPolynomial.X i)
    calc
      β₀ (rel i) = Polynomial.aeval (β₀ (MvPolynomial.X i)) (q i) := by
        simpa [rel, Polynomial.aeval_def] using hh
      _ = 0 := by
        have hX : β₀ (MvPolynomial.X i) = c i := by
          change MvPolynomial.eval₂ (algebraMap R S') c (MvPolynomial.X i) = c i
          simp
        rw [hX]
        exact hqc i
  have hαI : I ≤ RingHom.ker α₀ := by
    change Ideal.span (Set.range rel) ≤ RingHom.ker α₀
    refine Ideal.span_le.2 ?_
    rintro _ ⟨i, rfl⟩
    exact RingHom.mem_ker.mpr (hαrel i)
  have hβI : I ≤ RingHom.ker β₀ := by
    change Ideal.span (Set.range rel) ≤ RingHom.ker β₀
    refine Ideal.span_le.2 ?_
    rintro _ ⟨i, rfl⟩
    exact RingHom.mem_ker.mpr (hβrel i)
  let α : S'' →+* S := Ideal.Quotient.lift I α₀
    (fun a ha => RingHom.mem_ker.mp (hαI ha))
  let β : S'' →+* S' := Ideal.Quotient.lift I β₀
    (fun a ha => RingHom.mem_ker.mp (hβI ha))
  have hαmk : α.comp mk.toRingHom = α₀ := by
    change (Ideal.Quotient.lift I α₀ _).comp (Ideal.Quotient.mk I) = α₀
    exact Ideal.Quotient.lift_comp_mk I α₀ _
  have hβmk : β.comp mk.toRingHom = β₀ := by
    change (Ideal.Quotient.lift I β₀ _).comp (Ideal.Quotient.mk I) = β₀
    exact Ideal.Quotient.lift_comp_mk I β₀ _
  have hvar : ∀ i, IsIntegral R (mk (MvPolynomial.X i)) := by
    intro i
    refine ⟨q i, hq i, ?_⟩
    change Polynomial.aeval (mk (MvPolynomial.X i)) (q i) = 0
    have hcompq : (algebraMap R S'').comp (RingHom.id R) =
        mk.toRingHom.comp (algebraMap R B) := by
      ext r
      simp [mk]
    have hh := Polynomial.map_aeval_eq_aeval_map (R := R) (φ := RingHom.id R)
      (ψ := mk.toRingHom) hcompq (q i) (MvPolynomial.X i)
    have hzero : mk (rel i) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_range_self i))
    calc
      Polynomial.aeval (mk (MvPolynomial.X i)) (q i) = mk (rel i) := by
        change Polynomial.eval₂ (algebraMap R S'') (mk.toRingHom (MvPolynomial.X i)) (q i) =
          mk.toRingHom (Polynomial.eval₂ (algebraMap R B) (MvPolynomial.X i) (q i))
        simpa only [Polynomial.aeval_def, Polynomial.map_id] using hh.symm
      _ = 0 := hzero
  let A : Subalgebra R S'' := Algebra.adjoin R
    (Set.range (fun i : Fin n => mk (MvPolynomial.X i)))
  have hAint : Algebra.IsIntegral R A := by
    change Algebra.IsIntegral R (Algebra.adjoin R
      (Set.range (fun i : Fin n => mk (MvPolynomial.X i))))
    apply Algebra.IsIntegral.adjoin
    rintro _ ⟨i, rfl⟩
    exact hvar i
  have hAtop : A = ⊤ := by
    apply top_unique
    intro z hz
    obtain ⟨v, rfl⟩ := Ideal.Quotient.mk_surjective z
    have hv : v ∈ Algebra.adjoin R
        (Set.range (MvPolynomial.X : Fin n → B)) := by
      rw [MvPolynomial.adjoin_range_X]
      trivial
    refine Algebra.adjoin_induction ?_ ?_ ?_ ?_ hv
    · rintro v ⟨i, rfl⟩
      exact Algebra.subset_adjoin ⟨i, rfl⟩
    · intro r
      exact A.algebraMap_mem r
    · intro v w _ _ hv hw
      simpa only [map_add] using A.add_mem hv hw
    · intro v w _ _ hv hw
      simpa only [map_mul] using A.mul_mem hv hw
  have hsurjA : Function.Surjective A.val := by
    intro z
    refine ⟨⟨z, ?_⟩, rfl⟩
    rw [hAtop]
    trivial
  have hInt : Algebra.IsIntegral R S'' :=
    Algebra.IsIntegral.of_surjective A.val hsurjA
  have hFT : Algebra.FiniteType R S'' := inferInstance
  have hfinite : RingHom.Finite (algebraMap R S'') := by
    let oldAlg : Algebra R S'' := inferInstance
    let rS0 : R →+* S'' := algebraMap R S''
    let newAlg : Algebra R S'' := rS0.toAlgebra
    have hfinite0 : RingHom.Finite rS0 := by
      let : Algebra R S'' := newAlg
      have hInt' : Algebra.IsIntegral R S'' := by
        refine ⟨?_⟩
        intro z
        obtain ⟨p, hp, hz⟩ := @Algebra.IsIntegral.isIntegral R S'' _ _ oldAlg hInt z
        refine ⟨p, hp, ?_⟩
        change Polynomial.eval₂ rS0 z p = 0
        let : Algebra R S'' := oldAlg
        change Polynomial.eval₂ rS0 z p = 0 at hz
        exact hz
      have hFT' : Algebra.FiniteType R S'' := by
        obtain ⟨s, hs⟩ := hFT
        have hle : ∀ z : S'',
            z ∈ @Algebra.adjoin R S'' _ _ oldAlg (↑s) →
              z ∈ @Algebra.adjoin R S'' _ _ newAlg (↑s) := by
          let : Algebra R S'' := oldAlg
          intro z hz
          refine Algebra.adjoin_induction ?_ ?_ ?_ ?_ hz
          · intro v hv
            let : Algebra R S'' := newAlg
            exact Algebra.subset_adjoin hv
          · intro r
            change rS0 r ∈ @Algebra.adjoin R S'' _ _ newAlg (↑s)
            let : Algebra R S'' := newAlg
            exact (@Algebra.adjoin R S'' _ _ newAlg (↑s)).algebraMap_mem r
          · intro v w _ _ hv hw
            let : Algebra R S'' := newAlg
            exact (@Algebra.adjoin R S'' _ _ newAlg (↑s)).add_mem hv hw
          · intro v w _ _ hv hw
            let : Algebra R S'' := newAlg
            exact (@Algebra.adjoin R S'' _ _ newAlg (↑s)).mul_mem hv hw
        have htop : @Algebra.adjoin R S'' _ _ newAlg (↑s) = ⊤ := by
          apply top_unique
          intro z hz
          apply hle z
          rw [hs]
          trivial
        refine ⟨s, ?_⟩
        exact htop
      exact Algebra.finite_iff_isIntegral_and_finiteType.mpr ⟨hInt', hFT'⟩
    simpa only [rS0] using hfinite0
  have hα0R : α₀.comp (algebraMap R B) = algebraMap R S := by
    ext r
    change α₀ (MvPolynomial.C r) = algebraMap R S r
    change MvPolynomial.eval₂ (algebraMap R S) t (MvPolynomial.C r) = _
    rw [MvPolynomial.eval₂_C]
  have hβ0R : β₀.comp (algebraMap R B) =
      D.rfS'.comp (algebraMap R Rf) := by
    ext r
    change β₀ (MvPolynomial.C r) = D.rfS' (algebraMap R Rf r)
    change MvPolynomial.eval₂ (algebraMap R S') c (MvPolynomial.C r) = _
    rw [MvPolynomial.eval₂_C]
    rfl
  have hαr : α.comp (algebraMap R S'') = D.rS := by
    apply RingHom.ext
    intro r
    have hmk := congrArg (fun g => g (algebraMap R B r)) hαmk
    have h0 := congrArg (fun g => g r) hα0R
    calc
      α (algebraMap R S'' r) = α (mk (algebraMap R B r)) := by rfl
      _ = α₀ (algebraMap R B r) := by
        simpa [RingHom.comp_apply] using hmk
      _ = algebraMap R S r := by
        simpa [RingHom.comp_apply] using h0
      _ = D.rS r := by rfl
  have hβr : β.comp (algebraMap R S'') =
      D.rfS'.comp (algebraMap R Rf) := by
    apply RingHom.ext
    intro r
    have hmk := congrArg (fun g => g (algebraMap R B r)) hβmk
    have h0 := congrArg (fun g => g r) hβ0R
    calc
      β (algebraMap R S'' r) = β (mk (algebraMap R B r)) := by rfl
      _ = β₀ (algebraMap R B r) := by
        simpa [RingHom.comp_apply] using hmk
      _ = D.rfS' (algebraMap R Rf r) := by
        simpa [RingHom.comp_apply] using h0
  have hcomm₀ : (algebraMap S Sf).comp α₀ = D.s'Sf.comp β₀ := by
    apply RingHom.ext
    intro z
    induction z using MvPolynomial.induction_on with
    | C r =>
        simp only [RingHom.comp_apply]
        change algebraMap S Sf
          (MvPolynomial.eval₂ (algebraMap R S) t (MvPolynomial.C r)) =
            D.s'Sf (MvPolynomial.eval₂ (algebraMap R S') c (MvPolynomial.C r))
        rw [MvPolynomial.eval₂_C, MvPolynomial.eval₂_C]
        exact (hbase r).symm
    | add p q hp hq => simpa only [map_add] using congrArg₂ (· + ·) hp hq
    | mul_X p i hp =>
        simp only [map_mul, α₀, β₀] at hp ⊢
        have hX :
            ((algebraMap S Sf).comp α₀) (MvPolynomial.X i) =
              (D.s'Sf.comp β₀) (MvPolynomial.X i) := by
          simp only [RingHom.comp_apply, α₀, β₀]
          rw [MvPolynomial.eval₂Hom_X', MvPolynomial.eval₂Hom_X']
          change algebraMap S Sf
              (D.rS (f ^ l i) * s i) =
            D.s'Sf (algebraMap R S' (f ^ l i) * b i)
          calc
            algebraMap S Sf (D.rS (f ^ l i) * s i) =
                algebraMap S Sf (D.rS (f ^ l i)) *
                  algebraMap S Sf (s i) := by
                    rw [map_mul]
            _ = D.s'Sf (algebraMap R S' (f ^ l i)) *
                D.s'Sf (b i) := by
                  rw [← hbase (f ^ l i), ← hbs i]
            _ = D.s'Sf (algebraMap R S' (f ^ l i) * b i) := by
                  exact (D.s'Sf.map_mul _ _).symm
        exact congrArg₂ (· * ·) hp hX
  have hcomm : (algebraMap S Sf).comp α = D.s'Sf.comp β := by
    apply RingHom.ext
    intro z
    obtain ⟨v, rfl⟩ := Ideal.Quotient.mk_surjective z
    calc
      algebraMap S Sf (α (Ideal.Quotient.mk I v)) =
          algebraMap S Sf (α₀ v) := by
        exact congrArg (algebraMap S Sf) (congrArg (fun g => g v) hαmk)
      _ = D.s'Sf (β₀ v) := congrArg (fun g => g v) hcomm₀
      _ = D.s'Sf (β (Ideal.Quotient.mk I v)) := by
        exact congrArg D.s'Sf (congrArg (fun g => g v) hβmk).symm
  let J : Ideal S'' := RingHom.ker α ⊓ RingHom.ker β
  have hJα : J ≤ RingHom.ker α := by
    exact inf_le_left
  have hJβ : J ≤ RingHom.ker β := by
    exact inf_le_right
  let Sfin := S'' ⧸ J
  let : CommRing Sfin := Ideal.Quotient.commRing J
  let qfin : S'' →ₐ[R] Sfin := Ideal.Quotient.mkₐ R J
  let αfin : Sfin →+* S := Ideal.Quotient.lift J α
    (fun a ha => RingHom.mem_ker.mp (hJα ha))
  let βfin : Sfin →+* S' := Ideal.Quotient.lift J β
    (fun a ha => RingHom.mem_ker.mp (hJβ ha))
  have hαq : αfin.comp qfin.toRingHom = α := by
    change (Ideal.Quotient.lift J α _).comp (Ideal.Quotient.mk J) = α
    exact Ideal.Quotient.lift_comp_mk J α _
  have hβq : βfin.comp qfin.toRingHom = β := by
    change (Ideal.Quotient.lift J β _).comp (Ideal.Quotient.mk J) = β
    exact Ideal.Quotient.lift_comp_mk J β _
  have hqfinite : qfin.toRingHom.Finite := by
    apply RingHom.Finite.of_surjective
    exact Ideal.Quotient.mkₐ_surjective R J
  let rSfin : R →+* Sfin := qfin.toRingHom.comp (algebraMap R S'')
  have hrSfin : rSfin = algebraMap R Sfin := by
    ext r
    rfl
  have hfinitefin : rSfin.Finite := hqfinite.comp hfinite
  have hαfinr : αfin.comp rSfin = D.rS := by
    apply RingHom.ext
    intro r
    have hq := congrArg (fun g => g (algebraMap R S'' r)) hαq
    have hr := congrArg (fun g => g r) hαr
    simpa [hrSfin, RingHom.comp_apply, qfin, RingHom.algebraMap_toAlgebra] using hq.trans hr
  have hβfinr : βfin.comp rSfin =
      D.rfS'.comp (algebraMap R Rf) := by
    apply RingHom.ext
    intro r
    have hq := congrArg (fun g => g (algebraMap R S'' r)) hβq
    have hr := congrArg (fun g => g r) hβr
    simpa [hrSfin, RingHom.comp_apply, qfin, RingHom.algebraMap_toAlgebra] using hq.trans hr
  have hcommfin : (algebraMap S Sf).comp αfin = D.s'Sf.comp βfin := by
    apply RingHom.ext
    intro z
    obtain ⟨v, rfl⟩ := Ideal.Quotient.mk_surjective z
    rw [RingHom.comp_apply, RingHom.comp_apply]
    calc
      algebraMap S Sf (αfin (qfin v)) = algebraMap S Sf (α v) := by
        exact congrArg (algebraMap S Sf) (congrArg (fun g => g v) hαq)
      _ = D.s'Sf (β v) := congrArg (fun g => g v) hcomm
      _ = D.s'Sf (βfin (qfin v)) := by
        exact congrArg D.s'Sf (congrArg (fun g => g v) hβq).symm
  let U : S' := D.rfS' (algebraMap R Rf f)
  have hcX : ∀ i, β₀ (MvPolynomial.X i) = φ (MvPolynomial.X i) * U ^ (e i + k i + l i) := by
    intro i
    simp only [β₀]
    rw [MvPolynomial.eval₂Hom_X']
    change c i = x i * U ^ (e i + k i + l i)
    simp only [c, b, a, x, RingHom.algebraMap_toAlgebra, map_pow]
    change U ^ l i * (U ^ k i * (U ^ e i * φ (MvPolynomial.X i))) =
      φ (MvPolynomial.X i) * U ^ (e i + k i + l i)
    calc
      U ^ l i * (U ^ k i * (U ^ e i * φ (MvPolynomial.X i))) =
          (U ^ l i * U ^ k i) * (U ^ e i * φ (MvPolynomial.X i)) := by
            rw [mul_assoc]
      _ = U ^ (l i + k i) * (U ^ e i * φ (MvPolynomial.X i)) := by
        rw [pow_add]
      _ = (U ^ (l i + k i) * U ^ e i) * φ (MvPolynomial.X i) := by
        rw [mul_assoc]
      _ = U ^ (l i + k i + e i) * φ (MvPolynomial.X i) := by
        rw [← pow_add]
      _ = φ (MvPolynomial.X i) * U ^ (e i + k i + l i) := by
        rw [show l i + k i + e i = e i + k i + l i by omega, mul_comm]
  have hβC : ∀ r : R, β₀ (MvPolynomial.C r) = algebraMap R S' r := by
    intro r
    simp only [β₀]
    rw [MvPolynomial.eval₂Hom_C]
  have hφC : ∀ r : Rf, φ (MvPolynomial.C r) = D.rfS' r := by
    intro r
    have h := φ.commutes r
    rw [MvPolynomial.algebraMap_eq, RingHom.algebraMap_toAlgebra] at h
    exact h
  have hU : algebraMap R S' f = U := by
    calc
      algebraMap R S' f = β₀ (MvPolynomial.C f) := (hβC f).symm
      _ = D.rfS' (algebraMap R Rf f) := by
        simpa [B, MvPolynomial.algebraMap_eq, RingHom.comp_apply] using
          congrArg (fun g => g f) hβ0R
      _ = U := rfl
  have hcx : ∀ i, c i = x i * U ^ (e i + k i + l i) := by
    intro i
    calc
      c i = β₀ (MvPolynomial.X i) := by
        change c i = MvPolynomial.eval₂Hom (algebraMap R S') c (MvPolynomial.X i)
        rw [MvPolynomial.eval₂Hom_X']
      _ = x i * U ^ (e i + k i + l i) := by simpa [x] using hcX i
  have hUpow : ∀ m : ℕ, algebraMap R S' (f ^ m) = U ^ m := by
    intro m
    rw [map_pow, hU]
  have hpoly : ∀ v : MvPolynomial (Fin n) Rf, ∃ m : ℕ, ∃ w : B,
      β₀ w = φ v * U ^ m := by
    intro v
    induction v using MvPolynomial.induction_on with
    | C r =>
        obtain ⟨m, a, hm⟩ := IsLocalization.Away.surj f r
        refine ⟨m, MvPolynomial.C a, ?_⟩
        calc
          β₀ (MvPolynomial.C a) = D.rfS' (algebraMap R Rf a) := by
            simpa [B, MvPolynomial.algebraMap_eq, RingHom.comp_apply] using
              congrArg (fun g => g a) hβ0R
          _ = D.rfS' (r * (algebraMap R Rf f) ^ m) := by rw [hm]
          _ = D.rfS' r * U ^ m := by simp [U, map_mul, map_pow]
          _ = φ (MvPolynomial.C r) * U ^ m := by rw [hφC r]
    | add p q hp hq =>
        obtain ⟨m, w, hw⟩ := hp
        obtain ⟨m', w', hw'⟩ := hq
        refine ⟨m + m', w * MvPolynomial.C (f ^ m') +
          w' * MvPolynomial.C (f ^ m), ?_⟩
        rw [map_add, map_mul, map_mul, hw, hw', hβC, hβC, map_add]
        simp only [map_pow, hU]
        simp [U, mul_add, mul_assoc, mul_comm, mul_left_comm, pow_add]
    | mul_X p i hp =>
        obtain ⟨m, w, hw⟩ := hp
        refine ⟨m + (e i + k i + l i), w * MvPolynomial.X i, ?_⟩
        rw [map_mul, MvPolynomial.eval₂Hom_X', hw, hcx i]
        simp only [map_mul, x]
        simp [U, pow_add, mul_assoc, mul_comm, mul_left_comm]
  have hsurj : ∀ z : S', ∃ (m : ℕ) (a : Sfin),
      z * βfin (rSfin f) ^ m = βfin a := by
    intro z
    obtain ⟨v, hv⟩ := hφ z
    obtain ⟨m, w, hw⟩ := hpoly v
    refine ⟨m, qfin w, ?_⟩
    have hβf := congrArg (fun g => g f) hβfinr
    have hβf' : βfin (rSfin f) = U := by
      simpa [RingHom.comp_apply, U] using hβf
    calc
      z * βfin (rSfin f) ^ m = φ v * U ^ m := by rw [← hv, hβf']
      _ = β₀ w := hw.symm
      _ = βfin (qfin w) := (congrArg (fun g => g w) hβq).symm
  have hexists : ∀ a b : Sfin, βfin a = βfin b →
      ∃ (m : ℕ), (rSfin f) ^ m * a = (rSfin f) ^ m * b := by
    intro a b hab
    obtain ⟨v, rfl⟩ := Ideal.Quotient.mk_surjective a
    obtain ⟨w, rfl⟩ := Ideal.Quotient.mk_surjective b
    have hab' : β v = β w := by
      calc
        β v = βfin (qfin v) := (congrArg (fun g => g v) hβq).symm
        _ = βfin (qfin w) := hab
        _ = β w := congrArg (fun g => g w) hβq
    have hsfeq : algebraMap S Sf (α v) = algebraMap S Sf (α w) := by
      calc
        algebraMap S Sf (α v) = D.s'Sf (β v) :=
          congrArg (fun g => g v) hcomm
        _ = D.s'Sf (β w) := congrArg D.s'Sf hab'
        _ = algebraMap S Sf (α w) := (congrArg (fun g => g w) hcomm).symm
    obtain ⟨m, hm⟩ := IsLocalization.Away.exists_of_eq (D.rS f) hsfeq
    have hαf := congrArg (fun g => g f) hαr
    have hβf := congrArg (fun g => g f) hβr
    let v' := (algebraMap R S'' f) ^ m * v
    let w' := (algebraMap R S'' f) ^ m * w
    have hαf' : α (algebraMap R S'' f) = D.rS f := by
      simpa [RingHom.comp_apply] using hαf
    have hβf' : β (algebraMap R S'' f) =
        D.rfS' (algebraMap R Rf f) := by
      simpa [RingHom.comp_apply] using hβf
    have hα' : α v' = α w' := by
      simp only [v', w', map_mul, map_pow]
      rw [hαf']
      exact hm
    have hβ' : β v' = β w' := by
      simp only [v', w', map_mul, map_pow]
      rw [hβf', hab']
    have hJ : v' - w' ∈ J := by
      change v' - w' ∈ RingHom.ker α ⊓ RingHom.ker β
      constructor
      · apply RingHom.mem_ker.mpr
        rw [map_sub]
        exact sub_eq_zero.mpr hα'
      · apply RingHom.mem_ker.mpr
        rw [map_sub]
        exact sub_eq_zero.mpr hβ'
    have hqeq : Ideal.Quotient.mk J v' = Ideal.Quotient.mk J w' := by
      apply sub_eq_zero.mp
      rw [← map_sub, Ideal.Quotient.eq_zero_iff_mem]
      exact hJ
    refine ⟨m, ?_⟩
    change (rSfin f) ^ m * qfin v = (rSfin f) ^ m * qfin w
    calc
      (rSfin f) ^ m * qfin v = qfin v' := by
        simp [v', rSfin, map_mul, map_pow]
      _ = qfin w' := by
        change Ideal.Quotient.mk J v' = Ideal.Quotient.mk J w'
        exact hqeq
      _ = (rSfin f) ^ m * qfin w := by
        symm
        have hrs : rSfin f = qfin (algebraMap R S'' f) := by rfl
        rw [hrs, ← map_pow, ← map_mul]
  let : Algebra Sfin S' := βfin.toAlgebra
  have hunit : IsUnit (algebraMap Sfin S' (rSfin f)) := by
    have hβf := congrArg (fun g => g f) hβfinr
    have hβf' : βfin (rSfin f) = U := by
      simpa [RingHom.comp_apply, U] using hβf
    change IsUnit (βfin (rSfin f))
    rw [hβf']
    exact IsUnit.map D.rfS' (IsLocalization.Away.algebraMap_isUnit f)
  refine ⟨Sfin, inferInstance, rSfin, hfinitefin, αfin, βfin,
    hαfinr, hβfinr, hcommfin, ?_⟩
  exact IsLocalization.Away.mk _ hunit hsurj hexists

end
end Formalization.Books.Obsolete.Unit05
