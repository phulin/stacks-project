import Formalization.Books.Algebra.Unit29.ImagesOfFinitePresentation
import Formalization.Books.Topology.Unit21.NowhereDenseSets
import Mathlib.RingTheory.Algebraic.Basic
import Mathlib.RingTheory.Extension.Generators
import Mathlib.RingTheory.Localization.FractionRing

/-!
# Commutative Algebra, Chapter 30: More on images

The source's spectrum maps are represented by Mathlib's canonical
`PrimeSpectrum.comap`.  Ideals, radicals, minimal primes, constructible sets,
finite type and finite presentation use the corresponding canonical Mathlib
interfaces.  The only source-facing construction below is the localization
map needed to write the generic finite-presentation statement with explicit
denominators.
-/

namespace Formalization.Books.Algebra.Unit30

open Set
open _root_.Topology
open scoped TensorProduct
attribute [local instance] Polynomial.algebra Polynomial.isLocalization

/-! ## Generic finite presentation and constructible images -/

private theorem test_localized_eval
    {R S : Type*} [CommRing R] [CommRing S] [IsDomain R] [IsDomain S]
    (m : R) (_hm : m ≠ 0)
    (φ : R →+* S) (x : S) (_hφ : Function.Injective φ)
    (hev : Function.Surjective (Polynomial.eval₂RingHom φ x)) :
    Function.Surjective
      (IsLocalization.map (S := Polynomial (Localization.Away m))
        (Localization (Submonoid.map (Polynomial.eval₂RingHom φ x)
          (Submonoid.map (Polynomial.C : R →+* Polynomial R) (Submonoid.powers m))))
        (Polynomial.eval₂RingHom φ x)
        (Submonoid.map (Polynomial.C : R →+* Polynomial R) (Submonoid.powers m)).le_comap_map) := by
  let M := Submonoid.map (Polynomial.C : R →+* Polynomial R) (Submonoid.powers m)
  let T := Submonoid.map φ (Submonoid.powers m)
  have hT : Submonoid.map (Polynomial.eval₂RingHom φ x) M = T := by
    ext z
    constructor
    · rintro ⟨p, ⟨q, ⟨n, rfl⟩, rfl⟩, rfl⟩
      exact ⟨m ^ n, ⟨n, rfl⟩, by
        change φ (m ^ n) = Polynomial.eval₂ φ x (Polynomial.C (m ^ n))
        rw [Polynomial.eval₂_C]⟩
    · rintro ⟨s, ⟨n, rfl⟩, rfl⟩
      refine ⟨Polynomial.C (m ^ n), ?_, ?_⟩
      · exact ⟨m ^ n, ⟨n, rfl⟩, rfl⟩
      · change Polynomial.eval₂ φ x (Polynomial.C (m ^ n)) = φ (m ^ n)
        rw [Polynomial.eval₂_C]
  let : IsLocalization T (Localization (Submonoid.map
      (Polynomial.eval₂RingHom φ x) M)) := by
    rw [← hT]
    infer_instance
  let e : Polynomial (Localization.Away m) →+*
      Localization (Submonoid.map (Polynomial.eval₂RingHom φ x) M) :=
    IsLocalization.map _ (Polynomial.eval₂RingHom φ x) M.le_comap_map
  let g : Localization.Away m →+*
      Localization (Submonoid.map (Polynomial.eval₂RingHom φ x) M) :=
    IsLocalization.map _ φ (Submonoid.powers m).le_comap_map
  have hcomp : e.comp (algebraMap (Localization.Away m)
      (Polynomial (Localization.Away m))) = g := by
    apply IsLocalization.ringHom_ext (Submonoid.powers m)
    ext a
    simp only [RingHom.comp_apply]
    have ha : Polynomial.C (algebraMap R (Localization.Away m) a) =
        algebraMap (Polynomial R) (Polynomial (Localization.Away m)) (Polynomial.C a) := by
      simp
    rw [Polynomial.algebraMap_apply]
    have hb : Polynomial.C (algebraMap (Localization.Away m) (Localization.Away m)
        (algebraMap R (Localization.Away m) a)) =
        Polynomial.C (algebraMap R (Localization.Away m) a) := by simp
    have heC : e (Polynomial.C (algebraMap R (Localization.Away m) a)) =
        (algebraMap S (Localization (Submonoid.map
          (Polynomial.eval₂RingHom φ x) M))) (φ a) := by
      rw [ha]
      dsimp [e]
      change (IsLocalization.map (Localization (Submonoid.map
        (Polynomial.eval₂RingHom φ x) M)) (Polynomial.eval₂RingHom φ x)
        M.le_comap_map)
        (algebraMap (Polynomial R) (Polynomial (Localization.Away m))
          (Polynomial.C a)) = _
      rw [IsLocalization.map_eq]
      simp
    have hg : g (algebraMap R (Localization.Away m) a) =
        (algebraMap S (Localization (Submonoid.map
          (Polynomial.eval₂RingHom φ x) M))) (φ a) := by
      dsimp [g]
      rw [IsLocalization.map_eq]
    simpa [hb] using heC.trans hg.symm
  exact IsLocalization.map_surjective_of_surjective
    (M := M) (S := Polynomial (Localization.Away m))
    (Q := Localization (Submonoid.map (Polynomial.eval₂RingHom φ x) M))
    (g := Polynomial.eval₂RingHom φ x) hev

private theorem test_localization_submonoid
    {R S : Type*} [CommRing R] [CommRing S]
    (φ : R →+* S) (x : S) (m : R) :
    Submonoid.map (Polynomial.eval₂RingHom φ x)
        (Submonoid.map (Polynomial.C : R →+* Polynomial R) (Submonoid.powers m)) =
      Submonoid.map φ (Submonoid.powers m) := by
  ext z
  constructor
  · rintro ⟨p, ⟨q, ⟨n, rfl⟩, rfl⟩, rfl⟩
    exact ⟨m ^ n, ⟨n, rfl⟩, by
      change φ (m ^ n) = Polynomial.eval₂ φ x (Polynomial.C (m ^ n))
      rw [Polynomial.eval₂_C]⟩
  · rintro ⟨s, ⟨n, rfl⟩, rfl⟩
    refine ⟨Polynomial.C (m ^ n), ?_, ?_⟩
    · exact ⟨m ^ n, ⟨n, rfl⟩, rfl⟩
    · change Polynomial.eval₂ φ x (Polynomial.C (m ^ n)) = φ (m ^ n)
      rw [Polynomial.eval₂_C]

private theorem ker_eval_eq_span_of_map_eq_minpoly
    {A B K L : Type*} [CommRing A] [CommRing B] [Field K] [Field L]
    [Algebra K L]
    (ψ : A →+* B) (α : A →+* K) (β : B →+* L) (γ : K →+* L)
    (x : B) (q : Polynomial A)
    (hα : Function.Injective α) (_hβ : Function.Injective β)
    (hcomp : β.comp ψ = γ.comp α) (hγ : γ = algebraMap K L)
    (hqmonic : q.Monic) (hqroot : Polynomial.eval₂RingHom ψ x q = 0)
    (hqmap : q.map α = minpoly K (β x)) :
    RingHom.ker (Polynomial.eval₂RingHom ψ x) = Ideal.span ({q} : Set (Polynomial A)) := by
  let : Nontrivial A := ⟨⟨0, 1, fun h => by
    have := congrArg α h
    simp at this⟩⟩
  ext p
  constructor
  · intro hp
    have hroot : Polynomial.eval₂RingHom ψ x (p %ₘ q) = 0 := by
      change Polynomial.eval₂ ψ x (p %ₘ q) = 0
      rw [Polynomial.eval₂_modByMonic_eq_self_of_root hqroot]
      exact hp
    have hroot' :
        Polynomial.eval₂ γ (β x) ((p %ₘ q).map α) = 0 := by
      rw [Polynomial.eval₂_map, ← hcomp]
      rw [← Polynomial.hom_eval₂]
      simpa using congrArg β hroot
    have hdvd : minpoly K (β x) ∣ (p %ₘ q).map α :=
      minpoly.dvd K (β x) (by
        simpa [Polynomial.aeval_def, hγ] using hroot')
    rw [← hqmap] at hdvd
    have hdeg : ((p %ₘ q).map α).degree < (q.map α).degree := by
      rw [Polynomial.degree_map_eq_of_injective hα,
        Polynomial.degree_map_eq_of_injective hα]
      exact Polynomial.degree_modByMonic_lt p hqmonic
    have hzero : (p %ₘ q).map α = 0 :=
      Polynomial.eq_zero_of_dvd_of_degree_lt hdvd (hqmap ▸ hdeg)
    have hrem : p %ₘ q = 0 := Polynomial.map_injective α hα (by simpa using hzero)
    simpa [Ideal.mem_span_singleton] using
      (Polynomial.mem_ker_modByMonic hqmonic).mp hrem
  · intro hp
    rw [Ideal.mem_span_singleton] at hp
    obtain ⟨r, rfl⟩ := hp
    change Polynomial.eval₂RingHom ψ x (q * r) = 0
    rw [map_mul, hqroot, zero_mul]

private theorem one_generator_local_fp
    {R S : Type*} [CommRing R] [CommRing S] [IsDomain R] [IsDomain S]
    (φ : R →+* S) (hφ : Function.Injective φ)
    (x : S) (hev : Function.Surjective (Polynomial.eval₂RingHom φ x))
    (hxa : ∃ p : Polynomial (FractionRing R), p ≠ 0 ∧
      Polynomial.eval₂ (IsFractionRing.lift
        (g := (algebraMap S (FractionRing S)).comp φ)
        (A := R) (K := FractionRing R) (L := FractionRing S)
        (fun _a _b h => hφ (IsFractionRing.injective S (FractionRing S) h)))
        (algebraMap S (FractionRing S) x) p = 0) :
  ∃ m : R, m ≠ 0 ∧ RingHom.FinitePresentation (Localization.awayMap φ m) := by
  classical
  let K := FractionRing R
  let L := FractionRing S
  let : Algebra R S := φ.toAlgebra
  let : Algebra K L :=
    RingHom.toAlgebra (IsFractionRing.lift
      (g := (algebraMap S L).comp φ)
      (A := R) (K := K) (L := L)
      (fun a b h => hφ (IsFractionRing.injective S L h)))
  let xL := algebraMap S L x
  let p := minpoly K xL
  have hxa' : IsAlgebraic K xL := by
    change ∃ p : Polynomial K, p ≠ 0 ∧
      Polynomial.eval₂ (IsFractionRing.lift
        (g := (algebraMap S L).comp φ) (A := R) (K := K) (L := L)
        (fun a b h => hφ (IsFractionRing.injective S L h)))
        (algebraMap S L x) p = 0
    exact hxa
  have hpmonic : p.Monic := minpoly.monic (IsAlgebraic.isIntegral hxa')
  let M₀ := nonZeroDivisors R
  let d₀ := IsLocalization.commonDenom M₀ p.support p.coeff
  let d : R := d₀
  have hd : d ≠ 0 := by
    change (d₀ : R) ≠ 0
    exact mem_nonZeroDivisors_iff_ne_zero.mp d₀.property
  have hmem : p.scaleRoots (algebraMap R K d) ∈ Polynomial.lifts (algebraMap R K) := by
    exact IsLocalization.scaleRoots_commonDenom_mem_lifts M₀ p (by
      rw [hpmonic.leadingCoeff]
      exact one_mem _)
  obtain ⟨q, hqmap, -, hqmonic⟩ :=
    Polynomial.lifts_and_natDegree_eq_and_monic hmem
      (Polynomial.monic_scaleRoots_iff _ |>.mpr hpmonic)
  let M := Submonoid.map (Polynomial.C : R →+* Polynomial R) (Submonoid.powers d)
  let T := Submonoid.map φ (Submonoid.powers d)
  have hTnonzero : T ≤ nonZeroDivisors S :=
    map_le_nonZeroDivisors_of_injective φ hφ
      (powers_le_nonZeroDivisors_of_noZeroDivisors hd)
  let Q := Localization (Submonoid.map (Polynomial.eval₂RingHom φ x) M)
  have hT : Submonoid.map (Polynomial.eval₂RingHom φ x) M = T := by
    ext z
    constructor
    · rintro ⟨p', ⟨r', ⟨n, rfl⟩, rfl⟩, rfl⟩
      exact ⟨d ^ n, ⟨n, rfl⟩, by
        change φ (d ^ n) = Polynomial.eval₂ φ x (Polynomial.C (d ^ n))
        rw [Polynomial.eval₂_C]⟩
    · rintro ⟨s, ⟨n, rfl⟩, rfl⟩
      refine ⟨Polynomial.C (d ^ n), ?_, ?_⟩
      · exact ⟨d ^ n, ⟨n, rfl⟩, rfl⟩
      · change Polynomial.eval₂ φ x (Polynomial.C (d ^ n)) = φ (d ^ n)
        rw [Polynomial.eval₂_C]
  let : IsLocalization T Q := by
    rw [← hT]
    infer_instance
  let g : Localization.Away d →+* Q :=
    IsLocalization.map Q φ (Submonoid.powers d).le_comap_map
  let e : Polynomial (Localization.Away d) →+* Q :=
    IsLocalization.map Q (Polynomial.eval₂RingHom φ x) M.le_comap_map
  have hesurj : Function.Surjective e := by
    exact test_localized_eval d hd φ x hφ hev
  let α : Localization.Away d →+* K :=
    IsLocalization.Away.lift d
      (IsFractionRing.isUnit_map_of_injective (IsFractionRing.injective R K) d₀)
  let β : Q →+* L :=
    IsLocalization.lift (M := T) (S := Q)
      (fun y : T => IsFractionRing.isUnit_map_of_injective
        (IsFractionRing.injective S L) ⟨y.1, hTnonzero y.2⟩)
  have hα : Function.Injective α := by
    change Function.Injective (IsLocalization.lift (M := Submonoid.powers d)
      (fun y : Submonoid.powers d => IsFractionRing.isUnit_map_of_injective
        (IsFractionRing.injective R K) ⟨y.1, powers_le_nonZeroDivisors_of_noZeroDivisors hd y.2⟩))
    rw [IsLocalization.lift_injective_iff]
    intro a b
    constructor
    · intro h
      simpa [α] using congrArg α h
    · intro h
      have hab : a = b := (IsFractionRing.injective R K) h
      simp [hab]
  have hβ : Function.Injective β := by
    change Function.Injective (IsLocalization.lift (M := T) (S := Q)
      (fun y : T => IsFractionRing.isUnit_map_of_injective
        (IsFractionRing.injective S L) ⟨y.1, hTnonzero y.2⟩))
    rw [IsLocalization.lift_injective_iff]
    intro a b
    constructor
    · intro h
      simpa [β] using congrArg β h
    · intro h
      have hab : a = b := (IsFractionRing.injective S L) h
      simp [hab]
  have hcomp : β.comp g = (algebraMap K L).comp α := by
    have hbase : (algebraMap K L).comp (algebraMap R K) =
        (algebraMap S L).comp φ := by
      have hKL : (algebraMap K L : K →+* L) = IsFractionRing.lift
          (g := (algebraMap S L).comp φ) (A := R) (K := K) (L := L)
          (fun a b h => hφ (IsFractionRing.injective S L h)) := rfl
      rw [hKL]
      apply RingHom.ext
      intro a
      change IsFractionRing.lift
          (g := (algebraMap S L).comp φ) (A := R) (K := K) (L := L)
          (fun a b h => hφ (IsFractionRing.injective S L h))
          (algebraMap R K a) = (algebraMap S L) (φ a)
      exact IsFractionRing.lift_algebraMap
        (A := R) (K := K) (L := L)
        (g := (algebraMap S L).comp φ)
        (fun a b h => hφ (IsFractionRing.injective S L h)) a
    apply IsLocalization.ringHom_ext (Submonoid.powers d)
    ext a
    simp [α, β, g, IsLocalization.lift_eq]
    exact congrArg (fun k : R →+* L => k a) hbase.symm
  let r := (q.map (algebraMap R (Localization.Away d))).scaleRoots
    (IsLocalization.Away.invSelf d)
  have hD : algebraMap R K d ≠ 0 := by
    intro h
    apply hd
    exact (IsFractionRing.injective R K) (by simpa using h)
  have hrmap : r.map α = p := by
    dsimp [r]
    have hmapq : (q.map (algebraMap R (Localization.Away d))).map α =
        q.map (algebraMap R K) := by
      have hαcomp : α.comp (algebraMap R (Localization.Away d)) = algebraMap R K := by
        simp [α]
      simpa [hαcomp] using
        (Polynomial.map_map (f := algebraMap R (Localization.Away d)) α q)
    rw [Polynomial.map_scaleRoots]
    · rw [hmapq, hqmap, ← Polynomial.scaleRoots_mul]
      have hinv : α (IsLocalization.Away.invSelf d) = (algebraMap R K d)⁻¹ := by
        have hmul : (algebraMap R K d) * α (IsLocalization.Away.invSelf d) = 1 := by
          have hmul' := congrArg α (IsLocalization.Away.mul_invSelf d)
          rw [map_mul, map_one] at hmul'
          rw [show α (algebraMap R (Localization.Away d) d) = algebraMap R K d by
            simp [α]] at hmul'
          exact hmul'
        exact ((mul_eq_one_iff_inv_eq₀ hD).mp hmul).symm
      rw [hinv]
      simp [hD]
    · have hmonic : (q.map (algebraMap R (Localization.Away d))).Monic :=
        hqmonic.map _
      rw [hmonic.leadingCoeff]
      intro hzero
      have hK : (1 : K) = 0 := by
        simp at hzero
      exact (one_ne_zero : (1 : K) ≠ 0) hK
  let xQ : Q := algebraMap S Q x
  have hroot : Polynomial.eval₂RingHom g xQ r = 0 := by
    apply hβ
    change β (Polynomial.eval₂ g xQ r) = β 0
    rw [Polynomial.hom_eval₂, hcomp]
    rw [← Polynomial.eval₂_map, hrmap]
    have hxQ : β xQ = xL := by
      dsimp [xQ, β]
      rw [IsLocalization.lift_eq]
    rw [hxQ]
    simpa [xL, p, Polynomial.aeval_def] using minpoly.aeval K xL
  have hker : RingHom.ker (Polynomial.eval₂RingHom g xQ) =
      Ideal.span ({r} : Set (Polynomial (Localization.Away d))) := by
    apply ker_eval_eq_span_of_map_eq_minpoly g α β (algebraMap K L) xQ r hα hβ hcomp rfl
    · exact (Polynomial.monic_scaleRoots_iff _).mpr (hqmonic.map _)
    · exact hroot
    · have hxQ : β xQ = xL := by
        dsimp [xQ, β]
        rw [IsLocalization.lift_eq]
      simpa [hxQ, xL, p]
  have heq : e = Polynomial.eval₂RingHom g xQ := by
    apply Polynomial.ringHom_ext
    intro a
    · have heC : e.comp (Polynomial.C : Localization.Away d →+*
          Polynomial (Localization.Away d)) = g := by
        apply IsLocalization.ringHom_ext (Submonoid.powers d)
        ext b
        change e (Polynomial.C (algebraMap R (Localization.Away d) b)) =
          g (algebraMap R (Localization.Away d) b)
        have hC : Polynomial.C (algebraMap R (Localization.Away d) b) =
            algebraMap (Polynomial R) (Polynomial (Localization.Away d))
              (Polynomial.C b) := by
          simp
        rw [hC]
        dsimp [e]
        change (IsLocalization.map Q (Polynomial.eval₂RingHom φ x)
          M.le_comap_map)
          (algebraMap (Polynomial R) (Polynomial (Localization.Away d))
            (Polynomial.C b)) = g (algebraMap R (Localization.Away d) b)
        rw [IsLocalization.map_eq]
        dsimp [g]
        rw [Polynomial.eval₂_C]
        rw [IsLocalization.map_eq]
      simpa [RingHom.comp_apply] using congrArg
        (fun k : Localization.Away d →+* Q => k a) heC
    · have hX : e Polynomial.X = xQ := by
        have hX' : Polynomial.X =
            algebraMap (Polynomial R) (Polynomial (Localization.Away d)) Polynomial.X := by
          simp
        rw [hX']
        dsimp [e]
        change (IsLocalization.map Q (Polynomial.eval₂RingHom φ x)
          M.le_comap_map)
          (algebraMap (Polynomial R) (Polynomial (Localization.Away d)) Polynomial.X) = xQ
        rw [IsLocalization.map_eq]
        simp [xQ]
      simp [hX, xQ]
  have hef : e.FinitePresentation :=
    RingHom.FinitePresentation.of_surjective e hesurj (by
      rw [heq, hker]
      exact Submodule.fg_span (Set.finite_singleton r))
  have hbase : (algebraMap (Localization.Away d)
      (Polynomial (Localization.Away d))).FinitePresentation := by
    rw [RingHom.finitePresentation_algebraMap]
    infer_instance
  have hgf : g.FinitePresentation := by
    rw [← show e.comp (algebraMap (Localization.Away d)
      (Polynomial (Localization.Away d))) = g from by
        rw [heq]
        ext a
        simp]
    exact hef.comp hbase
  have hpow : T = Submonoid.powers (φ d) := by
    ext z
    constructor
    · rintro ⟨s, ⟨n, rfl⟩, rfl⟩
      exact ⟨n, by simp⟩
    · rintro ⟨n, rfl⟩
      exact ⟨d ^ n, ⟨n, rfl⟩, by simp⟩
  let : IsLocalization T (Localization.Away (φ d)) := by
    rw [hpow]
    infer_instance
  let eQ : Q ≃ₐ[S] Localization.Away (φ d) :=
    IsLocalization.algEquiv T Q (Localization.Away (φ d))
  have heQ : (eQ : Q →+* Localization.Away (φ d)).FinitePresentation :=
    RingHom.FinitePresentation.of_bijective eQ.bijective
  have hfinal : ((eQ : Q →+* Localization.Away (φ d)).comp g).FinitePresentation :=
    heQ.comp hgf
  have hmap : (eQ : Q →+* Localization.Away (φ d)).comp g =
      Localization.awayMap φ d := by
    apply IsLocalization.ringHom_ext (Submonoid.powers d)
    ext a
    simp [eQ, g, Localization.awayMap, IsLocalization.Away.map,
      IsLocalization.map_eq]
  refine ⟨d, hd, ?_⟩
  simpa [hmap] using hfinal

/- The map in the first lemma is the canonical map
`R_f → S_{φ(f)g}`.  It is obtained by the universal property of localization;
the image of `f` is invertible because it divides `φ(f) * g`. -/
noncomputable def localizationAwayMulMap
    {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) (f : R) (g : S) :
    Localization.Away f →+* Localization.Away (φ f * g) :=
  Localization.awayLift
    ((algebraMap S (Localization.Away (φ f * g))).comp φ) f
    (by
      change IsUnit (algebraMap S (Localization.Away (φ f * g)) (φ f))
      exact IsLocalization.Away.isUnit_of_dvd
        (S := Localization.Away (φ f * g))
        (x := φ f * g) (r := φ f) (dvd_mul_right (φ f) g))

private theorem localizationAwayMulMap_finitePresentation_of_awayMap
    {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) (f : R) (g : S)
    (h : RingHom.FinitePresentation (Localization.awayMap φ f)) :
    RingHom.FinitePresentation (localizationAwayMulMap φ f g) := by
  let A := Localization.Away (φ f)
  let T := Localization.Away (algebraMap S A g)
  let : SMul S A := (inferInstance : Algebra S A).toSMul
  let : SMul A T := (inferInstance : Algebra A T).toSMul
  let : Algebra S T :=
    ((algebraMap A T).comp (algebraMap S A)).toAlgebra
  let : SMul S T := (inferInstance : Algebra S T).toSMul
  let : IsScalarTower S A T :=
    IsScalarTower.of_algebraMap_eq' rfl
  let : IsLocalization.Away (φ f * g) T :=
    IsLocalization.Away.mul' A T (φ f) g
  let e : T ≃ₐ[S] Localization.Away (φ f * g) :=
    IsLocalization.algEquiv (Submonoid.powers (φ f * g)) T
      (Localization.Away (φ f * g))
  have hAT : RingHom.FinitePresentation (algebraMap A T) := by
    rw [RingHom.finitePresentation_algebraMap]
    infer_instance
  have hcomp : RingHom.FinitePresentation
      ((algebraMap A T).comp (Localization.awayMap φ f)) :=
    hAT.comp h
  have he : RingHom.FinitePresentation (e : T →+* Localization.Away (φ f * g)) :=
    RingHom.FinitePresentation.of_bijective e.bijective
  have hfinal : RingHom.FinitePresentation
      ((e : T →+* Localization.Away (φ f * g)).comp
        ((algebraMap A T).comp (Localization.awayMap φ f))) :=
    he.comp hcomp
  have heq : (e : T →+* Localization.Away (φ f * g)).comp
      ((algebraMap A T).comp (Localization.awayMap φ f)) =
      localizationAwayMulMap φ f g := by
    apply IsLocalization.ringHom_ext (Submonoid.powers f)
    ext a
    simp only [RingHom.comp_apply]
    have hleft : (Localization.awayMap φ f)
        (algebraMap R (Localization.Away f) a) =
        algebraMap S (Localization.Away (φ f)) (φ a) := by
      simp [Localization.awayMap, IsLocalization.Away.map,
        IsLocalization.map_eq]
    have hright : localizationAwayMulMap φ f g
        (algebraMap R (Localization.Away f) a) =
        algebraMap S (Localization.Away (φ f * g)) (φ a) := by
      simp [localizationAwayMulMap]
    rw [hleft, hright]
    change e ((algebraMap A T) ((algebraMap S A) (φ a))) =
      algebraMap S (Localization.Away (φ f * g)) (φ a)
    rw [← IsScalarTower.algebraMap_apply S A T]
    exact e.commutes _
  rw [← heq]
  exact hfinal

private theorem localizationAwayMulMap_one_finitePresentation_of_finitePresentation
    {R S : Type*} [CommRing R] [CommRing S]
    (φ : R →+* S) (hφ : RingHom.FinitePresentation φ) :
    RingHom.FinitePresentation (localizationAwayMulMap φ 1 1) := by
  let eR : R ≃ₐ[R] Localization.Away (1 : R) :=
    IsLocalization.atOne R (Localization.Away (1 : R))
  let eS : S ≃ₐ[S] Localization.Away (φ 1 * 1) :=
    IsLocalization.atUnit S (Localization.Away (φ 1 * 1))
      (φ 1 * 1) (by simp)
  have heR : RingHom.FinitePresentation
      (eR.symm : Localization.Away (1 : R) →+* R) :=
    RingHom.FinitePresentation.of_bijective eR.symm.bijective
  have heS : RingHom.FinitePresentation
      (eS : S →+* Localization.Away (φ 1 * 1)) :=
    RingHom.FinitePresentation.of_bijective eS.bijective
  have hcomp : RingHom.FinitePresentation
      ((eS : S →+* Localization.Away (φ 1 * 1)).comp
        (φ.comp (eR.symm : Localization.Away (1 : R) →+* R))) :=
    heS.comp (hφ.comp heR)
  have heq : (eS : S →+* Localization.Away (φ 1 * 1)).comp
      (φ.comp (eR.symm : Localization.Away (1 : R) →+* R)) =
      localizationAwayMulMap φ 1 1 := by
    apply IsLocalization.ringHom_ext (Submonoid.powers (1 : R))
    ext r
    simpa [eR, localizationAwayMulMap] using eS.commutes (φ r)
  exact heq ▸ hcomp

private theorem one_generator_local_fp_general
    {R S : Type*} [CommRing R] [CommRing S] [IsDomain R] [IsDomain S]
    (φ : R →+* S) (hφ : Function.Injective φ)
    (x : S) (hev : Function.Surjective (Polynomial.eval₂RingHom φ x)) :
    ∃ f : R, f ≠ 0 ∧ ∃ g : S, g ≠ 0 ∧
      RingHom.FinitePresentation (localizationAwayMulMap φ f g) := by
  classical
  let K := FractionRing R
  let L := FractionRing S
  let γ := IsFractionRing.lift
    (g := (algebraMap S L).comp φ)
    (A := R) (K := K) (L := L)
    (fun _a _b h => hφ (IsFractionRing.injective S L h))
  let xL := algebraMap S L x
  let : Algebra K L := RingHom.toAlgebra γ
  by_cases hxa : ∃ p : Polynomial K, p ≠ 0 ∧
      Polynomial.eval₂ γ xL p = 0
  · obtain ⟨m, hm, hmfp⟩ := one_generator_local_fp φ hφ x hev hxa
    exact ⟨m, hm, 1, one_ne_zero,
      localizationAwayMulMap_finitePresentation_of_awayMap φ m 1 hmfp⟩
  · have hinj : Function.Injective (Polynomial.eval₂RingHom φ x) := by
      have hcomp : (algebraMap S L).comp φ =
          γ.comp (algebraMap R K) := by
        apply RingHom.ext
        intro y
        change (algebraMap S L) (φ y) = γ (algebraMap R K y)
        exact (IsFractionRing.lift_algebraMap
          (A := R) (K := K) (L := L)
          (g := (algebraMap S L).comp φ)
          (fun a b h => hφ (IsFractionRing.injective S L h)) y).symm
      intro p q hpq
      by_contra hpq0
      have hpqmap : p - q ≠ 0 := sub_ne_zero.mpr hpq0
      have hroot : Polynomial.eval₂ γ xL
          ((p - q).map (algebraMap R K)) = 0 := by
        rw [Polynomial.eval₂_map, ← hcomp, ← Polynomial.hom_eval₂]
        have := congrArg (algebraMap S L) (sub_eq_zero.mpr hpq)
        simpa [γ, xL] using this
      apply hxa
      refine ⟨(p - q).map (algebraMap R K), ?_, hroot⟩
      intro hzero
      apply hpqmap
      exact Polynomial.map_injective (algebraMap R K)
        (IsFractionRing.injective R K) (by simpa using hzero)
    have hEval : RingHom.FinitePresentation
        (Polynomial.eval₂RingHom φ x) :=
      RingHom.FinitePresentation.of_bijective ⟨hinj, hev⟩
    have hC : RingHom.FinitePresentation
        (Polynomial.C : R →+* Polynomial R) := by
      change RingHom.FinitePresentation (algebraMap R (Polynomial R))
      rw [RingHom.finitePresentation_algebraMap]
      infer_instance
    have hφfp : RingHom.FinitePresentation φ := by
      have := hEval.comp hC
      have heq : (Polynomial.eval₂RingHom φ x).comp
          (Polynomial.C : R →+* Polynomial R) = φ := by
        ext y
        simp
      rw [← heq]
      exact this
    exact ⟨1, one_ne_zero, 1, one_ne_zero,
      localizationAwayMulMap_one_finitePresentation_of_finitePresentation φ hφfp⟩

private theorem adjoin_insert_eval_surjective
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    (t : Finset S) (x : S)
    (hgen : Algebra.adjoin R (insert x (↑t : Set S)) = ⊤) :
    Function.Surjective
      (Polynomial.eval₂RingHom
        (algebraMap (Algebra.adjoin R (↑t : Set S)) S) x) := by
  let A := Algebra.adjoin R (↑t : Set S)
  have hgen' : Algebra.adjoin A ({x} : Set S) = ⊤ := by
    apply Algebra.eq_top_iff.2
    intro y
    have hy : y ∈ Algebra.adjoin R (insert x (↑t : Set S)) := by
      rw [hgen]
      exact Algebra.mem_top
    induction hy using Algebra.adjoin_induction with
    | mem y hy =>
        rcases hy with (rfl | hy)
        · exact Algebra.subset_adjoin (Set.mem_singleton y)
        · let ya : A := ⟨y, Algebra.subset_adjoin hy⟩
          simpa using Subalgebra.algebraMap_mem (Algebra.adjoin A ({x} : Set S)) ya
    | algebraMap r =>
        rw [IsScalarTower.algebraMap_apply R A S]
        exact Subalgebra.algebraMap_mem _ _
    | add y z _ _ hy hz =>
        exact Subalgebra.add_mem _ hy hz
    | mul y z _ _ hy hz =>
        exact Subalgebra.mul_mem _ hy hz
  have hsurj_aeval : Function.Surjective
      (Polynomial.aeval x : Polynomial A →ₐ[A] S) := by
    rw [← AlgHom.range_eq_top, ← Algebra.adjoin_singleton_eq_range_aeval A x]
    exact hgen'
  intro s
  obtain ⟨p, hp⟩ := hsurj_aeval s
  refine ⟨p, ?_⟩
  simpa [A, Polynomial.aeval_def] using hp
/-
  let A := Algebra.adjoin R (↑t : Set S)
  have hgen' : Algebra.adjoin A ({x} : Set S) = ⊤ := by
    apply Algebra.eq_top_iff.2
    intro y
    have hy : y ∈ Algebra.adjoin R (insert x (↑t : Set S)) := by
      rw [hgen]
      exact Algebra.mem_top
    induction hy using Algebra.adjoin_induction with
    | mem y hy =>
        rcases hy with (rfl | hy)
        · exact Algebra.subset_adjoin (Set.mem_singleton x)
        · let ya : A := ⟨y, Algebra.subset_adjoin hy⟩
          simpa using Subalgebra.algebraMap_mem (Algebra.adjoin A ({x} : Set S)) ya
    | algebraMap r =>
        rw [IsScalarTower.algebraMap_apply R A S]
        exact Subalgebra.algebraMap_mem _ _
    | add y z _ _ hy hz =>
        exact Subalgebra.add_mem _ hy hz
    | mul y z _ _ hy hz =>
        exact Subalgebra.mul_mem _ hy hz
  have hsurj_aeval : Function.Surjective
      (Polynomial.aeval x : Polynomial A →ₐ[A] S) := by
    rw [← AlgHom.range_eq_top, ← Algebra.adjoin_singleton_eq_range_aeval A x]
    exact hgen'
  simpa [Polynomial.aeval_def] using hsurj_aeval
-/

private theorem localizationAwayMulMap_comp_finitePresentation
    {R : Type u} {A S : Type v} [CommRing R] [CommRing A] [CommRing S]
    (φ : R →+* A) (ψ : A →+* S)
    (f : R) (g a : A) (b : S)
    (_hf : f ≠ 0) (_hg : g ≠ 0) (_ha : a ≠ 0) (_hb : b ≠ 0)
    (_hφ : Function.Injective φ) (_hψ : Function.Injective ψ)
    (h₁ : RingHom.FinitePresentation (localizationAwayMulMap φ f g))
    (h₂ : RingHom.FinitePresentation (localizationAwayMulMap ψ a b)) :
    RingHom.FinitePresentation
      (localizationAwayMulMap (ψ.comp φ) f (ψ a * b * ψ g)) := by
  let A₁ := Localization.Away (φ f * g)
  let T₁ := Localization.Away (algebraMap A A₁ a)
  have hA₁T₁ : RingHom.FinitePresentation (algebraMap A₁ T₁) := by
    rw [RingHom.finitePresentation_algebraMap]
    infer_instance
  have h₁' : RingHom.FinitePresentation
      ((algebraMap A₁ T₁).comp (localizationAwayMulMap φ f g)) :=
    hA₁T₁.comp h₁
  let A₂ := Localization.Away a
  let T₂ := Localization.Away (algebraMap A A₂ (φ f * g))
  let S₁ := Localization.Away (ψ a * b)
  let T₃ := Localization.Away
    ((localizationAwayMulMap ψ a b) (algebraMap A A₂ (φ f * g)))
  have h₂' : RingHom.FinitePresentation
      (IsLocalization.map T₃ (localizationAwayMulMap ψ a b)
        (Submonoid.powers (algebraMap A A₂ (φ f * g))).le_comap_map) :=
    RingHom.finitePresentation_localizationPreserves.away
      (localizationAwayMulMap ψ a b) (algebraMap A A₂ (φ f * g)) T₂ T₃ h₂
  let : SMul A A₁ := (inferInstance : Algebra A A₁).toSMul
  let : SMul A₁ T₁ := (inferInstance : Algebra A₁ T₁).toSMul
  let : Algebra A T₁ :=
    ((algebraMap A₁ T₁).comp (algebraMap A A₁)).toAlgebra
  let : SMul A T₁ := (inferInstance : Algebra A T₁).toSMul
  let : IsScalarTower A A₁ T₁ := IsScalarTower.of_algebraMap_eq' rfl
  let : SMul A A₂ := (inferInstance : Algebra A A₂).toSMul
  let : SMul A₂ T₂ := (inferInstance : Algebra A₂ T₂).toSMul
  let : Algebra A T₂ :=
    ((algebraMap A₂ T₂).comp (algebraMap A A₂)).toAlgebra
  let : SMul A T₂ := (inferInstance : Algebra A T₂).toSMul
  let : IsScalarTower A A₂ T₂ := IsScalarTower.of_algebraMap_eq' rfl
  let : IsLocalization.Away (a * (φ f * g)) T₁ :=
    IsLocalization.Away.mul A₁ T₁ (φ f * g) a
  let : IsLocalization.Away (a * (φ f * g)) T₂ :=
    IsLocalization.Away.mul' A₂ T₂ a (φ f * g)
  let e₁₂ : T₁ ≃ₐ[A] T₂ :=
    IsLocalization.algEquiv (Submonoid.powers (a * (φ f * g))) T₁ T₂
  have he₁₂ : RingHom.FinitePresentation (e₁₂ : T₁ →+* T₂) :=
    RingHom.FinitePresentation.of_bijective e₁₂.bijective
  let : SMul S S₁ := (inferInstance : Algebra S S₁).toSMul
  let : SMul S₁ T₃ := (inferInstance : Algebra S₁ T₃).toSMul
  let : Algebra S T₃ :=
    ((algebraMap S₁ T₃).comp (algebraMap S S₁)).toAlgebra
  let : SMul S T₃ := (inferInstance : Algebra S T₃).toSMul
  let : IsScalarTower S S₁ T₃ := IsScalarTower.of_algebraMap_eq' rfl
  have hT₃ : (localizationAwayMulMap ψ a b)
      (algebraMap A A₂ (φ f * g)) =
      algebraMap S S₁ (ψ (φ f * g)) := by
    have hψf : (localizationAwayMulMap ψ a b)
        (algebraMap A A₂ (φ f)) =
        algebraMap S (Localization.Away (ψ a * b)) (ψ (φ f)) := by
      unfold localizationAwayMulMap
      rw [IsLocalization.Away.lift_eq]
      simp only [RingHom.comp_apply]
    have hψg : (localizationAwayMulMap ψ a b)
        (algebraMap A A₂ g) =
        algebraMap S (Localization.Away (ψ a * b)) (ψ g) := by
      unfold localizationAwayMulMap
      rw [IsLocalization.Away.lift_eq]
      simp only [RingHom.comp_apply]
    rw [show algebraMap A A₂ (φ f * g) =
        algebraMap A A₂ (φ f) * algebraMap A A₂ g by rw [map_mul]]
    rw [map_mul, hψf, hψg, ψ.map_mul, ← map_mul]
  let : IsLocalization.Away
      (algebraMap S S₁ (ψ (φ f * g))) T₃ := by
    rw [← hT₃]
    infer_instance
  let : IsLocalization.Away
      ((ψ a * b) * ψ (φ f * g)) T₃ :=
    IsLocalization.Away.mul' S₁ T₃ (ψ a * b) (ψ (φ f * g))
  let P := Localization.Away ((ψ.comp φ) f * (ψ a * b * ψ g))
  let e₃ : T₃ ≃ₐ[S] P := by
    letI : IsLocalization.Away
        ((ψ.comp φ) f * (ψ a * b * ψ g)) T₃ := by
      simpa [P, mul_assoc, mul_comm, mul_left_comm, map_mul] using
        (inferInstance : IsLocalization.Away
          ((ψ a * b) * ψ (φ f * g)) T₃)
    exact IsLocalization.algEquiv
      (Submonoid.powers ((ψ.comp φ) f * (ψ a * b * ψ g))) T₃ P
  have he₃ : RingHom.FinitePresentation (e₃ : T₃ →+* P) :=
    RingHom.FinitePresentation.of_bijective e₃.bijective
  have hcomp : RingHom.FinitePresentation
      ((e₃ : T₃ →+* P).comp
      ((IsLocalization.map T₃ (localizationAwayMulMap ψ a b)
          (Submonoid.powers (algebraMap A A₂ (φ f * g))).le_comap_map).comp
          ((e₁₂ : T₁ →+* T₂).comp
            ((algebraMap A₁ T₁).comp (localizationAwayMulMap φ f g))))) :=
    he₃.comp (h₂'.comp (he₁₂.comp h₁'))
  have h₁base (x : R) :
      ((algebraMap A₁ T₁).comp (localizationAwayMulMap φ f g))
          (algebraMap R (Localization.Away f) x) =
        algebraMap A T₁ (φ x) := by
    have hx : (localizationAwayMulMap φ f g)
        (algebraMap R (Localization.Away f) x) =
        algebraMap A A₁ (φ x) := by
      unfold localizationAwayMulMap
      rw [IsLocalization.Away.lift_eq]
      simp only [RingHom.comp_apply]
      rfl
    rw [RingHom.comp_apply, hx]
    rw [← IsScalarTower.algebraMap_apply A A₁ T₁]
  have h₂base (x : A) :
      (IsLocalization.map T₃ (localizationAwayMulMap ψ a b)
        (Submonoid.powers (algebraMap A A₂ (φ f * g))).le_comap_map)
          (algebraMap A T₂ x) =
        algebraMap S T₃ (ψ x) := by
    have hx : (localizationAwayMulMap ψ a b)
        (algebraMap A A₂ x) =
        algebraMap S (Localization.Away (ψ a * b)) (ψ x) := by
      unfold localizationAwayMulMap
      rw [IsLocalization.Away.lift_eq]
      simp only [RingHom.comp_apply]
    rw [IsScalarTower.algebraMap_apply A A₂ T₂]
    rw [IsLocalization.map_eq, hx]
    change algebraMap S₁ T₃ (algebraMap S S₁ (ψ x)) =
      algebraMap S T₃ (ψ x)
    rw [← IsScalarTower.algebraMap_apply S S₁ T₃]
  have h₁₂base (x : A) :
      (e₁₂ : T₁ →+* T₂) (algebraMap A T₁ x) =
        algebraMap A T₂ x := e₁₂.commutes x
  have h₃base (x : S) :
      (e₃ : T₃ →+* P) (algebraMap S T₃ x) =
        algebraMap S P x := e₃.commutes x
  have heq : (e₃ : T₃ →+* P).comp
      ((IsLocalization.map T₃ (localizationAwayMulMap ψ a b)
        (Submonoid.powers (algebraMap A A₂ (φ f * g))).le_comap_map).comp
        ((e₁₂ : T₁ →+* T₂).comp
          ((algebraMap A₁ T₁).comp (localizationAwayMulMap φ f g)))) =
      localizationAwayMulMap (ψ.comp φ) f (ψ a * b * ψ g) := by
    apply IsLocalization.ringHom_ext (Submonoid.powers f)
    ext r
    simp only [RingHom.comp_apply]
    have hx₁ : (algebraMap A₁ T₁)
        ((localizationAwayMulMap φ f g)
          (algebraMap R (Localization.Away f) r)) =
        algebraMap A T₁ (φ r) := by
      change ((algebraMap A₁ T₁).comp (localizationAwayMulMap φ f g))
        (algebraMap R (Localization.Away f) r) = _
      exact h₁base r
    rw [hx₁, h₁₂base (φ r), h₂base (φ r), h₃base (ψ (φ r))]
    unfold localizationAwayMulMap
    rw [IsLocalization.Away.lift_eq]
    simp only [RingHom.comp_apply]
    rfl
  rw [← heq]
  exact hcomp

/-- A finite-type inclusion of domains becomes finitely presented after
localizing the source and target at suitable nonzero elements. -/
theorem exists_localization_away_finitePresentation
    {R S : Type*} [CommRing R] [CommRing S] [IsDomain R] [IsDomain S]
    (φ : R →+* S) (hφ : Function.Injective φ)
    (hft : RingHom.FiniteType φ) :
    ∃ f : R, f ≠ 0 ∧ ∃ g : S, g ≠ 0 ∧
      RingHom.FinitePresentation (localizationAwayMulMap φ f g) := by
  classical
  letI : Algebra R S := φ.toAlgebra
  change Algebra.FiniteType R S at hft
  have hφ' : Function.Injective (algebraMap R S) := hφ
  have aux : ∀ t : Finset S,
      ∃ f : R, f ≠ 0 ∧ ∃ g : Algebra.adjoin R (↑t : Set S), g ≠ 0 ∧
        RingHom.FinitePresentation
          (localizationAwayMulMap
            (algebraMap R (Algebra.adjoin R (↑t : Set S))) f g) := by
    intro t
    induction t using Finset.induction_on with
    | empty =>
        let A := Algebra.adjoin R (↑(∅ : Finset S) : Set S)
        have hA : A = ⊥ := by simp [A]
        have hinjA : Function.Injective (algebraMap R A) := by
          intro r s hrs
          apply hφ'
          have hrs' := congrArg (fun z : A => (z : S)) hrs
          simpa [A] using hrs'
        have hsurjA : Function.Surjective (algebraMap R A) := by
          intro y
          have hy : (y : S) ∈ (⊥ : Subalgebra R S) := by
            rw [← hA]
            exact y.property
          obtain ⟨r, hr⟩ := Algebra.mem_bot.mp hy
          refine ⟨r, ?_⟩
          apply Subtype.ext
          simpa [A] using hr
        have hfpA : RingHom.FinitePresentation (algebraMap R A) :=
          RingHom.FinitePresentation.of_bijective ⟨hinjA, hsurjA⟩
        simpa [A] using
          (show ∃ f : R, f ≠ 0 ∧ ∃ g : A, g ≠ 0 ∧
              RingHom.FinitePresentation
                (localizationAwayMulMap (algebraMap R A) f g) from
            ⟨1, one_ne_zero, 1, one_ne_zero,
              localizationAwayMulMap_one_finitePresentation_of_finitePresentation
                (algebraMap R A) hfpA⟩)
    | @insert x t hx ih =>
        let A := Algebra.adjoin R (↑t : Set S)
        let A' := Algebra.adjoin R (↑(insert x t) : Set S)
        have hA'eq : A' = Algebra.adjoin R (insert x (↑t : Set S)) := by
          apply SetLike.coe_injective
          ext y
          simp [A']
        have hAA' : A ≤ A' := by
          apply Algebra.adjoin_le
          intro y hy
          rw [hA'eq]
          exact Algebra.subset_adjoin (Or.inr hy)
        let ψ : A →+* A' := (Subalgebra.inclusion hAA').toRingHom
        letI : Algebra A A' := ψ.toAlgebra
        letI : IsScalarTower R A A' := IsScalarTower.of_algebraMap_eq' rfl
        let x' : A' := ⟨x, by rw [hA'eq]; exact Algebra.subset_adjoin (by simp)⟩
        have hψ : Function.Injective ψ := by
          exact Subalgebra.inclusion_injective hAA'
        have hpre : Algebra.adjoin R
            (((↑) : A' → S) ⁻¹' (insert x (↑t : Set S))) = ⊤ := by
          rw [hA'eq]
          exact Algebra.adjoin_adjoin_coe_preimage
        have hB : Subalgebra.restrictScalars R
            (Algebra.adjoin A ({x'} : Set A')) = ⊤ := by
          apply Algebra.eq_top_iff.2
          intro y
          have hy : y ∈ Algebra.adjoin R
              (((↑) : A' → S) ⁻¹' (insert x (↑t : Set S))) := by
            rw [hpre]
            exact Algebra.mem_top
          induction hy using Algebra.adjoin_induction with
          | mem z hz =>
              change (z : S) ∈ insert x (↑t : Set S) at hz
              rcases hz with (hz | hz)
              · have hzx : z = x' := by
                  apply Subtype.ext
                  exact hz
                rw [hzx]
                change x' ∈ Algebra.adjoin A ({x'} : Set A')
                exact Algebra.subset_adjoin (Set.mem_singleton x')
              · let za : A := ⟨z, Algebra.subset_adjoin hz⟩
                change z ∈ Algebra.adjoin A ({x'} : Set A')
                have hza : algebraMap A A' za = z := by
                  apply Subtype.ext
                  rfl
                rw [← hza]
                exact Subalgebra.algebraMap_mem _ za
          | algebraMap r =>
              change (algebraMap R A' r) ∈ Algebra.adjoin A ({x'} : Set A')
              rw [IsScalarTower.algebraMap_apply R A A']
              exact Subalgebra.algebraMap_mem _ _
          | add y z _ _ hy hz =>
              exact Subalgebra.add_mem _ hy hz
          | mul y z _ _ hy hz =>
              exact Subalgebra.mul_mem _ hy hz
        have hgenA : Algebra.adjoin A ({x'} : Set A') = ⊤ := by
          apply Subalgebra.restrictScalars_injective R
          rw [Subalgebra.restrictScalars_top]
          exact hB
        have hev : Function.Surjective
            (Polynomial.eval₂RingHom ψ x') := by
          have hsurj : Function.Surjective
              (Polynomial.aeval x' : Polynomial A →ₐ[A] A') := by
            rw [← AlgHom.range_eq_top, ← Algebra.adjoin_singleton_eq_range_aeval A x']
            exact hgenA
          intro y
          obtain ⟨p, hp⟩ := hsurj y
          refine ⟨p, ?_⟩
          have hψalg : ψ = (algebraMap A A' : A →+* A') := by rfl
          simpa [Polynomial.aeval_def, hψalg] using hp
        obtain ⟨f, hf, g, hg, h₁⟩ := ih
        obtain ⟨a, ha, b, hb, h₂⟩ :=
          one_generator_local_fp_general ψ hψ x' hev
        have hinjA : Function.Injective (algebraMap R A) := by
          intro r s hrs
          apply hφ'
          have hrs' := congrArg (fun z : A => (z : S)) hrs
          simpa [A] using hrs'
        have hcomp := localizationAwayMulMap_comp_finitePresentation
          (φ := algebraMap R A) (ψ := ψ) f g a b hf hg ha hb hinjA hψ h₁ h₂
        have hψcomp : ψ.comp (algebraMap R A) = algebraMap R A' := by
          ext r
          rfl
        have hψa : ψ a ≠ 0 := by
          intro h
          apply ha
          exact hψ (by simpa using h)
        have hψg : ψ g ≠ 0 := by
          intro h
          apply hg
          exact hψ (by simpa using h)
        have hnonzero : ψ a * b * ψ g ≠ 0 :=
          mul_ne_zero (mul_ne_zero hψa hb) hψg
        refine ⟨f, hf, ψ a * b * ψ g, hnonzero, ?_⟩
        change RingHom.FinitePresentation
          (localizationAwayMulMap (algebraMap R A') f (ψ a * b * ψ g))
        rw [← hψcomp]
        exact hcomp
  obtain ⟨n, q, hq⟩ :=
    (Algebra.FiniteType.iff_quotient_mvPolynomial'').mp hft
  let v : Fin n → S := fun i => q (MvPolynomial.X i)
  have hqv : MvPolynomial.aeval v = q := by
    ext p
    simp [v]
  let t : Finset S := Finset.univ.image v
  have ht : Algebra.adjoin R (↑t : Set S) = ⊤ := by
    have hset : (↑t : Set S) = Set.range v := by
      ext y
      constructor
      · intro hy
        rcases Finset.mem_image.mp hy with ⟨i, -, rfl⟩
        exact ⟨i, rfl⟩
      · rintro ⟨i, rfl⟩
        exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
    rw [hset, Algebra.adjoin_range_eq_range_aeval]
    rw [hqv]
    rw [AlgHom.range_eq_top]
    exact hq
  obtain ⟨f, hf, g, hg, hfp⟩ := aux t
  let A := Algebra.adjoin R (↑t : Set S)
  let e : A ≃ₐ[R] S :=
    (Subalgebra.equivOfEq A (⊤ : Subalgebra R S) ht).trans
      (Subalgebra.topEquiv : (⊤ : Subalgebra R S) ≃ₐ[R] S)
  have heq : (e : A →+* S).comp (algebraMap R A) = φ := by
    ext r
    change e (algebraMap R A r) = φ r
    rw [e.commutes]
    rfl
  have hefp : RingHom.FinitePresentation (e : A →+* S) :=
    RingHom.FinitePresentation.of_bijective e.bijective
  have h₂ : RingHom.FinitePresentation
      (localizationAwayMulMap (e : A →+* S) 1 1) :=
    localizationAwayMulMap_one_finitePresentation_of_finitePresentation
      (e : A →+* S) hefp
  have hinjA : Function.Injective (algebraMap R A) := by
    intro r s hrs
    apply hφ'
    have hrs' := congrArg (fun z : A => (z : S)) hrs
    simpa [A] using hrs'
  have hcomp := localizationAwayMulMap_comp_finitePresentation
    (φ := algebraMap R A) (ψ := (e : A →+* S)) f g 1 1 hf hg one_ne_zero one_ne_zero
    hinjA e.injective hfp h₂
  refine ⟨f, hf, e g, ?_, ?_⟩
  · intro h
    apply hg
    exact e.injective (by simpa using h)
  · rw [heq] at hcomp
    have hden : (e : A →+* S) 1 * 1 * (e : A →+* S) g = e g := by
      rw [map_one]
      simp
    rw [hden] at hcomp
    exact hcomp

/- The quotient/localization square in the source proof is proof scaffolding:
the canonical quotient spectra and `PrimeSpectrum.comap` already provide its
four arrows.  The theorem below records the resulting relative open-dense
statement directly. -/
/- The displayed polynomial relation in the source's proof of the last lemma
is likewise an argument for the theorem, not an additional chapter-level
interface. -/

/- A constructible image of a finite-type map contains a relatively open dense
subset of the closure of every point it contains. -/
theorem image_constructible_contains_open_dense_subset_of_finiteType
    {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S)
    (hφ : RingHom.FiniteType φ) {E : Set (PrimeSpectrum S)}
    (hE : IsConstructible E) {ξ : PrimeSpectrum R}
    (hξ : ξ ∈ PrimeSpectrum.comap φ '' E) :
    ∃ U : Set (closure ({ξ} : Set (PrimeSpectrum R))),
      IsOpen U ∧ Dense U ∧
        (U : Set (PrimeSpectrum R)) ⊆ PrimeSpectrum.comap φ '' E := by
  rcases hξ with ⟨η, hηE, rfl⟩
  let p : Ideal R := Ideal.comap φ η.asIdeal
  let q : Ideal S := η.asIdeal
  let ψ : R ⧸ p →+* S ⧸ q := Ideal.quotientMap q φ (by
    dsimp [p, q]
    exact le_rfl)
  have hψinj : Function.Injective ψ := by
    apply Ideal.quotientMap_injective
  letI : Algebra (R ⧸ p) (S ⧸ q) := ψ.toAlgebra
  have hft' : Algebra.FiniteType (R ⧸ p) (S ⧸ q) := by
    letI : Algebra R S := φ.toAlgebra
    change Algebra.FiniteType R S at hφ
    obtain ⟨n, t, qgen, hqgen⟩ := Algebra.FiniteType.iff_exists_generators.mp hφ
    let qmk : S →+* S ⧸ q := Ideal.Quotient.mk q
    let t' : Fin n → S ⧸ q := fun i => qmk (t i)
    have hmap_eval (P : MvPolynomial (Fin n) R) :
        qmk (MvPolynomial.aeval t P) =
          MvPolynomial.aeval t' (MvPolynomial.map (Ideal.Quotient.mk p) P) := by
      let lhs : MvPolynomial (Fin n) R →+* (S ⧸ q) :=
        qmk.comp (MvPolynomial.aeval t).toRingHom
      let rhs : MvPolynomial (Fin n) R →+* (S ⧸ q) :=
        (MvPolynomial.aeval t').toRingHom.comp
          (MvPolynomial.map (Ideal.Quotient.mk p))
      have heq : lhs = rhs := by
        apply MvPolynomial.ringHom_ext
        · intro r
          simp [lhs, rhs]
          rw [show algebraMap R S r = φ r by rfl]
          rfl
        · intro i
          simp [lhs, rhs, t']
      exact congrArg (fun f : MvPolynomial (Fin n) R →+* (S ⧸ q) => f P) heq
    let lift : (S ⧸ q) → S := fun y => Classical.choose (Ideal.Quotient.mk_surjective y)
    have hlift (y : S ⧸ q) : qmk (lift y) = y :=
      Classical.choose_spec (Ideal.Quotient.mk_surjective y)
    let qbar : (S ⧸ q) → MvPolynomial (Fin n) (R ⧸ p) :=
      fun y => MvPolynomial.map (Ideal.Quotient.mk p) (qgen (lift y))
    have hqbar (y : S ⧸ q) :
        MvPolynomial.aeval t' (qbar y) = y := by
      dsimp [qbar]
      rw [← hmap_eval, hqgen, hlift]
    have hsurj : Function.Surjective
        (MvPolynomial.aeval t' :
          MvPolynomial (Fin n) (R ⧸ p) →ₐ[R ⧸ p] (S ⧸ q)) := by
      intro y
      exact ⟨qbar y, hqbar y⟩
    exact Algebra.FiniteType.iff_exists_generators.mpr
      ⟨n, ⟨Algebra.Generators.ofAlgHom _ hsurj⟩⟩
  change RingHom.FiniteType ψ at hft'
  have hqprime : q.IsPrime := by
    dsimp [q]
    exact η.isPrime
  letI : q.IsPrime := hqprime
  have hpprime : p.IsPrime := by
    dsimp [p]
    exact Ideal.comap_isPrime φ q
  letI : p.IsPrime := hpprime
  let Ebar : Set (PrimeSpectrum (S ⧸ q)) :=
    PrimeSpectrum.comap (Ideal.Quotient.mk q) ⁻¹' E
  have hEbar : IsConstructible Ebar := by
    exact (Formalization.Books.Algebra.Unit29.affine_map_quasiCompact_and_constructible_preimage
      (Ideal.Quotient.mk q)).2 E hE
  let ηbar : PrimeSpectrum (S ⧸ q) := ⟨⊥, inferInstance⟩
  have hηbar : PrimeSpectrum.comap (Ideal.Quotient.mk q) ηbar = η := by
    apply PrimeSpectrum.ext
    change Ideal.comap (Ideal.Quotient.mk q) (⊥ : Ideal (S ⧸ q)) = q
    rw [← RingHom.ker_eq_comap_bot]
    exact q.mk_ker
  have hηbarE : ηbar ∈ Ebar := by
    change PrimeSpectrum.comap (Ideal.Quotient.mk q) ηbar ∈ E
    rw [hηbar]
    exact hηE
  obtain ⟨f, hf, g, hg, hfp⟩ :=
    exists_localization_away_finitePresentation ψ hψinj hft'
  have hψf : ψ f ≠ 0 := by
    intro h
    apply hf
    exact hψinj (by simpa using h)
  have hden : ψ f * g ≠ 0 := mul_ne_zero hψf hg
  letI : IsDomain (Localization.Away f) :=
    @Localization.Away.isDomain (R ⧸ p) _ inferInstance f hf
  letI : IsDomain (Localization.Away (ψ f * g)) :=
    @Localization.Away.isDomain (S ⧸ q) _ inferInstance (ψ f * g) hden
  let Efg : Set (PrimeSpectrum (Localization.Away (ψ f * g))) :=
    PrimeSpectrum.comap
      (algebraMap (S ⧸ q) (Localization.Away (ψ f * g))) ⁻¹' Ebar
  have hEfg : IsConstructible Efg := by
    exact (Formalization.Books.Algebra.Unit29.affine_map_quasiCompact_and_constructible_preimage
      (algebraMap (S ⧸ q) (Localization.Away (ψ f * g)))).2 Ebar hEbar
  have hI : IsConstructible
      (PrimeSpectrum.comap (localizationAwayMulMap ψ f g) '' Efg) := by
    exact PrimeSpectrum.isConstructible_comap_image hfp hEfg
  have hRf : Function.Injective
      (algebraMap (R ⧸ p) (Localization.Away f)) :=
    IsLocalization.injective (Localization.Away f)
      (@powers_le_nonZeroDivisors_of_noZeroDivisors (R ⧸ p) _ f
        (@IsDomain.to_noZeroDivisors (R ⧸ p) _ inferInstance) hf)
  have hB : Function.Injective
      (algebraMap (S ⧸ q) (Localization.Away (ψ f * g))) :=
    IsLocalization.injective (Localization.Away (ψ f * g))
      (@powers_le_nonZeroDivisors_of_noZeroDivisors (S ⧸ q) _ (ψ f * g)
        (@IsDomain.to_noZeroDivisors (S ⧸ q) _ inferInstance) hden)
  have hmapinj : Function.Injective (localizationAwayMulMap ψ f g) := by
    unfold localizationAwayMulMap Localization.awayLift IsLocalization.Away.lift
    rw [IsLocalization.lift_injective_iff]
    intro a b
    constructor
    · intro hab
      have hab' : a = b := hRf hab
      simpa [hab']
    · intro hab
      have hab' : a = b := hψinj (hB hab)
      exact congrArg (algebraMap (R ⧸ p) (Localization.Away f)) hab'
  let r0 : PrimeSpectrum (Localization.Away f) := ⟨⊥, inferInstance⟩
  let s0 : PrimeSpectrum (Localization.Away (ψ f * g)) := ⟨⊥, inferInstance⟩
  have hs0 : PrimeSpectrum.comap
      (algebraMap (S ⧸ q) (Localization.Away (ψ f * g))) s0 = ηbar := by
    apply PrimeSpectrum.ext
    change Ideal.comap
        (algebraMap (S ⧸ q) (Localization.Away (ψ f * g)))
        (⊥ : Ideal (Localization.Away (ψ f * g))) = ⊥
    exact Ideal.comap_bot_of_injective _ hB
  have hs0E : s0 ∈ Efg := by
    change PrimeSpectrum.comap
        (algebraMap (S ⧸ q) (Localization.Away (ψ f * g))) s0 ∈ Ebar
    rw [hs0]
    exact hηbarE
  have hr0 : r0 ∈ PrimeSpectrum.comap
      (localizationAwayMulMap ψ f g) '' Efg := by
    refine ⟨s0, hs0E, ?_⟩
    apply PrimeSpectrum.ext
    change Ideal.comap (localizationAwayMulMap ψ f g)
        (⊥ : Ideal (Localization.Away (ψ f * g))) = ⊥
    exact Ideal.comap_bot_of_injective _ hmapinj
  have hr0closure : closure ({r0} : Set (PrimeSpectrum (Localization.Away f))) = Set.univ := by
    rw [PrimeSpectrum.closure_singleton]
    change PrimeSpectrum.zeroLocus (r0.asIdeal : Set (Localization.Away f)) = Set.univ
    change PrimeSpectrum.zeroLocus
        (↑(⊥ : Ideal (Localization.Away f)) : Set (Localization.Away f)) = Set.univ
    exact PrimeSpectrum.zeroLocus_bot
  have hIclosure : closure
      (PrimeSpectrum.comap (localizationAwayMulMap ψ f g) '' Efg) = Set.univ := by
    apply Set.Subset.antisymm le_top
    calc
      (Set.univ : Set (PrimeSpectrum (Localization.Away f))) =
          closure ({r0} : Set (PrimeSpectrum (Localization.Away f))) :=
        hr0closure.symm
      _ ⊆ closure (PrimeSpectrum.comap (localizationAwayMulMap ψ f g) '' Efg) :=
        closure_mono (singleton_subset_iff.mpr hr0)
  obtain ⟨W, hWopen, hWdense, hWsub⟩ :=
    Formalization.Books.Topology.Unit21.exists_dense_open_subset_of_closure_of_isConstructible hI
  let eUniv : (Set.univ : Set (PrimeSpectrum (Localization.Away f))) ≃ₜ
      PrimeSpectrum (Localization.Away f) :=
    { toFun := Subtype.val
      invFun := fun x => ⟨x, Set.mem_univ x⟩
      left_inv := by intro x; rfl
      right_inv := by intro x; rfl
      continuous_toFun := continuous_subtype_val
      continuous_invFun := by
        apply Continuous.subtype_mk
        exact continuous_id }
  let eI : closure (PrimeSpectrum.comap (localizationAwayMulMap ψ f g) '' Efg) ≃ₜ
      PrimeSpectrum (Localization.Away f) :=
    (Homeomorph.setCongr hIclosure).trans eUniv
  let V0 : Set (PrimeSpectrum (Localization.Away f)) := eI '' W
  have hV0open : IsOpen V0 := eI.isOpenMap W hWopen
  have hV0dense : Dense V0 := by
    rw [dense_iff_inter_open] at hWdense ⊢
    intro O hO hOne
    have hpreopen : IsOpen (eI ⁻¹' O) := hO.preimage eI.continuous
    have hprene : (eI ⁻¹' O).Nonempty := by
      rcases hOne with ⟨y, hy⟩
      exact ⟨eI.symm y, by simpa using hy⟩
    obtain ⟨x, hxpre, hxW⟩ := hWdense _ hpreopen hprene
    exact ⟨eI x, hxpre, ⟨x, hxW, rfl⟩⟩
  let eR :=
    Formalization.Books.Algebra.Unit17.standardOpenSpectrumHomeomorph f
  let Vsub : Set {r : PrimeSpectrum (R ⧸ p) //
      r ∈ (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum (R ⧸ p)))} := eR '' V0
  have hVsubopen : IsOpen Vsub := eR.isOpenMap V0 hV0open
  have hVsubdense : Dense Vsub := by
    rw [dense_iff_inter_open] at hV0dense ⊢
    intro O hO hOne
    have hpreopen : IsOpen (eR ⁻¹' O) := hO.preimage eR.continuous
    have hprene : (eR ⁻¹' O).Nonempty := by
      rcases hOne with ⟨y, hy⟩
      exact ⟨eR.symm y, by simpa using hy⟩
    obtain ⟨x, hxpre, hxV⟩ := hV0dense _ hpreopen hprene
    exact ⟨eR x, hxpre, ⟨x, hxV, rfl⟩⟩
  let rb0 : PrimeSpectrum (R ⧸ p) := ⟨⊥, inferInstance⟩
  have hrb0closure : closure ({rb0} : Set (PrimeSpectrum (R ⧸ p))) = Set.univ := by
    rw [PrimeSpectrum.closure_singleton]
    change PrimeSpectrum.zeroLocus
        (↑(⊥ : Ideal (R ⧸ p)) : Set (R ⧸ p)) = Set.univ
    exact PrimeSpectrum.zeroLocus_bot
  have hrb0basic : rb0 ∈
      (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum (R ⧸ p))) := by
    apply (PrimeSpectrum.mem_basicOpen f rb0).2
    simpa [rb0] using hf
  have hbasicdense : Dense
      (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum (R ⧸ p))) := by
    have hzero : Dense ({rb0} : Set (PrimeSpectrum (R ⧸ p))) := by
      rw [dense_iff_closure_eq]
      exact hrb0closure
    exact hzero.mono (singleton_subset_iff.mpr hrb0basic)
  let Vbar : Set (PrimeSpectrum (R ⧸ p)) := Subtype.val '' Vsub
  have hVbaropen : IsOpen Vbar := by
    exact (PrimeSpectrum.isOpen_basicOpen.isOpenEmbedding_subtypeVal.isOpen_iff_image_isOpen).mp
      hVsubopen
  have hVbardense : Dense Vbar := by
    rw [dense_iff_inter_open] at hVsubdense ⊢
    intro O hO hOne
    have hOD : (O ∩ (PrimeSpectrum.basicOpen f :
        Set (PrimeSpectrum (R ⧸ p)))).Nonempty := by
      exact (dense_iff_inter_open.mp hbasicdense) O hO hOne
    rcases hOD with ⟨y, hyO, hybasic⟩
    let Osub : Set {r : PrimeSpectrum (R ⧸ p) //
        r ∈ (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum (R ⧸ p)))} :=
      Subtype.val ⁻¹' O
    have hOsub : IsOpen Osub := hO.preimage continuous_subtype_val
    have hOsubprene : Osub.Nonempty := by
      exact ⟨⟨y, hybasic⟩, hyO⟩
    have hinter : (Osub ∩ Vsub).Nonempty :=
      hVsubdense (U := Osub) hOsub hOsubprene
    obtain ⟨x, hxpre, hxV⟩ := hinter
    exact ⟨(x : PrimeSpectrum (R ⧸ p)), hxpre, ⟨x, hxV, rfl⟩⟩
  have hbase :
      (algebraMap (S ⧸ q) (Localization.Away (ψ f * g))).comp ψ =
        (localizationAwayMulMap ψ f g).comp
          (algebraMap (R ⧸ p) (Localization.Away f)) := by
    ext a
    simp only [RingHom.comp_apply]
    unfold localizationAwayMulMap
    rw [IsLocalization.Away.lift_eq]
    simp [RingHom.comp_apply]
  have hquot :
      (Ideal.Quotient.mk q).comp φ = ψ.comp (Ideal.Quotient.mk p) := by
    ext r
    rfl
  have hξclosure :
      closure ({PrimeSpectrum.comap φ η} : Set (PrimeSpectrum R)) =
        PrimeSpectrum.zeroLocus (p : Set R) := by
    rw [PrimeSpectrum.closure_singleton]
    simp [p]
  let eQ := Formalization.Books.Algebra.Unit17.quotientSpectrumHomeomorph p
  let eQ' : PrimeSpectrum (R ⧸ p) ≃ₜ
      closure ({PrimeSpectrum.comap φ η} : Set (PrimeSpectrum R)) :=
    eQ.trans (Homeomorph.setCongr hξclosure.symm)
  let U : Set (closure ({PrimeSpectrum.comap φ η} : Set (PrimeSpectrum R))) :=
    eQ' '' Vbar
  have hUopen : IsOpen U := eQ'.isOpenMap Vbar hVbaropen
  have hUdense : Dense U := by
    rw [dense_iff_inter_open] at hVbardense ⊢
    intro O hO hOne
    have hpreopen : IsOpen (eQ' ⁻¹' O) := hO.preimage eQ'.continuous
    have hprene : (eQ' ⁻¹' O).Nonempty := by
      rcases hOne with ⟨y, hy⟩
      exact ⟨eQ'.symm y, by simpa using hy⟩
    have hinter : ((eQ' ⁻¹' O) ∩ Vbar).Nonempty :=
      hVbardense (U := eQ' ⁻¹' O) hpreopen hprene
    obtain ⟨y, hyO, hyV⟩ := hinter
    exact ⟨eQ' y, hyO, ⟨y, hyV, rfl⟩⟩
  have heIval (w : closure
      (PrimeSpectrum.comap (localizationAwayMulMap ψ f g) '' Efg)) :
      eI w = (w : PrimeSpectrum (Localization.Away f)) := by
    rfl
  have heRval (x : PrimeSpectrum (Localization.Away f)) :
      (eR x : PrimeSpectrum (R ⧸ p)) =
        PrimeSpectrum.comap (algebraMap (R ⧸ p) (Localization.Away f)) x := by
    rw [Formalization.Books.Algebra.Unit17.standardOpenSpectrumHomeomorph_apply]
  have heQval (y : PrimeSpectrum (R ⧸ p)) :
      ((eQ' y : closure ({PrimeSpectrum.comap φ η} : Set (PrimeSpectrum R))) :
        PrimeSpectrum R) = PrimeSpectrum.comap (Ideal.Quotient.mk p) y := by
    change ((eQ y : {r : PrimeSpectrum R //
      r ∈ PrimeSpectrum.zeroLocus (p : Set R)}) : PrimeSpectrum R) = _
    rw [Formalization.Books.Algebra.Unit17.quotientSpectrumHomeomorph_apply]
  have hcomp' :
      ((algebraMap (S ⧸ q) (Localization.Away (ψ f * g))).comp
        (Ideal.Quotient.mk q)).comp φ =
        ((localizationAwayMulMap ψ f g).comp
          (algebraMap (R ⧸ p) (Localization.Away f))).comp
            (Ideal.Quotient.mk p) := by
    ext r
    simp only [RingHom.comp_apply]
    have hq := congrArg (fun F : R →+* (S ⧸ q) => F r) hquot
    have hb := congrArg
      (fun F : (R ⧸ p) →+* Localization.Away (ψ f * g) =>
        F (Ideal.Quotient.mk p r)) hbase
    change (algebraMap (S ⧸ q) (Localization.Away (ψ f * g)))
        ((Ideal.Quotient.mk q).comp φ r) = _
    rw [hq]
    exact hb
  refine ⟨U, hUopen, hUdense, ?_⟩
  rintro z ⟨u, huU, rfl⟩
  rcases huU with ⟨y, hyV, rfl⟩
  rcases hyV with ⟨y', hyVsub, rfl⟩
  rcases hyVsub with ⟨x, hxV0, rfl⟩
  rcases hxV0 with ⟨w, hwW, rfl⟩
  have hwI : (w : PrimeSpectrum (Localization.Away f)) ∈
      PrimeSpectrum.comap (localizationAwayMulMap ψ f g) '' Efg :=
    hWsub ⟨w, hwW, rfl⟩
  rcases hwI with ⟨s, hs, hws⟩
  have hsE : PrimeSpectrum.comap (Ideal.Quotient.mk q)
      (PrimeSpectrum.comap
        (algebraMap (S ⧸ q) (Localization.Away (ψ f * g))) s) ∈ E := by
    change PrimeSpectrum.comap
        (algebraMap (S ⧸ q) (Localization.Away (ψ f * g))) s ∈ Ebar at hs
    exact hs
  refine ⟨PrimeSpectrum.comap (Ideal.Quotient.mk q)
      (PrimeSpectrum.comap
        (algebraMap (S ⧸ q) (Localization.Away (ψ f * g))) s), hsE, ?_⟩
  have hpoint :
      PrimeSpectrum.comap (Ideal.Quotient.mk p)
          (PrimeSpectrum.comap (algebraMap (R ⧸ p) (Localization.Away f))
            (PrimeSpectrum.comap (localizationAwayMulMap ψ f g) s)) =
        PrimeSpectrum.comap φ
          (PrimeSpectrum.comap (Ideal.Quotient.mk q)
            (PrimeSpectrum.comap
              (algebraMap (S ⧸ q) (Localization.Away (ψ f * g))) s)) := by
    apply PrimeSpectrum.ext
    ext r
    have hr := congrArg (fun F : R →+* Localization.Away (ψ f * g) =>
      F r) hcomp'
    simpa [PrimeSpectrum.comap_asIdeal, RingHom.comp_apply] using
      (congrArg (fun z => z ∈ s.asIdeal) hr).symm
  rw [heQval]
  rw [heRval (eI w), heIval w, ← hws]
  exact hpoint.symm

/-! ## Surjectivity on spectra and radical ideals -/

/- The four conditions in the source are stated as a single `List.TFAE`, so
the ideal-map/comap directions and the prime-spectrum range are visible in
one reusable interface. -/
theorem spectrum_surjective_radical_ideal_conditions
    {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) :
    List.TFAE
      [ Function.Surjective (PrimeSpectrum.comap φ),
        ∀ I : Ideal R,
          Ideal.comap φ (I.map φ).radical = I.radical,
        ∀ I : Ideal R, I.IsRadical →
          Ideal.comap φ (I.map φ) = I,
      ∀ p : PrimeSpectrum R,
          Ideal.comap φ (p.asIdeal.map φ) = p.asIdeal ] := by
  rw [List.tfae_cons_cons]
  refine ⟨?_, ?_⟩
  · constructor
    · intro h I
      rw [Ideal.comap_radical]
      have hle : Ideal.comap φ (I.map φ) ≤ I.radical := by
        rw [Ideal.radical_eq_sInf]
        refine le_sInf ?_
        intro p hp
        let _ : p.IsPrime := hp.2
        have hprime : Ideal.comap φ (p.map φ) = p := by
          obtain ⟨q, hq⟩ := h ⟨p, hp.2⟩
          rw [Ideal.comap_map_eq_self_iff_of_isPrime]
          refine ⟨q.asIdeal, q.isPrime, ?_⟩
          simpa using congrArg PrimeSpectrum.asIdeal hq
        have hle' : Ideal.comap φ (I.map φ) ≤ Ideal.comap φ (p.map φ) :=
          Ideal.comap_mono (Ideal.map_mono hp.1)
        rw [hprime] at hle'
        exact hle'
      apply le_antisymm
      · simpa using Ideal.radical_mono hle
      · exact Ideal.radical_mono Ideal.le_comap_map
    · intro h p
      apply (PrimeSpectrum.mem_range_comap_iff φ).mpr
      apply le_antisymm
      · calc
          Ideal.comap φ (p.asIdeal.map φ) ≤
              Ideal.comap φ (p.asIdeal.map φ).radical :=
            Ideal.comap_mono Ideal.le_radical
          _ = p.asIdeal.radical := h p.asIdeal
          _ = p.asIdeal := p.isPrime.radical
      · exact Ideal.le_comap_map
  · rw [List.tfae_cons_cons]
    refine ⟨?_, ?_⟩
    · constructor
      · intro h I hI
        apply le_antisymm
        · calc
            Ideal.comap φ (I.map φ) ≤
                Ideal.comap φ (I.map φ).radical :=
              Ideal.comap_mono Ideal.le_radical
            _ = I.radical := h I
            _ = I := hI.radical
        · exact Ideal.le_comap_map
      · intro h I
        have hupper : Ideal.comap φ (I.map φ) ≤ I.radical := by
          calc
            Ideal.comap φ (I.map φ) ≤
                Ideal.comap φ ((I.radical).map φ) :=
              Ideal.comap_mono (Ideal.map_mono Ideal.le_radical)
            _ = I.radical := h I.radical (Ideal.radical_isRadical I)
        have heq : (Ideal.comap φ (I.map φ)).radical = I.radical := by
          apply le_antisymm
          · simpa using Ideal.radical_mono hupper
          · exact Ideal.radical_mono Ideal.le_comap_map
        rw [Ideal.comap_radical]
        exact heq
    · rw [List.tfae_cons_cons]
      refine ⟨?_, ?_⟩
      · constructor
        · intro h p
          exact h p.asIdeal p.isPrime.isRadical
        · intro h I hI
          apply le_antisymm
          · have hle : Ideal.comap φ (I.map φ) ≤
                sInf {J : Ideal R | I ≤ J ∧ J.IsPrime} := by
              refine le_sInf ?_
              intro p hp
              have hle' : Ideal.comap φ (I.map φ) ≤ Ideal.comap φ (p.map φ) :=
                Ideal.comap_mono (Ideal.map_mono hp.1)
              simpa using hle'.trans_eq (h ⟨p, hp.2⟩)
            calc
              Ideal.comap φ (I.map φ) ≤ I.radical := by
                rw [Ideal.radical_eq_sInf]
                exact hle
              _ = I := hI.radical
          · exact Ideal.le_comap_map
      · exact List.tfae_singleton _

/- The source's base-change clause asserts preservation of the first three
conditions.  The tensor product uses the algebra structures induced by the
two displayed ring maps. -/
theorem spectrum_surjective_radical_ideal_conditions_baseChange
    {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S)
    (hφ : Function.Surjective (PrimeSpectrum.comap φ))
    {R' : Type*} [CommRing R'] (ψ : R →+* R') :
    letI : Algebra R S := φ.toAlgebra
    letI : Algebra R R' := ψ.toAlgebra
    List.TFAE
      [ Function.Surjective
          (PrimeSpectrum.comap (algebraMap R' (R' ⊗[R] S))),
        ∀ I : Ideal R',
          Ideal.comap (algebraMap R' (R' ⊗[R] S))
            (I.map (algebraMap R' (R' ⊗[R] S))).radical = I.radical,
        ∀ I : Ideal R', I.IsRadical →
          Ideal.comap (algebraMap R' (R' ⊗[R] S))
            (I.map (algebraMap R' (R' ⊗[R] S))) = I ] ∧
      Function.Surjective
        (PrimeSpectrum.comap (algebraMap R' (R' ⊗[R] S))) := by
  let solve : ∀ [algS : Algebra R S] [algR' : Algebra R R'],
      algS = φ.toAlgebra → algR' = ψ.toAlgebra →
      List.TFAE
        [ Function.Surjective
            (PrimeSpectrum.comap (algebraMap R' (R' ⊗[R] S))),
          ∀ I : Ideal R',
            Ideal.comap (algebraMap R' (R' ⊗[R] S))
              (I.map (algebraMap R' (R' ⊗[R] S))).radical = I.radical,
          ∀ I : Ideal R', I.IsRadical →
            Ideal.comap (algebraMap R' (R' ⊗[R] S))
              (I.map (algebraMap R' (R' ⊗[R] S))) = I ] ∧
        Function.Surjective
          (PrimeSpectrum.comap (algebraMap R' (R' ⊗[R] S))) := by
    intro algS algR' halgS halgR'
    have hmapS : (algebraMap R S : R →+* S) = φ := by
      calc
        algebraMap R S =
            @algebraMap R S _ _ (φ.toAlgebra) :=
          congrArg (fun a : Algebra R S => @algebraMap R S _ _ a) halgS
        _ = φ := RingHom.algebraMap_toAlgebra φ
    have hmapR' : (algebraMap R R' : R →+* R') = ψ := by
      calc
        algebraMap R R' =
            @algebraMap R R' _ _ (ψ.toAlgebra) :=
          congrArg (fun a : Algebra R R' => @algebraMap R R' _ _ a) halgR'
        _ = ψ := RingHom.algebraMap_toAlgebra ψ
    rw [List.tfae_cons_cons]
    refine ⟨?_, ?_⟩
    · have hT := spectrum_surjective_radical_ideal_conditions
        (algebraMap R' (R' ⊗[R] S))
      rw [List.tfae_cons_cons] at hT
      rw [List.tfae_cons_cons] at hT
      rw [List.tfae_cons_cons]
      exact ⟨hT.1, ⟨hT.2.1, List.tfae_singleton _⟩⟩
    · intro p'
      apply (PrimeSpectrum.nontrivial_iff_mem_rangeComap p').mp
      let p := PrimeSpectrum.comap ψ p'
      obtain ⟨q, hq⟩ := hφ p
      have hf : p.asIdeal = q.asIdeal.comap φ := by
        simpa [p] using congrArg PrimeSpectrum.asIdeal hq.symm
      have hfiber : Nontrivial (p.asIdeal.ResidueField ⊗[R] S) := by
        apply (PrimeSpectrum.nontrivial_iff_mem_rangeComap p).mpr
        have hrange : p ∈ Set.range (PrimeSpectrum.comap φ) := ⟨q, hq⟩
        simpa [hmapS] using hrange
      let k := p.asIdeal.ResidueField
      let K := p'.asIdeal.ResidueField
      have hfp : p.asIdeal = p'.asIdeal.comap ψ := by
        rfl
      let kmap := Ideal.ResidueField.map p.asIdeal p'.asIdeal ψ hfp
      let algRK := ((algebraMap R' K).comp ψ).toAlgebra
      let hKK :=
        (letI : Algebra R K := algRK
         letI : Algebra k K := kmap.toAlgebra
         letI : IsScalarTower R k K :=
           IsScalarTower.of_algebraMap_eq' (by
             ext r
             change algebraMap R' K (ψ r) = kmap (algebraMap R k r)
             symm
             exact Ideal.ResidueField.map_algebraMap p.asIdeal p'.asIdeal ψ hfp r)
         (Module.FaithfullyFlat.nontrivial_tensorProduct_iff_right
           (R := k) (M := K) (N := k ⊗[R] S)).mpr hfiber)
      let e1 :=
        (letI : Algebra R K := algRK
         letI : Algebra k K := kmap.toAlgebra
         letI : IsScalarTower R k K :=
           IsScalarTower.of_algebraMap_eq' (by
             ext r
             change algebraMap R' K (ψ r) = kmap (algebraMap R k r)
             symm
             exact Ideal.ResidueField.map_algebraMap p.asIdeal p'.asIdeal ψ hfp r)
         Algebra.TensorProduct.cancelBaseChange R k K K S)
      let e2 :=
        (letI : Algebra R K := algRK
         letI : IsScalarTower R R' K :=
           IsScalarTower.of_algebraMap_eq' (by
             ext r
             dsimp [algRK]
             rw [RingHom.algebraMap_toAlgebra, hmapR']
             simp [RingHom.comp_apply])
         Algebra.TensorProduct.cancelBaseChange R R' K K S)
      obtain ⟨x, y, hxy⟩ := hKK.exists_pair_ne
      refine ⟨e2.symm (e1 x), e2.symm (e1 y), ?_⟩
      intro heq
      apply hxy
      apply e1.injective
      exact e2.symm.injective heq
  exact @solve (φ.toAlgebra) (ψ.toAlgebra) rfl rfl

/-! ## Dense images and minimal primes -/

/- `DenseRange` is the canonical set-level formulation of the source's
statement that the image contains a dense set of points. -/
theorem domain_injective_dense_spectrum_image_conditions
    {R S : Type*} [CommRing R] [CommRing S] [IsDomain R] (φ : R →+* S) :
    List.TFAE
      [ Function.Injective φ,
        DenseRange (PrimeSpectrum.comap φ),
        ∃ q : PrimeSpectrum S,
          Ideal.comap φ q.asIdeal = (⊥ : Ideal R) ] := by
  rw [List.tfae_cons_cons]
  refine ⟨?_, ?_⟩
  · constructor
    · intro h
      rw [PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical]
      rw [RingHom.ker_eq_comap_bot, Ideal.comap_bot_of_injective φ h]
      exact bot_le
    · intro h
      rw [PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical] at h
      have hnil : nilradical R = (⊥ : Ideal R) :=
        nilradical_eq_bot_iff.mpr inferInstance
      rw [hnil] at h
      intro x y hxy
      have hxy0 : x - y ∈ RingHom.ker φ := by
        change φ (x - y) = 0
        rw [map_sub, hxy, sub_self]
      have hz : x - y ∈ (⊥ : Ideal R) := h hxy0
      apply sub_eq_zero.mp
      simpa using hz
  · rw [List.tfae_cons_cons]
    refine ⟨?_, List.tfae_singleton _⟩
    constructor
    · intro h
      have hinj : Function.Injective φ := by
        rw [PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical] at h
        have hnil : nilradical R = (⊥ : Ideal R) :=
          nilradical_eq_bot_iff.mpr inferInstance
        rw [hnil] at h
        intro x y hxy
        have hxy0 : x - y ∈ RingHom.ker φ := by
          change φ (x - y) = 0
          rw [map_sub, hxy, sub_self]
        have hz : x - y ∈ (⊥ : Ideal R) := h hxy0
        apply sub_eq_zero.mp
        simpa using hz
      have hbot : (⊥ : PrimeSpectrum R) ∈ Set.range (PrimeSpectrum.comap φ) := by
        apply (PrimeSpectrum.mem_range_comap_iff φ).mpr
        simpa only [PrimeSpectrum.asIdeal_bot, Ideal.map_bot] using
          (Ideal.comap_bot_of_injective φ hinj)
      rcases hbot with ⟨q, hq⟩
      refine ⟨q, ?_⟩
      simpa only [PrimeSpectrum.comap_asIdeal, PrimeSpectrum.asIdeal_bot] using
        (congrArg PrimeSpectrum.asIdeal hq)
    · rintro ⟨q, hq⟩
      rw [PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical]
      calc
        RingHom.ker φ ≤ Ideal.comap φ q.asIdeal := Ideal.ker_le_comap φ
        _ = ⊥ := hq
        _ ≤ nilradical R := bot_le

theorem injective_spectrum_image_contains_minimalPrimes
    {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S)
    (hφ : Function.Injective φ) (p : PrimeSpectrum R)
    (hp : p.asIdeal ∈ minimalPrimes R) :
    p ∈ Set.range (PrimeSpectrum.comap φ) := by
  obtain ⟨q, hq, hqp⟩ :=
    Ideal.exists_comap_eq_of_mem_minimalPrimes_of_injective hφ p.asIdeal hp
  refine ⟨⟨q, hq⟩, ?_⟩
  apply PrimeSpectrum.ext
  exact hqp

theorem spectrum_image_dense_kernel_nilpotent_conditions
    {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) :
    List.TFAE
      [ (∀ x : R, x ∈ RingHom.ker φ → IsNilpotent x),
        ∀ p : PrimeSpectrum R, p.asIdeal ∈ minimalPrimes R →
          p ∈ Set.range (PrimeSpectrum.comap φ),
        DenseRange (PrimeSpectrum.comap φ) ] := by
  rw [List.tfae_cons_cons]
  refine ⟨?_, ?_⟩
  · constructor
    · intro h
      have hdense : DenseRange (PrimeSpectrum.comap φ) :=
        (PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical φ).mpr (by
          intro x hx
          simpa only [mem_nilradical] using h x hx)
      intro p hp
      have hp' := (PrimeSpectrum.denseRange_comap_iff_minimalPrimes φ).mp hdense
        p.asIdeal hp
      rcases hp' with ⟨q, hq⟩
      refine ⟨q, ?_⟩
      apply PrimeSpectrum.ext
      simpa only [PrimeSpectrum.comap_asIdeal] using
        (congrArg PrimeSpectrum.asIdeal hq)
    · intro h
      have hdense : DenseRange (PrimeSpectrum.comap φ) :=
        (PrimeSpectrum.denseRange_comap_iff_minimalPrimes φ).mpr (by
          intro I hI
          exact h ⟨I, hI.1.1⟩ hI)
      intro x hx
      have hx' := (PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical φ).mp hdense hx
      simpa only [mem_nilradical] using hx'
  · rw [List.tfae_cons_cons]
    refine ⟨?_, List.tfae_singleton _⟩
    constructor
    · intro h
      apply (PrimeSpectrum.denseRange_comap_iff_minimalPrimes φ).mpr
      intro I hI
      exact h ⟨I, hI.1.1⟩ hI
    · intro h p hp
      have hp' := (PrimeSpectrum.denseRange_comap_iff_minimalPrimes φ).mp h p.asIdeal hp
      rcases hp' with ⟨q, hq⟩
      refine ⟨q, ?_⟩
      apply PrimeSpectrum.ext
      simpa only [PrimeSpectrum.comap_asIdeal] using
        (congrArg PrimeSpectrum.asIdeal hq)

theorem minimalPrime_in_spectrum_image_of_minimalPrime
    {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S)
    (p : PrimeSpectrum R) (hp : p.asIdeal ∈ minimalPrimes R)
    (hpImage : p ∈ Set.range (PrimeSpectrum.comap φ)) :
    ∃ q : PrimeSpectrum S, q.asIdeal ∈ minimalPrimes S ∧
      PrimeSpectrum.comap φ q = p := by
  obtain ⟨q, hq⟩ := hpImage
  obtain ⟨r, hr, hrq⟩ :=
    Ideal.exists_minimalPrimes_le (I := (⊥ : Ideal S)) (J := q.asIdeal) bot_le
  let _ : r.IsPrime := hr.1.1
  let _ : (Ideal.comap φ r).IsPrime := Ideal.comap_isPrime φ r
  have hqp : Ideal.comap φ q.asIdeal = p.asIdeal := by
    simpa only [PrimeSpectrum.comap_asIdeal] using
      (congrArg PrimeSpectrum.asIdeal hq)
  have hle : Ideal.comap φ r ≤ p.asIdeal :=
    (Ideal.comap_mono hrq).trans_eq hqp
  have heq : p.asIdeal = Ideal.comap φ r :=
    (hp.2 ⟨inferInstance, bot_le⟩ hle).antisymm hle
  refine ⟨⟨r, hr.1.1⟩, hr, ?_⟩
  apply PrimeSpectrum.ext
  exact heq.symm

/-! ## Algebraic fraction fields -/

/- The source's ``A ⊂ B`` is forced by the displayed fraction-field and
   scalar-tower assumptions.  These compatibilities are kept explicit, so this
   interface also applies to any chosen fraction-field models. -/
theorem ideal_comap_ne_bot_of_algebraic_fractionFields
    {A B K L : Type*} [CommRing A] [CommRing B] [IsDomain A] [IsDomain B]
    [Field K] [Field L] [Algebra A B] [Algebra A K] [Algebra A L]
    [Algebra B L] [Algebra K L] [IsFractionRing A K] [IsFractionRing B L]
    [IsScalarTower A B L] [IsScalarTower A K L]
    [Algebra.IsAlgebraic K L]
    (J : Ideal B) (hJ : J ≠ ⊥) :
    Ideal.comap (algebraMap A B) J ≠ (⊥ : Ideal A) := by
  obtain ⟨x, hxJ, hx0⟩ := J.ne_bot_iff.mp hJ
  have hxalgL : IsAlgebraic A (algebraMap B L x) :=
    (IsFractionRing.isAlgebraic_iff A K L).mpr
      (Algebra.IsAlgebraic.isAlgebraic (R := K) (algebraMap B L x))
  obtain ⟨p, hpne, hpx⟩ := hxalgL
  have hxalgB : IsAlgebraic A x := by
    refine ⟨p, hpne, ?_⟩
    apply (IsFractionRing.injective B L)
    rw [← Polynomial.aeval_algebraMap_apply]
    simpa using hpx
  exact Ideal.comap_ne_bot_of_algebraic_mem hx0 hxJ hxalgB

/- The final sentence of the source lemma is recorded as its direct spectral
consequence for a proper closed subset. -/
theorem image_proper_closed_not_dense_of_algebraic_fractionFields
    {A B K L : Type*} [CommRing A] [CommRing B] [IsDomain A] [IsDomain B]
    [Field K] [Field L] [Algebra A B] [Algebra A K] [Algebra A L]
    [Algebra B L] [Algebra K L] [IsFractionRing A K] [IsFractionRing B L]
    [IsScalarTower A B L] [IsScalarTower A K L]
    [Algebra.IsAlgebraic K L]
    {Z : Set (PrimeSpectrum B)} (hZclosed : IsClosed Z)
    (hZproper : Z ≠ Set.univ) :
    ¬ Dense (PrimeSpectrum.comap (algebraMap A B) '' Z) := by
  rcases (PrimeSpectrum.isClosed_iff_zeroLocus_ideal Z).mp hZclosed with ⟨J, hJZ⟩
  have hJne : J ≠ (⊥ : Ideal B) := by
    intro hJbot
    apply hZproper
    rw [hJZ, hJbot, PrimeSpectrum.zeroLocus_bot]
  have hIne :
      Ideal.comap (algebraMap A B) J ≠ (⊥ : Ideal A) :=
    ideal_comap_ne_bot_of_algebraic_fractionFields
      (A := A) (B := B) (K := K) (L := L) J hJne
  have hsub :
      PrimeSpectrum.comap (algebraMap A B) '' Z ⊆
        PrimeSpectrum.zeroLocus
          (Ideal.comap (algebraMap A B) J : Set A) := by
    rintro p ⟨q, hq, rfl⟩
    rw [PrimeSpectrum.mem_zeroLocus]
    intro a ha
    change algebraMap A B a ∈ q.asIdeal
    apply (PrimeSpectrum.mem_zeroLocus q (J : Set B)).mp
      (hJZ ▸ hq)
    exact ha
  intro hdense
  have hclosedI : IsClosed
      (PrimeSpectrum.zeroLocus
        (Ideal.comap (algebraMap A B) J : Set A)) :=
    PrimeSpectrum.isClosed_zeroLocus _
  have hclosure :
      closure (PrimeSpectrum.comap (algebraMap A B) '' Z) =
        (Set.univ : Set (PrimeSpectrum A)) :=
    hdense.closure_eq
  have hunivsubset :
      (Set.univ : Set (PrimeSpectrum A)) ⊆
        PrimeSpectrum.zeroLocus
          (Ideal.comap (algebraMap A B) J : Set A) := by
    rw [← hclosure]
    exact (hclosedI.closure_subset_iff).mpr hsub
  have hzero :
      PrimeSpectrum.zeroLocus
          (Ideal.comap (algebraMap A B) J : Set A) =
        (Set.univ : Set (PrimeSpectrum A)) :=
    Set.eq_univ_of_forall fun p => hunivsubset (Set.mem_univ p)
  have hIleNil :
      Ideal.comap (algebraMap A B) J ≤ nilradical A := by
    exact (PrimeSpectrum.zeroLocus_eq_univ_iff
      (Ideal.comap (algebraMap A B) J : Set A)).mp hzero
  have hnil : nilradical A = (⊥ : Ideal A) :=
    nilradical_eq_bot_iff.mpr inferInstance
  exact hIne (le_antisymm (by simpa [hnil] using hIleNil) bot_le)

end Formalization.Books.Algebra.Unit30
