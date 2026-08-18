import Formalization.Books.Algebra.Unit29.ImagesOfFinitePresentation
import Mathlib.RingTheory.Algebraic.Basic
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

/-- A finite-type inclusion of domains becomes finitely presented after
localizing the source and target at suitable nonzero elements. -/
theorem exists_localization_away_finitePresentation
    {R S : Type*} [CommRing R] [CommRing S] [IsDomain R] [IsDomain S]
    (φ : R →+* S) (hφ : Function.Injective φ)
    (hft : RingHom.FiniteType φ) :
    ∃ f : R, f ≠ 0 ∧ ∃ g : S, g ≠ 0 ∧
      RingHom.FinitePresentation (localizationAwayMulMap φ f g) := by
  sorry

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
  sorry

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
