import Mathlib.Algebra.Algebra.Subalgebra.Pi
import Mathlib.LinearAlgebra.Prod
import Mathlib.RingTheory.Algebraic.Integral
import Mathlib.RingTheory.FinitePresentation
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.Localization.Integral
import Mathlib.RingTheory.RingHom.Finite
import Mathlib.RingTheory.RingHom.FinitePresentation
import Mathlib.RingTheory.RingHom.FiniteType
import Mathlib.RingTheory.RingHom.Integral
import Mathlib.RingTheory.QuasiFinite.Basic
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Formalization.Books.Algebra.Unit14.BaseChange

/-!
# Commutative Algebra, Chapter 36: Finite and integral ring extensions

Mathlib's canonical `RingHom.IsIntegralElem`, `RingHom.IsIntegral`,
`integralClosure`, `RingHom.Finite`, and `RingHom.FiniteType` interfaces are
used throughout.  The declarations below record the source's definitions and
theorem interfaces in source order; theorem proofs are deferred to the proving
stage.
-/

namespace Formalization.Books.Algebra.Unit36

universe u v w z

noncomputable section

open Set
open scoped Polynomial TensorProduct

/-! ## Integral elements and finite extensions -/

/- The definition of integrality is Mathlib's `RingHom.IsIntegralElem` and
`RingHom.IsIntegral`; the following iff records its polynomial presentation
explicitly in the chapter namespace. -/

/-- An element is integral over a ring map exactly when it is a root of a
monic polynomial after applying the map to its coefficients. -/
theorem isIntegralElem_iff
    {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (s : S) :
    f.IsIntegralElem s ↔
      ∃ p : R[X], p.Monic ∧ Polynomial.eval₂ f s p = 0 :=
  Iff.rfl

/-- A ring map is integral exactly when each target element is integral. -/
theorem isIntegral_iff
    {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) :
    f.IsIntegral ↔ ∀ s : S, f.IsIntegralElem s :=
  Iff.rfl

/-- The algebra form of integrality is the pointwise form of `Algebra.IsIntegral`. -/
theorem algebraIsIntegral_iff
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] :
    Algebra.IsIntegral R S ↔ ∀ s : S, IsIntegral R s :=
  Algebra.isIntegral_def

/-- The determinant-trick criterion for an integral element. -/
theorem isIntegral_of_finite_submodule
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    (M : Submodule R S) [Module.Finite R M] (y : S)
    (h1 : (1 : S) ∈ M) (hstable : ∀ m ∈ M, y * m ∈ M) :
    IsIntegral R y := by
  let A' : Subalgebra R S :=
    { carrier := {x | ∀ m ∈ M, x * m ∈ M}
      mul_mem' := fun {a b} ha hb m hm => by
        simpa [mul_assoc] using ha _ (hb _ hm)
      one_mem' := fun m hm => by simpa using hm
      add_mem' := fun {a b} ha hb m hm => by
        simpa [add_mul] using M.add_mem (ha _ hm) (hb _ hm)
      zero_mem' := fun m _hm => by simp
      algebraMap_mem' := fun r m hm => by
        simpa [Algebra.smul_def, mul_assoc, mul_left_comm, mul_comm] using M.smul_mem r hm }
  let f : A' →ₐ[R] Module.End R M :=
    AlgHom.ofLinearMap
      { toFun := fun x => (DistribSMul.toLinearMap R S x).restrict x.prop
        map_add' := by intro x z; ext m; exact add_mul _ _ _
        map_smul' := by
          intro r x
          ext m
          simp [DistribSMul.toLinearMap_apply, LinearMap.restrict_apply,
            Algebra.smul_def, mul_assoc]
          change (algebraMap R S r) * ((x : S) * (m : S)) =
            (algebraMap R S r) * ((x : S) * (m : S))
          rfl }
      (by
        ext m
        change (1 : S) * (m : S) = (m : S)
        simp)
      (by
        intro x z
        ext m
        change ((x : S) * (z : S)) * (m : S) =
          (x : S) * ((z : S) * (m : S))
        rw [mul_assoc])
  have hf : Function.Injective f := by
    intro x z hx
    apply Subtype.ext
    have hx1 := congr_arg (fun g : Module.End R M => g ⟨1, h1⟩) hx
    have hx2 := congr_arg Subtype.val hx1
    change (x : S) * (1 : S) = (z : S) * (1 : S) at hx2
    simpa using hx2
  change IsIntegral R (A'.val ⟨y, hstable⟩)
  apply (isIntegral_algHom_iff A'.val Subtype.val_injective).2
  have hiff : ∀ x : A', IsIntegral R (f x) ↔ IsIntegral R x :=
    fun x => @isIntegral_algHom_iff R _ A' (Module.End R M) _ _ _ _ f hf x
  apply (hiff _).mp
  apply Algebra.IsIntegral.isIntegral

/-- A finite ring map is integral. -/
theorem finite_isIntegral
    {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (hf : f.Finite) : f.IsIntegral := by
  exact hf.to_isIntegral

/-- A finite set of integral elements is contained in a finite subalgebra, and
conversely every finite subalgebra consists of integral elements. -/
theorem finite_subalgebra_of_integral_elements
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    (s : Finset S) :
    (∀ x ∈ s, IsIntegral R x) ↔
      ∃ A : Subalgebra R S, Module.Finite R A ∧ ∀ x ∈ s, x ∈ A := by
  classical
  constructor
  · intro h
    refine ⟨Algebra.adjoin R (s : Set S),
      Module.Finite.of_fg (fg_adjoin_of_finite s.finite_toSet h), ?_⟩
    intro x hx
    exact Algebra.subset_adjoin hx
  · rintro ⟨A, hA, hmem⟩ x hx
    let hA := hA
    exact IsIntegral.of_mem_of_fg A Submodule.FG.of_finite x (hmem x hx)

/-- Finite is equivalent to integral and finite type. -/
theorem finite_iff_isIntegral_and_finiteType
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] :
    Module.Finite R S ↔ Algebra.IsIntegral R S ∧ Algebra.FiniteType R S :=
  Algebra.finite_iff_isIntegral_and_finiteType

/-- A ring map is finite exactly when it has finitely many integral algebra
generators. -/
theorem finite_iff_finite_integral_generators
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] :
    Module.Finite R S ↔
      ∃ s : Finset S,
        Algebra.adjoin R (s : Set S) = ⊤ ∧ ∀ x ∈ s, IsIntegral R x := by
  classical
  constructor
  · intro h
    let h := h
    obtain ⟨s, hs⟩ := (inferInstance : Algebra.FiniteType R S).out
    exact ⟨s, hs, fun x hx => Algebra.IsIntegral.isIntegral x⟩
  · rintro ⟨s, hs, hintegral⟩
    have hfin : Module.Finite R (Algebra.adjoin R (s : Set S)) :=
      Module.Finite.of_fg (fg_adjoin_of_finite s.finite_toSet hintegral)
    rw [hs] at hfin
    let hfin := hfin
    exact Module.Finite.equiv (Subalgebra.topEquiv (R := R) (A := S)).toLinearEquiv

/-- Integrality is transitive in an algebra tower. -/
theorem integral_transitive
    {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra S T] [Algebra R T] [IsScalarTower R S T]
    [Algebra.IsIntegral R S] [Algebra.IsIntegral S T] :
    Algebra.IsIntegral R T := by
  exact Algebra.IsIntegral.trans S

/-! ## Integral closures -/

/- `integralClosure R S : Subalgebra R S` is Mathlib's integral-closure
construction and is the source's `R`-subalgebra of integral elements. -/

/-- The carrier of the canonical integral closure is the set of integral
elements. -/
theorem integralClosure_carrier
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] :
    (integralClosure R S : Set S) = {s : S | IsIntegral R s} :=
  rfl

/-- The base algebra is integral exactly when its integral closure is the top
subalgebra. -/
theorem integral_iff_integralClosure_eq_top
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] :
    Algebra.IsIntegral R S ↔ integralClosure R S = ⊤ := by
  exact integralClosure_eq_top_iff.symm

/-- For an injective structure map, being integrally closed is the statement
that the integral closure is just the image of the base algebra. -/
theorem integrallyClosed_iff_integralClosure_eq_bot
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    (hinj : Function.Injective (algebraMap R S)) :
    integralClosure R S = ⊥ ↔ IsIntegrallyClosedIn R S := by
  exact IsIntegrallyClosedIn.integralClosure_eq_bot_iff S hinj

/-- The integral closure is integrally closed in the ambient algebra. -/
theorem integralClosure_isIntegrallyClosedIn
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] :
    IsIntegrallyClosedIn (integralClosure R S) S := by
  infer_instance

/-- Integrality of a finite product is coordinatewise. -/
theorem product_isIntegral_iff
    {ι : Type u} [Fintype ι]
    {R S : ι → Type v} [∀ i, CommRing (R i)] [∀ i, CommRing (S i)]
    (f : ∀ i, R i →+* S i) (s : ∀ i, S i) :
    (RingHom.pi (fun i => (f i).comp (Pi.evalRingHom R i))).IsIntegralElem s ↔
      ∀ i, (f i).IsIntegralElem (s i) := by
  classical
  constructor
  · rintro ⟨p, hp, hp0⟩ i
    refine ⟨p.map (Pi.evalRingHom R i), hp.map _, ?_⟩
    rw [Polynomial.eval₂_map]
    simpa [Polynomial.eval₂_eq_sum, Polynomial.sum_def, RingHom.comp_apply] using
      congr_fun hp0 i
  · intro h
    choose p hp hroot using h
    let N : ℕ := ∑ i, (p i).natDegree
    let q : ∀ i, (R i)[X] :=
      fun i => p i * Polynomial.X ^ (N - (p i).natDegree)
    have hdeg_le (i : ι) : (p i).natDegree ≤ N := by
      dsimp [N]
      exact Finset.single_le_sum (f := fun j => (p j).natDegree)
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
    have hq_monic (i : ι) : (q i).Monic := by
      dsimp [q]
      exact (hp i).mul (Polynomial.monic_X_pow _)
    have hq_coeff (i : ι) : (q i).coeff N = 1 := by
      by_cases hRi : Nontrivial (R i)
      · let hRi := hRi
        have hdegree : (q i).natDegree = N := by
          dsimp [q]
          rw [(hp i).natDegree_mul (Polynomial.monic_X_pow _),
            Polynomial.natDegree_X_pow]
          exact Nat.add_sub_of_le (hdeg_le i)
        rw [← hdegree]
        exact (hq_monic i).coeff_natDegree
      · let hRi := not_nontrivial_iff_subsingleton.mp hRi
        exact Subsingleton.elim _ _
    have hq_root (i : ι) :
        Polynomial.eval₂ (f i) (s i) (q i) = 0 := by
      dsimp [q]
      simp [Polynomial.eval₂_mul, hroot i]
    let p' : (∀ i, R i)[X] := (Polynomial.piEquiv R).symm q
    have hp'_coeff (i : ι) : p'.coeff N i = 1 := by
      have hi := congr_arg (fun r : ∀ i, (R i)[X] => (r i).coeff N)
        ((Polynomial.piEquiv R).apply_symm_apply q)
      have hqi := hq_coeff i
      have hi' : (p'.map (Pi.evalRingHom R i)).coeff N = (q i).coeff N := by
        change (p'.map (Pi.evalRingHom R i)).coeff N = (q i).coeff N at hi
        exact hi
      rw [Polynomial.coeff_map] at hi'
      exact hi'.trans hqi
    have hp'_coeff_zero {n : ℕ} (hn : N < n) : p'.coeff n = 0 := by
      ext i
      have hi := congr_arg (fun r : ∀ i, (R i)[X] => (r i).coeff n)
        ((Polynomial.piEquiv R).apply_symm_apply q)
      have hqi : (q i).coeff n = 0 := by
        by_cases hRi : Nontrivial (R i)
        · let hRi := hRi
          have hdegree : (q i).natDegree = N := by
            dsimp [q]
            rw [(hp i).natDegree_mul (Polynomial.monic_X_pow _),
              Polynomial.natDegree_X_pow]
            exact Nat.add_sub_of_le (hdeg_le i)
          exact Polynomial.coeff_eq_zero_of_natDegree_lt (hdegree.trans_lt hn)
        · let hRi := not_nontrivial_iff_subsingleton.mp hRi
          exact Subsingleton.elim _ _
      have hi' : (p'.map (Pi.evalRingHom R i)).coeff n = (q i).coeff n := by
        change (p'.map (Pi.evalRingHom R i)).coeff n = (q i).coeff n at hi
        exact hi
      rw [Polynomial.coeff_map] at hi'
      exact hi'.trans hqi
    have hp'_monic : p'.Monic :=
      (Polynomial.MonicDegreeEq.monic
        (⟨p', funext hp'_coeff, fun n hn => hp'_coeff_zero hn⟩ :
          Polynomial.MonicDegreeEq (∀ i, R i) N))
    refine ⟨p', hp'_monic, ?_⟩
    funext i
    have hi := congr_arg (fun r : ∀ i, (R i)[X] => r i)
      ((Polynomial.piEquiv R).apply_symm_apply q)
    have hi' : p'.map (Pi.evalRingHom R i) = q i := by
      change p'.map (Pi.evalRingHom R i) = q i at hi
      exact hi
    have hi'' :
        Polynomial.eval₂ ((f i).comp (Pi.evalRingHom R i)) (s i) p' = 0 := by
      have ht := hq_root i
      rw [← hi'] at ht
      rw [Polynomial.eval₂_map] at ht
      exact ht
    simpa [Polynomial.eval₂_eq_sum, Polynomial.sum_def, RingHom.comp_apply] using hi''

/-- Membership in the integral closure of a product is coordinatewise. -/
theorem product_integralClosure_mem_iff
    {ι : Type u} [Fintype ι]
    {R S : ι → Type v} [∀ i, CommRing (R i)] [∀ i, CommRing (S i)]
    [∀ i, Algebra (R i) (S i)] (s : ∀ i, S i) :
    s ∈ integralClosure (∀ i, R i) (∀ i, S i) ↔
      ∀ i, s i ∈ integralClosure (R i) (S i) := by
  change (algebraMap (∀ i, R i) (∀ i, S i)).IsIntegralElem s ↔
    ∀ i, (algebraMap (R i) (S i)).IsIntegralElem (s i)
  exact product_isIntegral_iff (fun i => algebraMap (R i) (S i)) s

/-- A product extension is integrally closed exactly when each factor is. -/
theorem product_isIntegrallyClosedIn_iff
    {ι : Type u} [Fintype ι]
    {R S : ι → Type v} [∀ i, CommRing (R i)] [∀ i, CommRing (S i)]
    [∀ i, Algebra (R i) (S i)] :
    IsIntegrallyClosedIn (∀ i, R i) (∀ i, S i) ↔
      ∀ i, IsIntegrallyClosedIn (R i) (S i) := by
  classical
  constructor
  · intro h i
    refine ⟨?_, ?_⟩
    · intro a b hab
      let a' : ∀ j, R j := Function.update 0 i a
      let b' : ∀ j, R j := Function.update 0 i b
      have hab' : a' = b' := h.1 (by
        funext j
        by_cases hji : j = i
        · subst j
          change (algebraMap (R i) (S i)) (a' i) =
            (algebraMap (R i) (S i)) (b' i)
          simpa [a', b'] using hab
        · change (algebraMap (R j) (S j)) (a' j) =
            (algebraMap (R j) (S j)) (b' j)
          simp [a', b', hji])
      simpa [a', b'] using congr_fun hab' i
    · intro x
      constructor
      · intro hx
        let x' : ∀ j, S j := Function.update 0 i x
        have hx' : IsIntegral (∀ j, R j) x' := by
          rw [← mem_integralClosure_iff]
          apply (product_integralClosure_mem_iff x').2
          intro j
          by_cases hji : j = i
          · subst j
            rw [mem_integralClosure_iff]
            simpa [x'] using hx
          · rw [mem_integralClosure_iff]
            simpa [x', hji] using (isIntegral_zero (R := R j))
        obtain ⟨y, hy⟩ := h.2.mp hx'
        refine ⟨y i, ?_⟩
        have hi := congr_fun hy i
        change
          (RingHom.pi (fun j => (algebraMap (R j) (S j)).comp
            (Pi.evalRingHom R j)) y) i = x' i at hi
        simpa [x'] using hi
      · rintro ⟨y, rfl⟩
        exact isIntegral_algebraMap
  · intro h
    refine ⟨?_, ?_⟩
    · intro a b hab
      funext i
      apply (h i).1
      have hi := congr_fun hab i
      change (algebraMap (R i) (S i)) (a i) =
        (algebraMap (R i) (S i)) (b i) at hi
      exact hi
    · intro x
      constructor
      · intro hx
        have hx' := (product_isIntegral_iff (fun i => algebraMap (R i) (S i)) x).mp hx
        choose y hy using fun i => (h i).2.mp (hx' i)
        refine ⟨y, ?_⟩
        funext i
        change (algebraMap (R i) (S i)) (y i) = x i
        exact hy i
      · rintro ⟨y, rfl⟩
        exact isIntegral_algebraMap

/-- The integral-closure construction commutes with localization. -/
theorem integralClosure_localization
    {R S Rf Sf : Type*}
    [CommRing R] [CommRing S] [CommRing Rf] [CommRing Sf]
    [Algebra R S] [Algebra R Rf] [Algebra S Sf] [Algebra Rf Sf]
    [Algebra R Sf] [IsScalarTower R S Sf] [IsScalarTower R Rf Sf]
    (M : Submonoid R) [IsLocalization M Rf]
    [IsLocalization (Algebra.algebraMapSubmonoid S M) Sf]
    [Algebra (integralClosure R S) (integralClosure Rf Sf)]
    [IsScalarTower (integralClosure R S) (integralClosure Rf Sf) Sf]
    [IsScalarTower R (integralClosure R S) (integralClosure Rf Sf)] :
    IsLocalization
      (Algebra.algebraMapSubmonoid (integralClosure R S) M)
      (integralClosure Rf Sf) := by
  exact IsLocalization.integralClosure M

/-- An element is integral exactly when its image in every prime localization
is integral. -/
theorem isIntegral_iff_integral_at_prime
    {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (x : S) :
    f.IsIntegralElem x ↔
      ∀ p : PrimeSpectrum R,
        (IsLocalization.map
            (M := p.asIdeal.primeCompl)
            (S := Localization p.asIdeal.primeCompl)
            (P := S)
            (T := Submonoid.map (f : R →* S) p.asIdeal.primeCompl)
            (Q := Localization (Submonoid.map (f : R →* S) p.asIdeal.primeCompl))
            f
            (show p.asIdeal.primeCompl ≤
                Submonoid.comap (f : R →* S)
                  (Submonoid.map (f : R →* S) p.asIdeal.primeCompl) from
            p.asIdeal.primeCompl.le_comap_map)).IsIntegralElem
          (algebraMap S (Localization (Submonoid.map (f : R →* S) p.asIdeal.primeCompl)) x) := by
  constructor
  · intro hx p
    apply RingHom.IsIntegralElem.of_comp (R := R)
      (f := algebraMap R (Localization p.asIdeal.primeCompl))
    have hcomp :
        (IsLocalization.map
            (M := p.asIdeal.primeCompl)
            (S := Localization p.asIdeal.primeCompl)
            (P := S)
            (T := Submonoid.map (f : R →* S) p.asIdeal.primeCompl)
            (Q := Localization (Submonoid.map (f : R →* S) p.asIdeal.primeCompl))
            f p.asIdeal.primeCompl.le_comap_map).comp
            (algebraMap R (Localization p.asIdeal.primeCompl)) =
          (algebraMap S (Localization (Submonoid.map (f : R →* S) p.asIdeal.primeCompl))).comp f := by
      exact IsLocalization.map_comp _
    rw [hcomp]
    exact hx.map
      (algebraMap S (Localization (Submonoid.map (f : R →* S) p.asIdeal.primeCompl)))
  · intro h
    classical
    exact (letI := (f.toAlgebra : Algebra R S)
    letI (P : Ideal R) [P.IsMaximal] :=
      (OreLocalization.instAlgebra : Algebra R
        (Localization (Submonoid.map (f : R →* S) P.primeCompl)))
    letI (P : Ideal R) [P.IsMaximal] :=
      (show IsScalarTower R S
          (Localization (Submonoid.map (f : R →* S) P.primeCompl)) from
        { smul_assoc := by
            intro r s z
            simp only [Algebra.smul_def, map_mul, mul_assoc]
            rfl })
    letI (P : Ideal R) [P.IsMaximal] :=
      (by
        rw [Algebra.algebraMapSubmonoid, RingHom.algebraMap_toAlgebra]
        convert (inferInstance : IsLocalization
          (Submonoid.map (f : R →* S) P.primeCompl)
          (Localization (Submonoid.map (f : R →* S) P.primeCompl))) using 1
        rfl : IsLocalization
          (Algebra.algebraMapSubmonoid S P.primeCompl)
          (Localization (Submonoid.map (f : R →* S) P.primeCompl)))
    let localizedMap (P : Ideal R) [P.IsMaximal] :
        S →ₗ[R] Localization (Submonoid.map (f : R →* S) P.primeCompl) :=
      (IsScalarTower.toAlgHom R S
        (Localization (Submonoid.map (f : R →* S) P.primeCompl))).toLinearMap
    by
      refine @Submodule.mem_of_localization_maximal R S _ _ _
        (fun P [P.IsMaximal] => Localization (Submonoid.map (f : R →* S) P.primeCompl))
        (by infer_instance) (by infer_instance) localizedMap
        (by
          intro P hP
          apply isLocalizedModule_iff_isLocalization.mpr
          infer_instance)
        x (integralClosure R S).toSubmodule ?_
      intro P hP
      exact (letI :=
      (IsLocalization.map
        (M := P.primeCompl)
        (S := Localization P.primeCompl)
        (P := S)
        (T := Submonoid.map (f : R →* S) P.primeCompl)
        (Q := Localization (Submonoid.map (f : R →* S) P.primeCompl))
        f
        (P.primeCompl.le_comap_map : P.primeCompl ≤
          Submonoid.comap (f : R →* S)
            (Submonoid.map (f : R →* S) P.primeCompl))).toAlgebra
        by
    have hcomp :
        (algebraMap (Localization.AtPrime P)
            (Localization (Submonoid.map (f : R →* S) P.primeCompl))).comp
            (algebraMap R (Localization.AtPrime P)) =
          (algebraMap S
            (Localization (Submonoid.map (f : R →* S) P.primeCompl))).comp f := by
      exact IsLocalization.map_comp _
    exact (letI := IsScalarTower.of_algebraMap_eq' (by
        ext r
        change algebraMap R
            (Localization (Submonoid.map (f : R →* S) P.primeCompl)) r =
          algebraMap (Localization.AtPrime P)
            (Localization (Submonoid.map (f : R →* S) P.primeCompl))
            (algebraMap R (Localization.AtPrime P) r)
        have hr := congrArg (fun g : R →+*
            Localization (Submonoid.map (f : R →* S) P.primeCompl) => g r) hcomp
        calc
          algebraMap R
              (Localization (Submonoid.map (f : R →* S) P.primeCompl)) r =
            algebraMap S
              (Localization (Submonoid.map (f : R →* S) P.primeCompl))
              (algebraMap R S r) :=
            (IsScalarTower.algebraMap_apply R S
              (Localization (Submonoid.map (f : R →* S) P.primeCompl)) r).symm
          _ = algebraMap S
              (Localization (Submonoid.map (f : R →* S) P.primeCompl)) (f r) := by
            rfl
          _ = algebraMap (Localization.AtPrime P)
              (Localization (Submonoid.map (f : R →* S) P.primeCompl))
              (algebraMap R (Localization.AtPrime P) r) := hr.symm)
    let closureMap : integralClosure R S →+*
        integralClosure (Localization.AtPrime P)
          (Localization (Submonoid.map (f : R →* S) P.primeCompl)) :=
      { toFun := fun y =>
          ⟨algebraMap S
              (Localization (Submonoid.map (f : R →* S) P.primeCompl)) y,
            IsIntegral.map_of_comp_eq
              (algebraMap R (Localization.AtPrime P))
              (algebraMap S
                (Localization (Submonoid.map (f : R →* S) P.primeCompl)))
              hcomp y.property⟩
        map_one' := by
          apply Subtype.ext
          exact map_one _
        map_mul' := by
          intro a b
          apply Subtype.ext
          change algebraMap S
              (Localization (Submonoid.map (f : R →* S) P.primeCompl)) (a * b) =
            algebraMap S
              (Localization (Submonoid.map (f : R →* S) P.primeCompl)) a *
              algebraMap S
                (Localization (Submonoid.map (f : R →* S) P.primeCompl)) b
          exact map_mul _ _ _
        map_zero' := by
          apply Subtype.ext
          exact map_zero _
        map_add' := by
          intro a b
          apply Subtype.ext
          change algebraMap S
              (Localization (Submonoid.map (f : R →* S) P.primeCompl)) (a + b) =
            algebraMap S
              (Localization (Submonoid.map (f : R →* S) P.primeCompl)) a +
              algebraMap S
                (Localization (Submonoid.map (f : R →* S) P.primeCompl)) b
          exact map_add _ _ _ }
    letI := closureMap.toAlgebra
    let closureAlgebra : Algebra (integralClosure R S)
        (Localization (Submonoid.map (f : R →* S) P.primeCompl)) :=
      { smul := fun r z =>
            algebraMap S
              (Localization (Submonoid.map (f : R →* S) P.primeCompl)) (r : S) * z
        algebraMap :=
          (algebraMap S (Localization (Submonoid.map (f : R →* S) P.primeCompl))).comp
            (integralClosure R S).val
        commutes' := by
          intro r z
          change algebraMap S
              (Localization (Submonoid.map (f : R →* S) P.primeCompl)) (r : S) * z =
            z * algebraMap S
              (Localization (Submonoid.map (f : R →* S) P.primeCompl)) (r : S)
          exact mul_comm _ _
        smul_def' := by
          intro r z
          rfl }
    letI := closureAlgebra
    letI := closureAlgebra.toSMul
    letI :=
      (inferInstance : Algebra (integralClosure (Localization.AtPrime P)
        (Localization (Submonoid.map (f : R →* S) P.primeCompl)))
        (Localization (Submonoid.map (f : R →* S) P.primeCompl))).toSMul
    let p : PrimeSpectrum R := ⟨P, hP.isPrime⟩
    let hxP : algebraMap S (Localization (Submonoid.map (f : R →* S) P.primeCompl)) x ∈
        integralClosure (Localization.AtPrime P)
          (Localization (Submonoid.map (f : R →* S) P.primeCompl)) := by
      rw [mem_integralClosure_iff]
      exact h p
    letI := (by
        refine ⟨⟨?_, ?_, ?_⟩⟩
        · rintro ⟨_, a, ha, rfl⟩
          convert!
            (IsLocalization.map_units (S := Localization.AtPrime P) ⟨a, ha⟩).map
              (algebraMap (Localization.AtPrime P)
                (integralClosure (Localization.AtPrime P)
                  (Localization (Submonoid.map (f : R →* S) P.primeCompl))))
          apply Subtype.ext
          change algebraMap S
              (Localization (Submonoid.map (f : R →* S) P.primeCompl))
              (algebraMap R S a) =
            algebraMap (Localization.AtPrime P)
              (Localization (Submonoid.map (f : R →* S) P.primeCompl))
              (algebraMap R (Localization.AtPrime P) a)
          simpa only [RingHom.comp_apply, RingHom.algebraMap_toAlgebra] using
            (congrArg (fun g : R →+*
              Localization (Submonoid.map (f : R →* S) P.primeCompl) => g a) hcomp).symm
        · rintro ⟨s, hs⟩
          obtain ⟨⟨y, hy, m₁, hm₁, rfl⟩, e⟩ :=
            IsLocalization.surj (Algebra.algebraMapSubmonoid S P.primeCompl) s
          simp only [← IsScalarTower.algebraMap_apply] at e
          obtain ⟨⟨m₂, hm₂⟩, hm₂s⟩ :=
            IsIntegral.exists_multiple_integral_of_isLocalization P.primeCompl _ hs
          simp only [Submonoid.smul_def, Algebra.smul_def] at hm₂s
          obtain ⟨m₃, hm₃, hm₃s⟩ :=
            IsLocalization.exists_isIntegral_smul_of_isIntegral_map
              (Sₘ := Localization (Submonoid.map (f : R →* S) P.primeCompl))
              P.primeCompl (x := m₂ • y) <| by
                simp only [Algebra.smul_def, map_mul, ← e, ← mul_assoc]
                exact hm₂s.mul (.algebraMap (Algebra.IsIntegral.isIntegral _))
          let z₂ : integralClosure R S :=
            ⟨m₃ • m₂ • y, (mem_integralClosure_iff R S).2 hm₃s⟩
          refine ⟨⟨z₂, _, _, mul_mem hm₁ (mul_mem hm₂ hm₃), rfl⟩, ?_⟩
          apply (FaithfulSMul.algebraMap_injective
            (integralClosure (Localization.AtPrime P)
              (Localization (Submonoid.map (f : R →* S) P.primeCompl)))
            (Localization (Submonoid.map (f : R →* S) P.primeCompl)))
          have hmap (z : integralClosure (Localization.AtPrime P)
              (Localization (Submonoid.map (f : R →* S) P.primeCompl))) :
              algebraMap (integralClosure (Localization.AtPrime P)
                (Localization (Submonoid.map (f : R →* S) P.primeCompl)))
                (Localization (Submonoid.map (f : R →* S) P.primeCompl)) z = z := by
            rfl
          simp only [hmap]
          simp only [RingHom.algebraMap_toAlgebra]
          simp only [Subalgebra.coe_mul]
          have hclosure (z : integralClosure R S) :
              (closureMap z : Localization (Submonoid.map (f : R →* S) P.primeCompl)) =
                algebraMap S
                  (Localization (Submonoid.map (f : R →* S) P.primeCompl)) (z : S) := by
            rfl
          rw [hclosure]
          rw [hclosure z₂]
          simp only [RingHom.codRestrict_apply]
          rw [map_mul, map_mul, map_mul]
          change (s * (algebraMap S
              (Localization (Submonoid.map (f : R →* S) P.primeCompl)) (f m₁) *
              algebraMap S
                (Localization (Submonoid.map (f : R →* S) P.primeCompl))
                (f m₂ * f m₃)) =
            algebraMap S
              (Localization (Submonoid.map (f : R →* S) P.primeCompl)) (z₂ : S))
          rw [map_mul]
          have hf₁ : f m₁ = algebraMap R S m₁ := by rfl
          have hf₂ : f m₂ = algebraMap R S m₂ := by rfl
          have hf₃ : f m₃ = algebraMap R S m₃ := by rfl
          rw [hf₁, hf₂, hf₃]
          rw [← IsScalarTower.algebraMap_apply R S
            (Localization (Submonoid.map (f : R →* S) P.primeCompl)) m₁,
            ← IsScalarTower.algebraMap_apply R S
              (Localization (Submonoid.map (f : R →* S) P.primeCompl)) m₂,
            ← IsScalarTower.algebraMap_apply R S
              (Localization (Submonoid.map (f : R →* S) P.primeCompl)) m₃]
          rw [← mul_assoc]
          rw [e]
          change (algebraMap S
              (Localization (Submonoid.map (f : R →* S) P.primeCompl)) y *
              (algebraMap R
                (Localization (Submonoid.map (f : R →* S) P.primeCompl)) m₂ *
              algebraMap R
                (Localization (Submonoid.map (f : R →* S) P.primeCompl)) m₃) =
            algebraMap S
              (Localization (Submonoid.map (f : R →* S) P.primeCompl)) (z₂ : S))
          have hz₂ : (z₂ : S) = m₃ • m₂ • y := by rfl
          rw [hz₂]
          rw [IsScalarTower.algebraMap_apply R S
            (Localization (Submonoid.map (f : R →* S) P.primeCompl)) m₂,
            IsScalarTower.algebraMap_apply R S
              (Localization (Submonoid.map (f : R →* S) P.primeCompl)) m₃]
          simp only [Algebra.smul_def, map_mul]
          ring
        · rintro ⟨a, ha⟩ ⟨b, hb⟩ e
          have he := congrArg
            (algebraMap (integralClosure (Localization.AtPrime P)
                (Localization (Submonoid.map (f : R →* S) P.primeCompl)))
              (Localization (Submonoid.map (f : R →* S) P.primeCompl))) e
          have he' : algebraMap S
                (Localization (Submonoid.map (f : R →* S) P.primeCompl)) a =
              algebraMap S
                (Localization (Submonoid.map (f : R →* S) P.primeCompl)) b := by
            change algebraMap S
                (Localization (Submonoid.map (f : R →* S) P.primeCompl)) a =
              algebraMap S
                (Localization (Submonoid.map (f : R →* S) P.primeCompl)) b at he
            exact he
          obtain ⟨⟨_, m, hm, rfl⟩, hmab⟩ :=
            (IsLocalization.eq_iff_exists
              (Algebra.algebraMapSubmonoid S P.primeCompl) _).mp he'
          refine ⟨⟨_, m, hm, rfl⟩, ?_⟩
          apply Subtype.ext
          simpa using hmab : IsLocalization
            (Algebra.algebraMapSubmonoid (integralClosure R S) P.primeCompl)
            (integralClosure (Localization.AtPrime P)
              (Localization (Submonoid.map (f : R →* S) P.primeCompl))))
    by
      obtain ⟨w, hcm⟩ :=
        IsLocalization.surj (Algebra.algebraMapSubmonoid (integralClosure R S) P.primeCompl)
          (⟨algebraMap S (Localization (Submonoid.map (f : R →* S) P.primeCompl)) x, hxP⟩ :
            integralClosure (Localization.AtPrime P)
              (Localization (Submonoid.map (f : R →* S) P.primeCompl)))
      obtain ⟨m, hm, hmw⟩ := w.2.property
      let m' : P.primeCompl := ⟨m, hm⟩
      rw [Submodule.mem_localized₀]
      refine ⟨w.1, w.1.property, m', ?_⟩
      change IsLocalizedModule.mk' (localizedMap P) (w.1 : S) m' =
        algebraMap S (Localization (Submonoid.map (f : R →* S) P.primeCompl)) x
      rw [← IsLocalization.mk'_algebraMap_eq_mk']
      have hcm' := congrArg
        (fun z : integralClosure (Localization.AtPrime P)
            (Localization (Submonoid.map (f : R →* S) P.primeCompl)) =>
          (z : Localization (Submonoid.map (f : R →* S) P.primeCompl))) hcm
      rw [← hmw] at hcm'
      have hclosure' (z : integralClosure R S) :
          (closureMap z : Localization (Submonoid.map (f : R →* S) P.primeCompl)) =
            algebraMap S
              (Localization (Submonoid.map (f : R →* S) P.primeCompl)) (z : S) := by
        rfl
      simp only [Subalgebra.coe_mul, RingHom.algebraMap_toAlgebra] at hcm'
      rw [hclosure'] at hcm'
      rw [hclosure'] at hcm'
      simpa only [Subalgebra.coe_mul, RingHom.algebraMap_toAlgebra,
        RingHom.codRestrict_apply, IsLocalization.mk'_eq_iff_eq_mul]
        using hcm'.symm)))

/-! ## Base change and locality -/

/-- Integrality is preserved by the tensor-product base change map. -/
theorem integral_base_change
    {R S R' : Type*} [CommRing R] [CommRing S] [CommRing R']
    (f : R →+* S) (g : R →+* R') (hf : f.IsIntegral) :
    letI : Algebra R S := f.toAlgebra
    letI : Algebra R R' := g.toAlgebra
    (Formalization.Books.Algebra.Unit14.baseChangeRingMap f g).IsIntegral := by
  let : Algebra R S := f.toAlgebra
  let : Algebra R R' := g.toAlgebra
  let : Algebra.IsIntegral R S := ⟨hf⟩
  let : Algebra R' (R' ⊗[R] S) := Algebra.TensorProduct.leftAlgebra
  let : Algebra R' (S ⊗[R] R') := Algebra.TensorProduct.rightAlgebra
  have hsource : Algebra.IsIntegral R' (R' ⊗[R] S) :=
    Algebra.IsIntegral.tensorProduct R R' S
  have htarget : Algebra.IsIntegral R' (S ⊗[R] R') :=
    (AlgEquiv.isIntegral_iff (Algebra.TensorProduct.commRight R R' S)).mp hsource
  change (algebraMap R' (S ⊗[R] R')).IsIntegral
  exact htarget.isIntegral

/-- Finiteness is preserved by the tensor-product base change map. -/
theorem finite_base_change
    {R S R' : Type*} [CommRing R] [CommRing S] [CommRing R']
    (f : R →+* S) (g : R →+* R') (hf : f.Finite) :
    letI : Algebra R S := f.toAlgebra
    letI : Algebra R R' := g.toAlgebra
    (Formalization.Books.Algebra.Unit14.baseChangeRingMap f g).Finite := by
  let : Algebra R S := f.toAlgebra
  let : Algebra R R' := g.toAlgebra
  change Module.Finite R S at hf
  let : Module.Finite R S := hf
  let : Algebra R' (R' ⊗[R] S) := Algebra.TensorProduct.leftAlgebra
  have hsource : Module.Finite R' (R' ⊗[R] S) := by infer_instance
  let : Module.Finite R' (R' ⊗[R] S) := hsource
  let : Algebra R' (S ⊗[R] R') := Algebra.TensorProduct.rightAlgebra
  have htarget : Module.Finite R' (S ⊗[R] R') :=
    Module.Finite.equiv (Algebra.TensorProduct.commRight R R' S).toLinearEquiv
  change Module.Finite R' (S ⊗[R] R')
  exact htarget

/-- Integrality and finiteness can be checked on a finite principal-open cover. -/
theorem integral_finite_local
    {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (s : Finset R) (hs : Ideal.span (s : Set R) = ⊤) :
    ((∀ r : s, (Localization.awayMap f r).IsIntegral) → f.IsIntegral) ∧
      ((∀ r : s, (Localization.awayMap f r).Finite) → f.Finite) := by
  constructor
  · intro h r
    let : Algebra R S := f.toAlgebra
    change r ∈ (integralClosure R S).toSubmodule
    apply Submodule.mem_of_span_eq_top_of_smul_pow_mem _ (s : Set R) hs
    rintro ⟨t, ht⟩
    let : Algebra (Localization.Away t) (Localization.Away (f t)) :=
      (Localization.awayMap f t).toAlgebra
    have htower : IsScalarTower R (Localization.Away t) (Localization.Away (f t)) :=
      .of_algebraMap_eq' (IsLocalization.lift_comp _).symm
    have hlocal : IsIntegral (Localization.Away t)
        (algebraMap S (Localization.Away (f t)) r) :=
      h ⟨t, ht⟩ (algebraMap _ _ r)
    obtain ⟨⟨_, n, rfl⟩, p, hp, hp'⟩ :=
      hlocal.exists_multiple_integral_of_isLocalization (.powers t)
    rw [IsScalarTower.algebraMap_eq R S, Submonoid.smul_def, Algebra.smul_def,
      IsScalarTower.algebraMap_apply R S, ← map_mul, ← Polynomial.hom_eval₂,
      IsLocalization.map_eq_zero_iff (.powers (f t))] at hp'
    obtain ⟨⟨x, m, (rfl : algebraMap R S t ^ m = x)⟩, e⟩ := hp'
    by_cases hdeg : 1 ≤ p.natDegree
    · refine ⟨m + n, p.scaleRoots (t ^ m),
        (Polynomial.monic_scaleRoots_iff _).mpr hp, ?_⟩
      have hscale := p.scaleRoots_eval₂_mul (algebraMap R S) (t ^ n • r) (t ^ m)
      simp only [pow_add, ← Algebra.smul_def, mul_smul, ← map_pow] at e hscale ⊢
      rw [hscale, ← tsub_add_cancel_of_le hdeg, pow_succ, mul_smul, e, smul_zero]
    · have hzero : p.natDegree = 0 := Nat.eq_zero_of_not_pos (by
        intro hpos
        exact hdeg (Nat.succ_le_iff.mpr hpos))
      obtain rfl : p = 1 :=
        Polynomial.eq_one_of_monic_natDegree_zero hp hzero
      exact ⟨m, by simp [Algebra.smul_def,
        show algebraMap R S t ^ m = 0 by simpa using e]⟩
  · intro h
    classical
    let := f.toAlgebra
    let := fun r : s => (Localization.awayMap f r).toAlgebra
    have (r : s) : IsLocalization
        ((Submonoid.powers (r : R)).map (algebraMap R S))
        (Localization.Away (f r)) := by
      rw [Submonoid.map_powers]
      exact Localization.isLocalization
    have : ∀ r : s,
        IsScalarTower R (Localization.Away (r : R)) (Localization.Away (f r)) :=
      fun r => IsScalarTower.of_algebraMap_eq'
        (IsLocalization.map_comp (Submonoid.powers (r : R)).le_comap_map).symm
    constructor
    replace h := fun r => (h r).1
    choose s₁ s₂ using h
    let sf := fun x : s =>
      IsLocalization.finsetIntegerMultiple (Submonoid.powers (f x)) (s₁ x)
    use s.attach.biUnion sf
    rw [Submodule.span_attach_biUnion, eq_top_iff]
    rintro x -
    apply Submodule.mem_of_span_eq_top_of_smul_pow_mem _ (s : Set R) hs _ _
    intro r
    obtain ⟨⟨_, n₁, rfl⟩, hn₁⟩ :=
      multiple_mem_span_of_mem_localization_span (Submonoid.powers (r : R))
        (Localization.Away (r : R)) (s₁ r : Set (Localization.Away (f r)))
        (algebraMap S _ x) (by rw [s₂ r]; trivial)
    dsimp only at hn₁
    rw [Submonoid.smul_def, Algebra.smul_def, IsScalarTower.algebraMap_apply R S,
      ← map_mul] at hn₁
    obtain ⟨⟨_, n₂, rfl⟩, hn₂⟩ :=
      IsLocalization.smul_mem_finsetIntegerMultiple_span (Submonoid.powers (r : R))
        (Localization.Away (f r)) _ (s₁ r) hn₁
    rw [Submonoid.smul_def, ← Algebra.smul_def, smul_smul, ← pow_add] at hn₂
    simp_rw [Submonoid.map_powers] at hn₂
    use n₂ + n₁
    exact le_iSup (fun x : s => Submodule.span R (sf x : Set S)) r hn₂

/-- If a composite is integral, then its second map is integral; the finite
analogue holds as well. -/
theorem integral_finite_permanence
    {A B C : Type*} [CommRing A] [CommRing B] [CommRing C]
    (f : A →+* B) (g : B →+* C)
    : ((g.comp f).IsIntegral → g.IsIntegral) ∧
      ((g.comp f).Finite → g.Finite) := by
  exact ⟨fun h => h.tower_top, RingHom.Finite.of_comp_finite⟩

/- The canonical `IsIntegralClosure.tower_top` is the source-facing
transitivity principle for successive integral closures. -/
/-- Integral closures are transitive in a ring tower. -/
theorem integralClosure_transitive
    {A B C B' C' : Type*}
    [CommRing A] [CommRing B] [CommRing C] [CommRing B'] [CommRing C']
    [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]
    [Algebra A B'] [Algebra B' B] [IsScalarTower A B' B]
    [Algebra B' C] [Algebra C' C] [IsScalarTower A B' C]
    [IsScalarTower B' B C]
    [IsIntegralClosure B' A B] [IsIntegralClosure C' B' C] :
    IsIntegralClosure C' A C := by
  let _ : Algebra.IsIntegral A B' := IsIntegralClosure.isIntegral_algebra A B
  refine
    { algebraMap_injective := IsIntegralClosure.algebraMap_injective C' B' C
      isIntegral_iff := ?_ }
  intro x
  constructor
  · intro hx
    exact (IsIntegralClosure.isIntegral_iff (A := C') (R := B') (B := C)).mp
      (IsIntegral.tower_top hx)
  · rintro ⟨y, hy⟩
    have hy' : IsIntegral B' (algebraMap C' C y) :=
      (IsIntegralClosure.isIntegral_iff (A := C') (R := B') (B := C)).mpr ⟨y, rfl⟩
    rw [← hy]
    exact isIntegral_trans (R := A) _ hy'

/-! ## Spectra and field consequences -/

/-- An injective integral ring map induces a surjection on prime spectra. -/
theorem primeSpectrum_comap_surjective_of_integral
    {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (hf : f.IsIntegral) (hinj : Function.Injective f) :
    Function.Surjective (PrimeSpectrum.comap f) := by
  let := f.toAlgebra
  let _ : Algebra.IsIntegral R S := ⟨hf⟩
  intro p
  have hker : RingHom.ker (algebraMap R S) ≤ p.asIdeal := by
    rw [(RingHom.injective_iff_ker_eq_bot (algebraMap R S)).mp hinj]
    exact bot_le
  have hbot : (⊥ : Ideal S).comap (algebraMap R S) ≤ p.asIdeal := by
    rw [← RingHom.ker_eq_comap_bot]
    exact hker
  obtain ⟨Q, _, hQ, hQcomap⟩ :=
    Ideal.exists_ideal_over_prime_of_isIntegral p.asIdeal (⊥ : Ideal S) hbot
  refine ⟨⟨Q, hQ⟩, ?_⟩
  apply PrimeSpectrum.ext
  exact hQcomap

/-- An integral subring of a field is a field, and the field is algebraic over
the subring. -/
theorem integral_subring_of_field
    {R K : Type*} [CommRing R] [Field K] [Algebra R K]
    [FaithfulSMul R K] [Algebra.IsIntegral R K] :
    IsField R ∧ Algebra.IsAlgebraic R K := by
  have hR : IsField R :=
    isField_of_isIntegral_of_isField (FaithfulSMul.algebraMap_injective R K)
      (Field.toIsField K)
  refine ⟨hR, ?_⟩
  let _ : Nontrivial R := hR.nontrivial
  exact ⟨fun x => (Algebra.IsIntegral.isIntegral x).isAlgebraic⟩

/-- A finite subring of a field is a field and the field is finite algebraic
over it. -/
theorem finite_subring_of_field
    {R K : Type*} [CommRing R] [Field K] [Algebra R K]
    [FaithfulSMul R K] [Module.Finite R K] :
    IsField R ∧ Module.Finite R K ∧ Algebra.IsAlgebraic R K := by
  have hR : IsField R :=
    isField_of_isIntegral_of_isField (FaithfulSMul.algebraMap_injective R K)
      (Field.toIsField K)
  have hfinite : Module.Finite R K := inferInstance
  refine ⟨hR, hfinite, ?_⟩
  let _ : Nontrivial R := hR.nontrivial
  exact inferInstance

/-- A domain that is integral over a field is a field. -/
theorem integral_domain_over_field_isField
    {k S : Type*} [Field k] [CommRing S] [Algebra k S]
    [IsDomain S] [Algebra.IsIntegral k S] :
    IsField S := by
  exact isField_of_isIntegral_of_isField' (Field.toIsField k)

/-- A finite-dimensional domain algebra over a field is a field. -/
theorem finiteDimensional_domain_over_field_isField
    {k S : Type*} [Field k] [CommRing S] [Algebra k S]
    [IsDomain S] [Module.Finite k S] :
    IsField S := by
  exact isField_of_isIntegral_of_isField' (Field.toIsField k)

/-- In an integral algebra over a field, every prime ideal is maximal. -/
theorem prime_isMaximal_of_integral_over_field
    {k S : Type*} [Field k] [CommRing S] [Algebra k S]
    [Algebra.IsIntegral k S] (p : PrimeSpectrum S) :
    p.asIdeal.IsMaximal := by
  apply Ideal.Quotient.maximal_of_isField
  exact isField_of_isIntegral_of_isField' (Field.toIsField k)

/-- Distinct primes in an integral extension with the same contraction are
incomparable. -/
theorem primes_incomparable_of_same_comap
    {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (hf : f.IsIntegral)
    (q q' : PrimeSpectrum S)
    (heq : PrimeSpectrum.comap f q = PrimeSpectrum.comap f q')
    (hneq : q ≠ q') :
    ¬ q.asIdeal ≤ q'.asIdeal ∧ ¬ q'.asIdeal ≤ q.asIdeal := by
  let _ : Algebra R S := f.toAlgebra
  let _ : Algebra.IsIntegral R S := ⟨hf⟩
  have hcomap : q.asIdeal.comap f = q'.asIdeal.comap f :=
    congrArg PrimeSpectrum.asIdeal heq
  constructor
  · intro hle
    have hlt : q.asIdeal < q'.asIdeal :=
      lt_of_le_of_ne hle (fun h => hneq (PrimeSpectrum.ext h))
    exact (ne_of_lt (Ideal.IsIntegral.comap_lt_comap hlt)) hcomap
  · intro hle
    have hlt : q'.asIdeal < q.asIdeal :=
      lt_of_le_of_ne hle (fun h => hneq (PrimeSpectrum.ext h.symm))
    exact (ne_of_lt (Ideal.IsIntegral.comap_lt_comap hlt)) hcomap.symm

/-- A finite ring map has finite fibers on prime spectra. -/
theorem finite_primeSpectrum_fiber
    {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (hf : f.Finite) (p : PrimeSpectrum R) :
    {q : PrimeSpectrum S | PrimeSpectrum.comap f q = p}.Finite := by
  let _ : Algebra R S := f.toAlgebra
  let _ : Module.Finite R S := hf
  rw [show {q : PrimeSpectrum S | PrimeSpectrum.comap f q = p} =
      PrimeSpectrum.comap f ⁻¹' {p} by ext q; simp]
  simpa only [RingHom.algebraMap_toAlgebra] using
    (Algebra.QuasiFinite.finite_comap_preimage_singleton (R := R) (S := S) p)

/-- Going up for integral ring maps. -/
theorem integral_going_up
    {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (hf : f.IsIntegral)
    (p p' : Ideal R) [hp : p.IsPrime] [hp' : p'.IsPrime]
    (hpp' : p ≤ p') (q : Ideal S) [hq : q.IsPrime]
    (hqp : q.comap f = p) :
    ∃ q' : Ideal S, q ≤ q' ∧ q'.IsPrime ∧ q'.comap f = p' := by
  have _hp : p.IsPrime := hp
  have _hq : q.IsPrime := hq
  let _ : Algebra R S := f.toAlgebra
  let _ : Algebra.IsIntegral R S := ⟨hf⟩
  have hle : q.comap (algebraMap R S) ≤ p' := by
    rw [show q.comap (algebraMap R S) = q.comap f by rfl, hqp]
    exact hpp'
  obtain ⟨q', hqle, hqprime, hqcomap⟩ :=
    Ideal.exists_ideal_over_prime_of_isIntegral (R := R) (S := S) p' q hle
  exact ⟨q', hqle, hqprime, hqcomap⟩

/-! ## Finite and finitely presented modules -/

/-- For a finite, finitely presented ring map, finite presentation of an
S-module is independent of whether scalars are restricted to R. -/
theorem finite_finitelyPresented_module_iff
    {R S M : Type*} [CommRing R] [CommRing S]
    [AddCommGroup M] [Module S M]
    (f : R →+* S) (hfinite : f.Finite)
    (hfp : f.FinitePresentation) :
    (letI : Module R M := Module.compHom M f;
      Module.FinitePresentation R M) ↔
      Module.FinitePresentation S M := by
  let _ : Algebra R S := f.toAlgebra
  let _ : Module R M := Module.compHom M f
  let _ : IsScalarTower R S M :=
    IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
  let _ : Module.Finite R S := hfinite
  let _ : Algebra.FinitePresentation R S := hfp
  let _ : Module.FinitePresentation R S :=
    Module.FinitePresentation.of_finite_of_finitePresentation R S
  constructor
  · intro hM
    let _ : Module.FinitePresentation R M := hM
    have hsourceR : Module.FinitePresentation R (S ⊗[R] M) :=
      Module.FinitePresentation.trans R (S ⊗[R] M) S
    let _ : Module.FinitePresentation R (S ⊗[R] M) := hsourceR
    let fbase : S ⊗[R] M →ₗ[S] M :=
      (LinearMap.id : M →ₗ[R] M).liftBaseChange S
    have hfbase : Function.Surjective fbase := by
      intro m
      exact ⟨1 ⊗ₜ m, by simp [fbase]⟩
    have hkerR : (LinearMap.ker (fbase.restrictScalars R)).FG :=
      Module.FinitePresentation.fg_ker (fbase.restrictScalars R) hfbase
    have hkerS : (LinearMap.ker fbase).FG := by
      apply Submodule.FG.of_restrictScalars R
      simpa only [LinearMap.ker_restrictScalars] using hkerR
    exact Module.finitePresentation_of_surjective fbase hfbase hkerS
  · intro hM
    let _ : Module.FinitePresentation S M := hM
    exact Module.FinitePresentation.trans R M S

/-! ## The final short exact sequence -/

/-- The canonical common localization used for the two ratio subalgebras. -/
abbrev ratioLocalization (R : Type u) [CommRing R] (x y : R) :=
  Localization.Away (x * y)

/-- The element denoted by `x / y` in the localization away from `x * y`. -/
noncomputable def ratioXY
    {R : Type u} [CommRing R] (x y : R) : ratioLocalization R x y := by
  let hy : IsUnit (algebraMap R (ratioLocalization R x y) y) :=
    IsLocalization.Away.isUnit_of_dvd (x * y) (dvd_mul_left y x)
  exact algebraMap R (ratioLocalization R x y) x *
    ((hy.unit⁻¹ : Units (ratioLocalization R x y)) : ratioLocalization R x y)

/-- The element denoted by `y / x` in the localization away from `x * y`. -/
noncomputable def ratioYX
    {R : Type u} [CommRing R] (x y : R) : ratioLocalization R x y := by
  let hx : IsUnit (algebraMap R (ratioLocalization R x y) x) :=
    IsLocalization.Away.isUnit_of_dvd (x * y) (dvd_mul_right x y)
  exact algebraMap R (ratioLocalization R x y) y *
    ((hx.unit⁻¹ : Units (ratioLocalization R x y)) : ratioLocalization R x y)

/-- The `R[x/y]` subalgebra in the common localization. -/
noncomputable def ratioXYSubalgebra
    {R : Type u} [CommRing R] (x y : R) :
    Subalgebra R (ratioLocalization R x y) :=
  Algebra.adjoin R ({ratioXY x y} : Set (ratioLocalization R x y))

/-- The `R[y/x]` subalgebra in the common localization. -/
noncomputable def ratioYXSubalgebra
    {R : Type u} [CommRing R] (x y : R) :
    Subalgebra R (ratioLocalization R x y) :=
  Algebra.adjoin R ({ratioYX x y} : Set (ratioLocalization R x y))

/-- The subalgebra generated by both ratios.  It is written as a supremum so
the two inclusion maps are canonical lattice inclusions. -/
noncomputable def ratioBothSubalgebra
    {R : Type u} [CommRing R] (x y : R) :
    Subalgebra R (ratioLocalization R x y) :=
  ratioXYSubalgebra x y ⊔ ratioYXSubalgebra x y

/-- The source's “generated by both ratios” description agrees with the
supremum used for the inclusion maps. -/
theorem ratioBothSubalgebra_eq_adjoin
    {R : Type u} [CommRing R] (x y : R) :
    ratioBothSubalgebra x y =
      Algebra.adjoin R ({ratioXY x y, ratioYX x y} : Set (ratioLocalization R x y)) := by
  change Algebra.adjoin R ({ratioXY x y} : Set _) ⊔
      Algebra.adjoin R ({ratioYX x y} : Set _) =
    Algebra.adjoin R ({ratioXY x y, ratioYX x y} : Set _)
  rw [← Algebra.adjoin_union]
  apply congrArg (Algebra.adjoin R)
  ext z
  simp [or_comm]

/-- Inclusion of `R[x/y]` into `R[x/y,y/x]`. -/
noncomputable def ratioXYToBoth
    {R : Type u} [CommRing R] (x y : R) :
    ratioXYSubalgebra x y →ₐ[R] ratioBothSubalgebra x y :=
  Subalgebra.inclusion le_sup_left

/-- Inclusion of `R[y/x]` into `R[x/y,y/x]`. -/
noncomputable def ratioYXToBoth
    {R : Type u} [CommRing R] (x y : R) :
    ratioYXSubalgebra x y →ₐ[R] ratioBothSubalgebra x y :=
  Subalgebra.inclusion le_sup_right

/-- The left map in the final sequence, `r ↦ (-r,r)`. -/
noncomputable def sillyNormalLeft
    {R : Type u} [CommRing R] (x y : R) :
    R →ₗ[R] ratioXYSubalgebra x y × ratioYXSubalgebra x y :=
  (-Algebra.linearMap R (ratioXYSubalgebra x y)).prod
    (Algebra.linearMap R (ratioYXSubalgebra x y))

/-- The right map in the final sequence, `(a,b) ↦ a+b`. -/
noncomputable def sillyNormalRight
    {R : Type u} [CommRing R] (x y : R) :
    (ratioXYSubalgebra x y × ratioYXSubalgebra x y) →ₗ[R]
      ratioBothSubalgebra x y :=
  (ratioXYToBoth x y).toLinearMap.comp
      (LinearMap.fst R (ratioXYSubalgebra x y) (ratioYXSubalgebra x y)) +
    (ratioYXToBoth x y).toLinearMap.comp
      (LinearMap.snd R (ratioXYSubalgebra x y) (ratioYXSubalgebra x y))

private theorem integral_of_two_ratio_presentations
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    (t u : S) (htu : t * u = 1) (a : S)
    (p q : Polynomial R)
    (hp : Polynomial.eval₂ (algebraMap R S) t p = a)
    (hq : Polynomial.eval₂ (algebraMap R S) u q = a) :
    IsIntegral R a := by
  classical
  let n : ℕ := max p.natDegree q.natDegree
  let powers : Set S :=
    Set.range (fun i : Fin (n + 1) => t ^ (i : ℕ)) ∪
      Set.range (fun i : Fin (n + 1) => u ^ (i : ℕ))
  have hpowers : powers.Finite := by
    dsimp [powers]
    exact Set.Finite.union (Set.finite_range _) (Set.finite_range _)
  let M : Submodule R S := Submodule.span R powers
  let : Module.Finite R M := Module.Finite.span_of_finite R hpowers
  have hpow (i j : ℕ) : u ^ j * t ^ i =
      if j ≤ i then t ^ (i - j) else u ^ (j - i) := by
    have hcancel (k : ℕ) : t ^ k * u ^ k = 1 := by
      rw [← mul_pow, htu, one_pow]
    by_cases hji : j ≤ i
    · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hji
      rw [if_pos (Nat.le_add_right j k), Nat.add_sub_cancel_left]
      calc
        u ^ j * t ^ (j + k) = (t ^ j * u ^ j) * t ^ k := by ring
        _ = t ^ k := by rw [hcancel]; simp
    · have hij : i ≤ j := Nat.le_of_lt (Nat.lt_of_not_ge hji)
      obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hij
      rw [if_neg (by omega), Nat.add_sub_cancel_left]
      calc
        u ^ (i + k) * t ^ i = (t ^ i * u ^ i) * u ^ k := by ring
        _ = u ^ k := by rw [hcancel]; simp
  have hpow_mem (i j : ℕ) (hi : i ≤ n) (hj : j ≤ n) :
      u ^ j * t ^ i ∈ M := by
    rw [hpow]
    split
    · apply Submodule.subset_span
      exact Or.inl ⟨⟨i - j, Nat.lt_succ_of_le ((Nat.sub_le i j).trans hi)⟩, rfl⟩
    · apply Submodule.subset_span
      exact Or.inr ⟨⟨j - i, Nat.lt_succ_of_le ((Nat.sub_le j i).trans hj)⟩, rfl⟩
  have h_eval_u (i : ℕ) (hi : i ≤ n) :
      Polynomial.eval₂ (algebraMap R S) u q * t ^ i ∈ M := by
    rw [Polynomial.eval₂_eq_sum_range' (algebraMap R S) (p := q)
      (n := n + 1) (lt_of_le_of_lt
      (le_max_right p.natDegree q.natDegree) (Nat.lt_succ_self _))]
    rw [Finset.sum_mul]
    refine Submodule.sum_mem M fun j hj => ?_
    have hjn : j ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
    simpa [Algebra.smul_def, mul_assoc, mul_left_comm, mul_comm] using
      M.smul_mem (q.coeff j) (hpow_mem i j hi hjn)
  have h_eval_t (i : ℕ) (hi : i ≤ n) :
      Polynomial.eval₂ (algebraMap R S) t p * u ^ i ∈ M := by
    rw [Polynomial.eval₂_eq_sum_range' (algebraMap R S) (p := p)
      (n := n + 1) (lt_of_le_of_lt
      (le_max_left p.natDegree q.natDegree) (Nat.lt_succ_self _))]
    rw [Finset.sum_mul]
    refine Submodule.sum_mem M fun j hj => ?_
    have hjn : j ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
    simpa [Algebra.smul_def, mul_assoc, mul_left_comm, mul_comm] using
      M.smul_mem (p.coeff j) (hpow_mem j i hjn hi)
  have h1 : (1 : S) ∈ M := by
    apply Submodule.subset_span
    exact Or.inl ⟨⟨0, Nat.zero_lt_succ _⟩, by simp⟩
  have hstable : ∀ m ∈ M, a * m ∈ M := by
    intro m hm
    refine Submodule.span_induction (p := fun z _ => a * z ∈ M) ?_ ?_ ?_ ?_ hm
    · intro z hz
      rcases hz with ⟨i, rfl⟩ | ⟨i, rfl⟩
      · rw [← hq]
        exact h_eval_u i (Nat.lt_succ_iff.mp i.isLt)
      · rw [← hp]
        exact h_eval_t i (Nat.lt_succ_iff.mp i.isLt)
    · simp
    · intro z w _ _ hz hw
      simpa [mul_add] using M.add_mem hz hw
    · intro r z _ hz
      simpa [Algebra.smul_def, mul_assoc, mul_left_comm, mul_comm] using
        M.smul_mem r hz
  exact isIntegral_of_finite_submodule M a h1 hstable

private theorem adjoin_two_ratio_sum
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    (t u : S) (htu : t * u = 1)
    (z : Algebra.adjoin R ({t, u} : Set S)) :
    ∃ a : Algebra.adjoin R ({t} : Set S),
      ∃ b : Algebra.adjoin R ({u} : Set S),
        (a : S) + b = z := by
  classical
  let tA : Algebra.adjoin R ({t} : Set S) :=
    ⟨t, Algebra.subset_adjoin (by simp)⟩
  let uB : Algebra.adjoin R ({u} : Set S) :=
    ⟨u, Algebra.subset_adjoin (by simp)⟩
  let Good : S → Prop := fun z =>
    ∃ a : Algebra.adjoin R ({t} : Set S),
      ∃ b : Algebra.adjoin R ({u} : Set S), (a : S) + b = z
  have hgood_add {z w : S} : Good z → Good w → Good (z + w) := by
    rintro ⟨a, b, hab⟩ ⟨a', b', hab'⟩
    refine ⟨a + a', b + b', ?_⟩
    dsimp at *
    rw [← hab, ← hab']
    simp only [add_left_comm, add_comm]
  have hgood_A (a : Algebra.adjoin R ({t} : Set S)) : Good (a : S) := by
    exact ⟨a, 0, by simp⟩
  have hgood_B (b : Algebra.adjoin R ({u} : Set S)) : Good (b : S) := by
    exact ⟨0, b, by simp⟩
  have hpow (i j : ℕ) : u ^ j * t ^ i =
      if j ≤ i then t ^ (i - j) else u ^ (j - i) := by
    have hcancel (k : ℕ) : t ^ k * u ^ k = 1 := by
      rw [← mul_pow, htu, one_pow]
    by_cases hji : j ≤ i
    · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hji
      rw [if_pos (Nat.le_add_right j k), Nat.add_sub_cancel_left]
      calc
        u ^ j * t ^ (j + k) = (t ^ j * u ^ j) * t ^ k := by ring
        _ = t ^ k := by rw [hcancel]; simp
    · have hij : i ≤ j := Nat.le_of_lt (Nat.lt_of_not_ge hji)
      obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hij
      rw [if_neg (by omega), Nat.add_sub_cancel_left]
      calc
        u ^ (i + k) * t ^ i = (t ^ i * u ^ i) * u ^ k := by ring
        _ = u ^ k := by rw [hcancel]; simp
  have hpow' (i j : ℕ) : t ^ i * u ^ j =
      if j ≤ i then t ^ (i - j) else u ^ (j - i) := by
    simpa [mul_comm] using hpow i j
  have hmonomial (n m : ℕ) (a b : R) :
      Good ((algebraMap R S (a * b)) * t ^ n * u ^ m) := by
    by_cases hmn : m ≤ n
    · refine ⟨algebraMap R (Algebra.adjoin R ({t} : Set S)) (a * b) *
          tA ^ (n - m), 0, ?_⟩
      dsimp [Good]
      calc
        (↑(algebraMap R (Algebra.adjoin R ({t} : Set S)) (a * b) *
            tA ^ (n - m)) : S) + ↑(0 : Algebra.adjoin R ({u} : Set S)) =
            algebraMap R S (a * b) * t ^ (n - m) := by simp [tA]
        _ = algebraMap R S (a * b) * (t ^ n * u ^ m) := by
          rw [hpow', if_pos hmn]
        _ = _ := by ring
    · refine ⟨0, algebraMap R (Algebra.adjoin R ({u} : Set S)) (a * b) *
          uB ^ (m - n), ?_⟩
      dsimp [Good]
      calc
        (↑(0 : Algebra.adjoin R ({t} : Set S)) : S) +
            ↑(algebraMap R (Algebra.adjoin R ({u} : Set S)) (a * b) *
              uB ^ (m - n)) =
            algebraMap R S (a * b) * u ^ (m - n) := by simp [uB]
        _ = algebraMap R S (a * b) * (t ^ n * u ^ m) := by
          rw [hpow', if_neg hmn]
        _ = _ := by ring
  have hpoly_monomial (n : ℕ) (a : R) (q : Polynomial R) :
      Good (Polynomial.eval₂ (algebraMap R S) t (Polynomial.monomial n a) *
        Polynomial.eval₂ (algebraMap R S) u q) := by
    induction q using Polynomial.induction_on' with
    | add q r hq hr =>
        rw [Polynomial.eval₂_add, mul_add]
        exact hgood_add hq hr
    | monomial m b =>
        convert hmonomial n m a b using 1;
          simp [Polynomial.eval₂_monomial]; ring
  have hpoly (p q : Polynomial R) :
      Good (Polynomial.eval₂ (algebraMap R S) t p *
        Polynomial.eval₂ (algebraMap R S) u q) := by
    induction p using Polynomial.induction_on' generalizing q with
    | add p r hp hr =>
        rw [Polynomial.eval₂_add, add_mul]
        exact hgood_add (hp q) (hr q)
    | monomial n a =>
        exact hpoly_monomial n a q
  have hcross (a : Algebra.adjoin R ({t} : Set S))
      (b : Algebra.adjoin R ({u} : Set S)) : Good ((a : S) * b) := by
    obtain ⟨p, hp⟩ := Algebra.adjoin_eq_exists_aeval R t a
    obtain ⟨q, hq⟩ := Algebra.adjoin_eq_exists_aeval R u b
    simpa only [Polynomial.aeval_def] using (hp ▸ hq ▸ hpoly p q)
  have hgood_mul {z w : S} : Good z → Good w → Good (z * w) := by
    rintro ⟨a, b, hab⟩ ⟨a', b', hab'⟩
    have hs :=
      hgood_add (hgood_add (hgood_add (hgood_A (a * a'))
        (hcross a b')) (hcross a' b)) (hgood_B (b * b'))
    rw [← hab, ← hab']
    dsimp [Good] at hs ⊢
    rcases hs with ⟨A, B, hAB⟩
    refine ⟨A, B, ?_⟩
    rw [hAB]
    simp only [mul_add, add_mul]
    ring_nf
  have hgood : Good (z : S) := by
    refine Algebra.adjoin_induction (p := fun z _ => Good z) ?_ ?_ ?_ ?_ z.property
    · intro z hz
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
      rcases hz with rfl | rfl
      · exact hgood_A tA
      · exact hgood_B uB
    · intro r
      simpa using hgood_A (algebraMap R (Algebra.adjoin R ({t} : Set S)) r)
    · intro z w hz hw hzw hww
      exact hgood_add hzw hww
    · intro z w hz hw hzw hww
      exact hgood_mul hzw hww
  exact hgood

private theorem silly_normal_right_apply
    {R : Type u} [CommRing R] (x y : R)
    (a : ratioXYSubalgebra x y) (b : ratioYXSubalgebra x y) :
    ((sillyNormalRight x y (a, b) : ratioBothSubalgebra x y) :
      ratioLocalization R x y) = (a : ratioLocalization R x y) + b := by
  simp only [sillyNormalRight, LinearMap.add_apply, LinearMap.comp_apply,
    LinearMap.fst_apply, LinearMap.snd_apply]
  simp only [Subalgebra.coe_add, AlgHom.toLinearMap_apply]
  have ha :
      (((ratioXYToBoth x y) a : ratioBothSubalgebra x y) :
        ratioLocalization R x y) = a := by
    exact Subalgebra.coe_inclusion _ _
  have hb :
      (((ratioYXToBoth x y) b : ratioBothSubalgebra x y) :
        ratioLocalization R x y) = b := by
    exact Subalgebra.coe_inclusion _ _
  rw [ha, hb]

private theorem silly_normal_right_surjective
    {R : Type u} [CommRing R] (x y : R)
    (hxy : (ratioXY x y : ratioLocalization R x y) * ratioYX x y = 1) :
    Function.Surjective (sillyNormalRight x y) := by
  intro z
  let z' : Algebra.adjoin R
      ({ratioXY x y, ratioYX x y} : Set (ratioLocalization R x y)) :=
    ⟨(z : ratioLocalization R x y), by
      rw [← ratioBothSubalgebra_eq_adjoin]
      exact z.property⟩
  obtain ⟨a, b, hab⟩ := adjoin_two_ratio_sum
    (ratioXY x y) (ratioYX x y) hxy z'
  let a' : ratioXYSubalgebra x y :=
    ⟨(a : ratioLocalization R x y), by
      change (a : ratioLocalization R x y) ∈
        Algebra.adjoin R ({ratioXY x y} : Set _)
      exact a.property⟩
  let b' : ratioYXSubalgebra x y :=
    ⟨(b : ratioLocalization R x y), by
      change (b : ratioLocalization R x y) ∈
        Algebra.adjoin R ({ratioYX x y} : Set _)
      exact b.property⟩
  refine ⟨(a', b'), ?_⟩
  apply Subtype.ext
  rw [silly_normal_right_apply]
  simpa [a', b', z'] using hab

/- The final source sequence is short exact for nonzerodivisors when the base
ring is integrally closed in either of the two one-element localizations. -/
theorem silly_normal_short_exact
    {R : Type u} [CommRing R] (x y : R)
    (hx : x ∈ nonZeroDivisors R) (hy : y ∈ nonZeroDivisors R)
    (hclosed :
      IsIntegrallyClosedIn R (Localization.Away x) ∨
        IsIntegrallyClosedIn R (Localization.Away y)) :
    Function.Injective (sillyNormalLeft x y) ∧
      Function.Exact (sillyNormalLeft x y) (sillyNormalRight x y) ∧
      Function.Surjective (sillyNormalRight x y) := by
  /-
  classical
  let hxunit : IsUnit (algebraMap R (ratioLocalization R x y) x) :=
    IsLocalization.Away.isUnit_of_dvd (x * y) (dvd_mul_right x y)
  let hyunit : IsUnit (algebraMap R (ratioLocalization R x y) y) :=
    IsLocalization.Away.isUnit_of_dvd (x * y) (dvd_mul_left y x)
  have hxi : (algebraMap R (ratioLocalization R x y) x) *
      ((hxunit.unit⁻¹ : Units (ratioLocalization R x y)) :
        ratioLocalization R x y) = 1 := by
    calc
      _ = (hxunit.unit : ratioLocalization R x y) *
          ((hxunit.unit⁻¹ : Units (ratioLocalization R x y)) :
            ratioLocalization R x y) := by rw [hxunit.unit_spec]
      _ = 1 := hxunit.unit.mul_inv
  have hyi : (algebraMap R (ratioLocalization R x y) y) *
      ((hyunit.unit⁻¹ : Units (ratioLocalization R x y)) :
        ratioLocalization R x y) = 1 := by
    calc
      _ = (hyunit.unit : ratioLocalization R x y) *
          ((hyunit.unit⁻¹ : Units (ratioLocalization R x y)) :
            ratioLocalization R x y) := by rw [hyunit.unit_spec]
      _ = 1 := hyunit.unit.mul_inv
  have hxy : (ratioXY x y : ratioLocalization R x y) * ratioYX x y = 1 := by
    change ((algebraMap R (ratioLocalization R x y) x) *
        ((hyunit.unit⁻¹ : Units (ratioLocalization R x y)) :
          ratioLocalization R x y)) *
      ((algebraMap R (ratioLocalization R x y) y) *
        ((hxunit.unit⁻¹ : Units (ratioLocalization R x y)) :
          ratioLocalization R x y)) = 1
    calc
      _ = ((algebraMap R (ratioLocalization R x y) x) *
          ((hxunit.unit⁻¹ : Units (ratioLocalization R x y)) :
            ratioLocalization R x y)) *
        ((algebraMap R (ratioLocalization R x y) y) *
          ((hyunit.unit⁻¹ : Units (ratioLocalization R x y)) :
            ratioLocalization R x y)) := by ring
      _ = 1 := by rw [hxi, hyi]; simp
  have hpow (t u : ratioLocalization R x y) (h : t * u = 1) (i j : ℕ) :
      u ^ j * t ^ i =
        if j ≤ i then t ^ (i - j) else u ^ (j - i) := by
    have hcancel (n : ℕ) : t ^ n * u ^ n = 1 := by
      rw [← mul_pow, h, one_pow]
    by_cases hji : j ≤ i
    · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hji
      rw [if_pos (Nat.le_add_right j k), Nat.add_sub_cancel_left]
      calc
        u ^ j * t ^ (j + k) = (t ^ j * u ^ j) * t ^ k := by ring
        _ = t ^ k := by rw [hcancel]; simp
    · have hij : i ≤ j := Nat.le_of_lt (Nat.lt_of_not_ge hji)
      obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hij
      rw [if_neg (by omega), Nat.add_sub_cancel_left]
      calc
        u ^ (i + k) * t ^ i = (t ^ i * u ^ i) * u ^ k := by ring
        _ = u ^ k := by rw [hcancel]; simp
  let tA : ratioXYSubalgebra x y :=
    ⟨ratioXY x y, by exact Algebra.subset_adjoin (by simp)⟩
  let uB : ratioYXSubalgebra x y :=
    ⟨ratioYX x y, by exact Algebra.subset_adjoin (by simp)⟩
  let Good : ratioLocalization R x y → Prop :=
    fun z => ∃ a : ratioXYSubalgebra x y, ∃ b : ratioYXSubalgebra x y,
      (a : ratioLocalization R x y) + b = z
  have hgood_add {z w : ratioLocalization R x y} :
      Good z → Good w → Good (z + w) := by
    rintro ⟨a, b, hab⟩ ⟨a', b', hab'⟩
    refine ⟨a + a', b + b', ?_⟩
    dsimp at *
    rw [← hab, ← hab']
    simp only [add_left_comm, add_comm]
  have hgood_A (a : ratioXYSubalgebra x y) : Good (a : ratioLocalization R x y) := by
    exact ⟨a, 0, by simp⟩
  have hgood_B (b : ratioYXSubalgebra x y) : Good (b : ratioLocalization R x y) := by
    exact ⟨0, b, by simp⟩
  have hgood_monomial (n m : ℕ) (a b : R)
      (hpow' : (ratioXY x y) ^ n * (ratioYX x y) ^ m =
        if m ≤ n then (ratioXY x y) ^ (n - m)
        else (ratioYX x y) ^ (m - n)) :
      Good ((algebraMap R (ratioLocalization R x y) (a * b)) *
        (ratioXY x y) ^ n * (ratioYX x y) ^ m) := by
    by_cases hmn : m ≤ n
    · refine ⟨algebraMap R (ratioXYSubalgebra x y) (a * b) * tA ^ (n - m), 0, ?_⟩
      dsimp [Good]
      calc
        (↑(algebraMap R (ratioXYSubalgebra x y) (a * b) * tA ^ (n - m)) :
            ratioLocalization R x y) + ↑(0 : ratioYXSubalgebra x y) =
            (algebraMap R (ratioLocalization R x y) (a * b)) *
              (ratioXY x y) ^ (n - m) := by simp [tA]
        _ = (algebraMap R (ratioLocalization R x y) (a * b)) *
            ((ratioXY x y) ^ n * (ratioYX x y) ^ m) := by
              rw [hpow', if_pos hmn]
        _ = _ := by ring
    · refine ⟨0, algebraMap R (ratioYXSubalgebra x y) (a * b) * uB ^ (m - n), ?_⟩
      dsimp [Good]
      calc
        (↑(0 : ratioXYSubalgebra x y) : ratioLocalization R x y) +
            ↑(algebraMap R (ratioYXSubalgebra x y) (a * b) * uB ^ (m - n)) =
            (algebraMap R (ratioLocalization R x y) (a * b)) *
              (ratioYX x y) ^ (m - n) := by simp [uB]
        _ = (algebraMap R (ratioLocalization R x y) (a * b)) *
            ((ratioXY x y) ^ n * (ratioYX x y) ^ m) := by
              rw [hpow', if_neg hmn]
        _ = _ := by ring
  have hpow' (n m : ℕ) :
      (ratioXY x y) ^ n * (ratioYX x y) ^ m =
        if m ≤ n then (ratioXY x y) ^ (n - m)
        else (ratioYX x y) ^ (m - n) := by
    simpa [mul_comm] using hpow (ratioXY x y) (ratioYX x y) hxy n m
  have hpoly_monomial (n : ℕ) (a : R) (q : Polynomial R) :
      Good (Polynomial.eval₂ (algebraMap R (ratioLocalization R x y))
        (ratioXY x y) (Polynomial.monomial n a) *
        Polynomial.eval₂ (algebraMap R (ratioLocalization R x y))
          (ratioYX x y) q) := by
    induction q using Polynomial.induction_on' with
    | add q r hq hr =>
        rw [Polynomial.eval₂_add, mul_add]
        exact hgood_add hq hr
    | monomial m b =>
        convert hgood_monomial n m a b (hpow' n m) using 1 <;>
          simp [Polynomial.eval₂_monomial] <;> ring
  have hpoly (p q : Polynomial R) :
      Good (Polynomial.eval₂ (algebraMap R (ratioLocalization R x y))
        (ratioXY x y) p *
        Polynomial.eval₂ (algebraMap R (ratioLocalization R x y))
          (ratioYX x y) q) := by
    induction p using Polynomial.induction_on' generalizing q with
    | add p r hp hr =>
        rw [Polynomial.eval₂_add, add_mul]
        exact hgood_add (hp q) (hr q)
    | monomial n a =>
        exact hpoly_monomial n a q
  have hcross (a : ratioXYSubalgebra x y) (b : ratioYXSubalgebra x y) :
      Good ((a : ratioLocalization R x y) * b) := by
    obtain ⟨p, hp⟩ := Algebra.adjoin_eq_exists_aeval R (ratioXY x y) a
    obtain ⟨q, hq⟩ := Algebra.adjoin_eq_exists_aeval R (ratioYX x y) b
    simpa only [Polynomial.aeval_def] using (hp ▸ hq ▸ hpoly p q)
  have hgood_mul {z w : ratioLocalization R x y} :
      Good z → Good w → Good (z * w) := by
    rintro ⟨a, b, hab⟩ ⟨a', b', hab'⟩
    have hs :=
      hgood_add (hgood_add (hgood_add (hgood_A (a * a'))
        (hcross a b')) (hcross a' b)) (hgood_B (b * b'))
    rw [← hab, ← hab']
    dsimp [Good] at hs ⊢
    rcases hs with ⟨A, B, hAB⟩
    refine ⟨A, B, ?_⟩
    rw [hAB]
    simp only [mul_add, add_mul]
    ring_nf
  have hgood_both (z : ratioLocalization R x y)
      (hz : z ∈ ratioBothSubalgebra x y) : Good z := by
    rw [ratioBothSubalgebra_eq_adjoin] at hz
    refine Algebra.adjoin_induction (p := fun z _ => Good z) ?_ ?_ ?_ ?_ hz
    · intro z hz
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
      rcases hz with rfl | rfl
      · exact hgood_A tA
      · exact hgood_B uB
    · intro r
      simpa using hgood_A (algebraMap R (ratioXYSubalgebra x y) r)
    · intro z w hz hw hzw hww
      exact hgood_add hzw hww
    · intro z w hz hw hzw hww
      exact hgood_mul hzw hww
  have hsurj : Function.Surjective (sillyNormalRight x y) := by
    intro z
    obtain ⟨a, b, hab⟩ := hgood_both (z : ratioLocalization R x y) z.property
    refine ⟨(a, b), ?_⟩
    apply Subtype.ext
    change (a : ratioLocalization R x y) + b = z
    exact hab
  have hxyreg : x * y ∈ nonZeroDivisors R :=
    (mul_mem_nonZeroDivisors).2 ⟨hx, hy⟩
  have hinjR : Function.Injective
      (algebraMap R (ratioLocalization R x y)) :=
    IsLocalization.injective _
      (Submonoid.powers_le.mpr hxyreg)
  have hinjLeft : Function.Injective (sillyNormalLeft x y) := by
    intro r s hrs
    apply hinjR
    have hsecond := congrArg (fun p => (p.2 : ratioLocalization R x y)) hrs
    simpa [sillyNormalLeft] using hsecond
  refine ⟨hinjLeft, ?_, hsurj⟩
  sorry -/
  classical
  let hxunit : IsUnit (algebraMap R (ratioLocalization R x y) x) :=
    IsLocalization.Away.isUnit_of_dvd (x * y) (dvd_mul_right x y)
  let hyunit : IsUnit (algebraMap R (ratioLocalization R x y) y) :=
    IsLocalization.Away.isUnit_of_dvd (x * y) (dvd_mul_left y x)
  have hxi : (algebraMap R (ratioLocalization R x y) x) *
      ((hxunit.unit⁻¹ : Units (ratioLocalization R x y)) :
        ratioLocalization R x y) = 1 := by
    calc
      _ = (hxunit.unit : ratioLocalization R x y) *
          ((hxunit.unit⁻¹ : Units (ratioLocalization R x y)) :
            ratioLocalization R x y) := by rw [hxunit.unit_spec]
      _ = 1 := hxunit.unit.mul_inv
  have hyi : (algebraMap R (ratioLocalization R x y) y) *
      ((hyunit.unit⁻¹ : Units (ratioLocalization R x y)) :
        ratioLocalization R x y) = 1 := by
    calc
      _ = (hyunit.unit : ratioLocalization R x y) *
          ((hyunit.unit⁻¹ : Units (ratioLocalization R x y)) :
            ratioLocalization R x y) := by rw [hyunit.unit_spec]
      _ = 1 := hyunit.unit.mul_inv
  have hxy : (ratioXY x y : ratioLocalization R x y) * ratioYX x y = 1 := by
    change ((algebraMap R (ratioLocalization R x y) x) *
        ((hyunit.unit⁻¹ : Units (ratioLocalization R x y)) :
          ratioLocalization R x y)) *
      ((algebraMap R (ratioLocalization R x y) y) *
        ((hxunit.unit⁻¹ : Units (ratioLocalization R x y)) :
          ratioLocalization R x y)) = 1
    calc
      _ = ((algebraMap R (ratioLocalization R x y) x) *
          ((hxunit.unit⁻¹ : Units (ratioLocalization R x y)) :
            ratioLocalization R x y)) *
        ((algebraMap R (ratioLocalization R x y) y) *
          ((hyunit.unit⁻¹ : Units (ratioLocalization R x y)) :
            ratioLocalization R x y)) := by ring
      _ = 1 := by rw [hxi, hyi]; simp
  have hxyreg : x * y ∈ nonZeroDivisors R :=
    (mul_mem_nonZeroDivisors).2 ⟨hx, hy⟩
  have hinjR : Function.Injective
      (algebraMap R (ratioLocalization R x y)) :=
    IsLocalization.injective _ (Submonoid.powers_le.mpr hxyreg)
  have hinjLeft : Function.Injective (sillyNormalLeft x y) := by
    intro r s hrs
    apply hinjR
    have hsecond := congrArg (fun p => (p.2 : ratioLocalization R x y)) hrs
    simpa [sillyNormalLeft] using hsecond
  have hsurj : Function.Surjective (sillyNormalRight x y) := by
    exact silly_normal_right_surjective x y hxy
  refine ⟨hinjLeft, ?_, hsurj⟩
  intro z
  have hzero : z ∈ Set.range (sillyNormalLeft x y) →
      sillyNormalRight x y z = 0 := by
    rintro ⟨r, rfl⟩
    apply Subtype.ext
    change ((sillyNormalRight x y
        (-algebraMap R (ratioXYSubalgebra x y) r,
          algebraMap R (ratioYXSubalgebra x y) r) :
        ratioBothSubalgebra x y) : ratioLocalization R x y) = 0
    rw [silly_normal_right_apply]
    simp
  have hrange : sillyNormalRight x y z = 0 →
      z ∈ Set.range (sillyNormalLeft x y) := by
    intro hz
    have hab0 : (z.1 : ratioLocalization R x y) + z.2 = 0 := by
      have h := congrArg (fun w : ratioBothSubalgebra x y =>
        (w : ratioLocalization R x y)) hz
      change ((sillyNormalRight x y (z.1, z.2) : ratioBothSubalgebra x y) :
        ratioLocalization R x y) = 0 at h
      rw [silly_normal_right_apply] at h
      exact h
    have hneg : -(z.1 : ratioLocalization R x y) = z.2 := by
      exact (eq_neg_of_add_eq_zero_right hab0).symm
    have hneg' : (z.1 : ratioLocalization R x y) =
        -(z.2 : ratioLocalization R x y) := by
      simpa using congrArg Neg.neg hneg
    obtain ⟨p, hp⟩ := Algebra.adjoin_eq_exists_aeval R (ratioXY x y) (-z.1)
    obtain ⟨q, hq⟩ := Algebra.adjoin_eq_exists_aeval R (ratioYX x y) z.2
    have hp' : Polynomial.eval₂ (algebraMap R (ratioLocalization R x y))
        (ratioXY x y) p = z.2 := by
      calc
        _ = ((-z.1 : ratioXYSubalgebra x y) : ratioLocalization R x y) := by
          simpa only [Polynomial.aeval_def] using hp
        _ = -(z.1 : ratioLocalization R x y) := by rfl
        _ = z.2 := hneg
    have hq' : Polynomial.eval₂ (algebraMap R (ratioLocalization R x y))
        (ratioYX x y) q = z.2 := by
      simpa only [Polynomial.aeval_def] using hq
    have hzint : IsIntegral R (z.2 : ratioLocalization R x y) :=
      integral_of_two_ratio_presentations (ratioXY x y) (ratioYX x y) hxy
        (z.2 : ratioLocalization R x y) p q hp' hq'
    let xunit : IsUnit (algebraMap R (Localization.Away x) x) :=
      IsLocalization.Away.algebraMap_isUnit x
    let mapX : Localization.Away x →ₐ[R] ratioLocalization R x y :=
      IsLocalization.Away.liftAlgHom x (f := Algebra.ofId R
        (ratioLocalization R x y)) hxunit
    have hinjAwayX : Function.Injective
        (algebraMap R (Localization.Away x)) :=
      IsLocalization.injective _ (Submonoid.powers_le.mpr hx)
    have hmapunits : ∀ s : Submonoid.powers x,
        IsUnit ((Algebra.ofId R (ratioLocalization R x y)).toRingHom s) := by
      intro s
      obtain ⟨n, hn⟩ := s.2
      rw [← hn, map_pow]
      exact IsUnit.pow _ hxunit
    have hinjX : Function.Injective mapX := by
      change Function.Injective
        (IsLocalization.lift (M := Submonoid.powers x)
          (g := (Algebra.ofId R (ratioLocalization R x y)).toRingHom) hmapunits)
      rw [IsLocalization.lift_injective_iff]
      intro a b
      constructor
      · intro h
        exact congrArg (Algebra.ofId R (ratioLocalization R x y)).toRingHom
          (hinjAwayX h)
      · intro h
        have hab : a = b := hinjR (by simpa using h)
        exact congrArg (algebraMap R (Localization.Away x)) hab
    let invX : Localization.Away x :=
      ((xunit.unit⁻¹ : Units (Localization.Away x)) : Localization.Away x)
    have hinvX : mapX invX =
        ((hxunit.unit⁻¹ : Units (ratioLocalization R x y)) :
          ratioLocalization R x y) := by
      apply hxunit.mul_left_cancel
      calc
        _ = mapX (algebraMap R (Localization.Away x) x) * mapX invX := by
          rw [mapX.commutes]
        _ = mapX (algebraMap R (Localization.Away x) x * invX) := by
          exact (mapX.map_mul _ _).symm
        _ = 1 := by
          rw [← xunit.unit_spec]
          simp [invX]
        _ = _ := hxi.symm
    let yX : Localization.Away x :=
      algebraMap R (Localization.Away x) y * invX
    have hratioYX : mapX yX = ratioYX x y := by
      dsimp [yX, ratioYX]
      calc
        mapX (algebraMap R (Localization.Away x) y * invX) =
            mapX (algebraMap R (Localization.Away x) y) * mapX invX :=
          mapX.map_mul _ _
        _ = _ := by rw [mapX.commutes, hinvX]
    let betaX : Localization.Away x :=
      Polynomial.eval₂ (algebraMap R (Localization.Away x)) yX q
    have hbetaX : mapX betaX = (z.2 : ratioLocalization R x y) := by
      dsimp [betaX]
      change (mapX.toRingHom)
          (Polynomial.eval₂ (algebraMap R (Localization.Away x)) yX q) = _
      rw [Polynomial.hom_eval₂]
      have hmapXbase :
          mapX.toRingHom.comp (algebraMap R (Localization.Away x)) =
            algebraMap R (ratioLocalization R x y) := by
        ext r
        exact mapX.commutes r
      have hyX' : mapX.toRingHom yX = ratioYX x y := by
        exact hratioYX
      rw [hmapXbase, hyX']
      simpa only [mapX.commutes, RingHom.coe_comp, Function.comp_apply] using hq'
    have hbetaXint : IsIntegral R betaX := by
      apply (isIntegral_algHom_iff mapX hinjX).mp
      rw [hbetaX]
      exact hzint
    rcases hclosed with hclosed | hclosed
    · let : IsIntegrallyClosedIn R (Localization.Away x) := hclosed
      obtain ⟨r, hr⟩ :=
        IsIntegrallyClosedIn.algebraMap_eq_of_integral hbetaXint
      refine ⟨r, ?_⟩
      have hb : (algebraMap R (ratioLocalization R x y) r) =
          (z.2 : ratioLocalization R x y) := by
        calc
          _ = mapX (algebraMap R (Localization.Away x) r) :=
            (mapX.commutes r).symm
          _ = mapX betaX := by rw [hr]
          _ = _ := hbetaX
      apply Prod.ext
      · apply Subtype.ext
        calc
          (-algebraMap R (ratioXYSubalgebra x y) r :
              ratioLocalization R x y) =
              -(algebraMap R (ratioLocalization R x y) r) := by rfl
          _ = -(z.2 : ratioLocalization R x y) := by rw [hb]
          _ = (z.1 : ratioLocalization R x y) := hneg'.symm
      · apply Subtype.ext
        exact hb
    · let yunitAway : IsUnit (algebraMap R (Localization.Away y) y) :=
          IsLocalization.Away.algebraMap_isUnit y
      let mapY : Localization.Away y →ₐ[R] ratioLocalization R x y :=
        IsLocalization.Away.liftAlgHom y (f := Algebra.ofId R
          (ratioLocalization R x y)) hyunit
      have hinjAwayY : Function.Injective
          (algebraMap R (Localization.Away y)) :=
        IsLocalization.injective _ (Submonoid.powers_le.mpr hy)
      have hmapunitsY : ∀ s : Submonoid.powers y,
          IsUnit ((Algebra.ofId R (ratioLocalization R x y)).toRingHom s) := by
        intro s
        obtain ⟨n, hn⟩ := s.2
        rw [← hn, map_pow]
        exact IsUnit.pow _ hyunit
      have hinjY : Function.Injective mapY := by
        change Function.Injective
          (IsLocalization.lift (M := Submonoid.powers y)
            (g := (Algebra.ofId R (ratioLocalization R x y)).toRingHom)
            hmapunitsY)
        rw [IsLocalization.lift_injective_iff]
        intro a b
        constructor
        · intro h
          exact congrArg (Algebra.ofId R (ratioLocalization R x y)).toRingHom
            (hinjAwayY h)
        · intro h
          have hab : a = b := hinjR (by simpa using h)
          exact congrArg (algebraMap R (Localization.Away y)) hab
      let invY : Localization.Away y :=
        ((yunitAway.unit⁻¹ : Units (Localization.Away y)) : Localization.Away y)
      have hinvY : mapY invY =
          ((hyunit.unit⁻¹ : Units (ratioLocalization R x y)) :
            ratioLocalization R x y) := by
        apply hyunit.mul_left_cancel
        calc
          _ = mapY (algebraMap R (Localization.Away y) y) * mapY invY := by
            rw [mapY.commutes]
          _ = mapY (algebraMap R (Localization.Away y) y * invY) :=
            (mapY.map_mul _ _).symm
          _ = 1 := by
            rw [← yunitAway.unit_spec]
            simp [invY]
          _ = _ := hyi.symm
      let xY : Localization.Away y :=
        algebraMap R (Localization.Away y) x * invY
      have hratioXY : mapY xY = ratioXY x y := by
        dsimp [xY, ratioXY]
        calc
          mapY (algebraMap R (Localization.Away y) x * invY) =
              mapY (algebraMap R (Localization.Away y) x) * mapY invY :=
            mapY.map_mul _ _
          _ = _ := by rw [mapY.commutes, hinvY]
      let betaY : Localization.Away y :=
        Polynomial.eval₂ (algebraMap R (Localization.Away y)) xY p
      have hbetaY : mapY betaY = (z.2 : ratioLocalization R x y) := by
        dsimp [betaY]
        change (mapY.toRingHom)
            (Polynomial.eval₂ (algebraMap R (Localization.Away y)) xY p) = _
        rw [Polynomial.hom_eval₂]
        have hmapYbase :
            mapY.toRingHom.comp (algebraMap R (Localization.Away y)) =
              algebraMap R (ratioLocalization R x y) := by
          ext r
          exact mapY.commutes r
        have hxY' : mapY.toRingHom xY = ratioXY x y := by
          exact hratioXY
        rw [hmapYbase, hxY']
        simpa only [mapY.commutes, RingHom.coe_comp, Function.comp_apply] using hp'
      have hbetaYint : IsIntegral R betaY := by
        apply (isIntegral_algHom_iff mapY hinjY).mp
        rw [hbetaY]
        exact hzint
      let : IsIntegrallyClosedIn R (Localization.Away y) := hclosed
      obtain ⟨r, hr⟩ :=
        IsIntegrallyClosedIn.algebraMap_eq_of_integral hbetaYint
      refine ⟨r, ?_⟩
      have hb : (algebraMap R (ratioLocalization R x y) r) =
          (z.2 : ratioLocalization R x y) := by
        calc
          _ = mapY (algebraMap R (Localization.Away y) r) :=
            (mapY.commutes r).symm
          _ = mapY betaY := by rw [hr]
          _ = _ := hbetaY
      apply Prod.ext
      · apply Subtype.ext
        calc
          (-algebraMap R (ratioXYSubalgebra x y) r :
              ratioLocalization R x y) =
              -(algebraMap R (ratioLocalization R x y) r) := by rfl
          _ = -(z.2 : ratioLocalization R x y) := by rw [hb]
          _ = (z.1 : ratioLocalization R x y) := hneg'.symm
      · apply Subtype.ext
        exact hb
  exact ⟨hrange, hzero⟩

end

end Formalization.Books.Algebra.Unit36
