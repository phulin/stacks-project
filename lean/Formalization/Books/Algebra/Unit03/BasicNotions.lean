import Mathlib.Algebra.EuclideanDomain.Defs
import Mathlib.Algebra.Exact.Basic
import Mathlib.Algebra.Category.ModuleCat.Free
import Mathlib.Algebra.Group.Idempotent
import Mathlib.Algebra.GroupWithZero.Basic
import Mathlib.Algebra.Module.FinitePresentation
import Mathlib.Algebra.Module.LocalizedModule.Exact
import Mathlib.Data.Finset.Sort
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.LinearAlgebra.FreeModule.Basic
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.FinitePresentation
import Mathlib.RingTheory.FiniteType
import Mathlib.RingTheory.Ideal.Maps
import Mathlib.RingTheory.Ideal.Maximal
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.RingTheory.Ideal.Quotient.Basic
import Mathlib.RingTheory.Ideal.Span
import Mathlib.RingTheory.Jacobson.Radical
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.Localization.LocalizationLocalization
import Mathlib.RingTheory.Localization.Module
import Mathlib.RingTheory.Localization.Submodule
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
import Mathlib.RingTheory.Noetherian.Defs
import Mathlib.RingTheory.UniqueFactorizationDomain.Defs

/-!
# Basic notions

This file records the precise declarations from Chapter 3 of the algebra book.
The standard notions in the list are represented by Mathlib's existing classes,
predicates, and constructions; the declarations below expose the source-facing
assertions which are not already a single canonical declaration.
-/

namespace Formalization.Books.Algebra.Unit03

open Set

universe u v w

/-! ### Rings, elements, finiteness, and fields -/

-- A ring, nilpotent element, zerodivisor, unit, idempotent, and ring homomorphism
-- are respectively `CommRing`, `IsNilpotent`, membership in `zeroDivisors`,
-- `IsUnit`, `IsIdempotentElem`, and `RingHom`.

def trivialIdempotent {R : Type u} [MulOneClass R] [Zero R] (e : R) : Prop :=
  IsIdempotentElem e ∧ (e = 1 ∨ e = 0)

-- The finiteness notions in the list are `RingHom.FinitePresentation`,
-- `RingHom.FiniteType`, and `RingHom.Finite`.
-- Domain, reduced, and Noetherian are represented by `IsDomain`, `IsReduced`,
-- and `IsNoetherianRing`.  A PID is `IsDomain` together with
-- `IsPrincipalIdealRing`; a UFD is `IsDomain` together with
-- `UniqueFactorizationMonoid`; Euclidean domains, DVRs, fields, and field
-- extensions use `EuclideanDomain`, `IsDiscreteValuationRing`, `Field`, and
-- `Algebra`, respectively.

-- Algebraicity and transcendence use `Algebra.IsAlgebraic`, `IsAlgebraic`,
-- `IsTranscendenceBasis`, `Algebra.trdeg`, and `IsAlgClosed`.

theorem exists_algHom_of_algebraic_of_algClosed
    {K L Ω : Type*} [Field K] [Field L] [Field Ω]
    [Algebra K L] [Algebra K Ω] [IsAlgClosed Ω]
    (hL : Algebra.IsAlgebraic K L) : Nonempty (L →ₐ[K] Ω) := by
  let _ : Algebra.IsAlgebraic K L := hL
  exact ⟨IsAlgClosed.lift⟩

/-! ### Ideals -/

-- `Ideal` and `Ideal.IsRadical` are the canonical ideal and radical-ideal
-- notions, while `Ideal.radical` is the radical construction.
-- The nilpotence of an ideal is the existing predicate `IsNilpotent I`,
-- which unfolds to `∃ n : ℕ, I ^ n = 0`.

def locallyNilpotentIdeal {R : Type u} [CommRing R] (I : Ideal R) : Prop :=
  ∀ x : R, x ∈ I → IsNilpotent x

theorem prime_mul_le_iff
    {R : Type u} [CommRing R] {p I J : Ideal R} (hp : p.IsPrime) :
    I * J ≤ p ↔ I ≤ p ∨ J ≤ p := by
  exact hp.mul_le

theorem exists_maximal_ideal (R : Type u) [CommRing R] [Nontrivial R] :
    ∃ I : Ideal R, I.IsMaximal := by
  exact Ideal.exists_maximal R

theorem jacobson_radical_eq_sInf_maximal
    (R : Type u) [CommRing R] :
    Ring.jacobson R = sInf {I : Ideal R | I.IsMaximal} := by
  exact Ring.jacobson_eq_sInf_isMaximal R

-- `Ideal.span`, `R ⧸ I`, `Ideal.comap`, and `Ideal.map` are the generated
-- ideal, quotient ring, inverse-image ideal, and extended ideal.

theorem ideal_isPrime_iff_quotient_isDomain
    {R : Type u} [CommRing R] (I : Ideal R) :
    I.IsPrime ↔ IsDomain (R ⧸ I) := by
  exact (Ideal.Quotient.isDomain_iff_prime (I := I)).symm

theorem ideal_isMaximal_iff_quotient_isField
    {R : Type u} [CommRing R] (I : Ideal R) :
    I.IsMaximal ↔ IsField (R ⧸ I) := by
  exact Ideal.Quotient.maximal_ideal_iff_isField_quotient I

theorem comap_prime_ideal
    {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S) (p : Ideal S)
    [p.IsPrime] :
    (p.comap f).IsPrime := by
  exact Ideal.comap_isPrime f p

/-! ### Modules -/

-- `Module`, `Submodule`, `IsNoetherian`, `Module.Finite`,
-- `Module.FinitePresentation`, and `Module.Free` are the canonical module
-- notions.  The annihilator of an element is a span-annihilator.

def annihilatorOf {R : Type u} {M : Type v} [CommRing R] [AddCommGroup M] [Module R M]
    (m : M) : Ideal R :=
  (Submodule.span R ({m} : Set M)).annihilator

theorem annihilatorOf_mem_iff {R : Type u} {M : Type v} [CommRing R] [AddCommGroup M] [Module R M]
    (m : M) (r : R) :
    r ∈ annihilatorOf m ↔ r • m = 0 := by
  exact Submodule.mem_annihilator_span_singleton m r

theorem free_of_short_exact
    {R : Type u} {K L M : Type*} [Ring R]
    [AddCommGroup K] [AddCommGroup L] [AddCommGroup M]
    [Module R K] [Module R L] [Module R M]
    (f : K →ₗ[R] L) (g : L →ₗ[R] M)
    (hf : Function.Injective f) (hexact : Function.Exact f g)
    (hg : Function.Surjective g) [Module.Free R K] [Module.Free R M] :
    Module.Free R L := by
  obtain ⟨l, hl⟩ := g.exists_rightInverse_of_surjective (LinearMap.range_eq_top.mpr hg)
  let e : L ≃ₗ[R] K × M :=
    (hexact.splitSurjectiveEquiv hf ⟨l, hl⟩).1
  exact Module.Free.of_equiv e.symm

-- The module third isomorphism theorem is Mathlib's canonical
-- `Submodule.quotientQuotientEquivQuotient`.

/-! ### Localization -/

-- A multiplicative subset is a `Submonoid`; `Localization S` and
-- `LocalizedModule S M` are the canonical ring and module localizations.
-- For a ring homomorphism `f`, `S.map f` is the image multiplicative subset.

def productSubmonoid {R : Type u} [CommMonoid R]
    (S T : Submonoid R) : Submonoid R := S ⊔ T

theorem localization_isZero_iff
    {R : Type u} [CommSemiring R] (S : Submonoid R) :
    Subsingleton (Localization S) ↔ (0 : R) ∈ S := by
  exact IsLocalization.subsingleton_iff

theorem localization_algebraMap_injective_of_nonZeroDivisors
    {R : Type u} [CommRing R] (S : Submonoid R)
    (hS : S ≤ nonZeroDivisors R) :
    Function.Injective (algebraMap R (Localization S)) := by
  exact IsLocalization.injective (Localization S) hS

theorem iterated_localization_isLocalization
    {R S T : Type*} [CommSemiring R] [CommSemiring S] [CommSemiring T]
    (M : Submonoid R) (N : Submonoid S)
    [Algebra R S] [Algebra R T] [Algebra S T]
    [IsScalarTower R S T] [IsLocalization M S] [IsLocalization N T] :
    IsLocalization (IsLocalization.localizationLocalizationSubmodule M N) T := by
  exact IsLocalization.localization_localization_isLocalization M N T

theorem localizedModule_map_injective
    {R M N : Type*} [CommSemiring R]
    [AddCommMonoid M] [AddCommMonoid N] [Module R M] [Module R N]
    (S : Submonoid R) (f : M →ₗ[R] N) (hf : Function.Injective f) :
    Function.Injective (LocalizedModule.map S f) := by
  exact LocalizedModule.map_injective S f hf

theorem localizedModule_map_surjective
    {R M N : Type*} [CommSemiring R]
    [AddCommMonoid M] [AddCommMonoid N] [Module R M] [Module R N]
    (S : Submonoid R) (f : M →ₗ[R] N) (hf : Function.Surjective f) :
    Function.Surjective (LocalizedModule.map S f) := by
  exact LocalizedModule.map_surjective S f hf

theorem localizedModule_map_exact
    {R M N P : Type*} [CommSemiring R]
    [AddCommMonoid M] [AddCommMonoid N] [AddCommMonoid P]
    [Module R M] [Module R N] [Module R P]
    (S : Submonoid R) (f : M →ₗ[R] N) (g : N →ₗ[R] P)
    (h : Function.Exact f g) :
    Function.Exact (LocalizedModule.map S f) (LocalizedModule.map S g) := by
  exact LocalizedModule.map_exact S f g h

theorem iterated_localizedModule_equiv
    {R M : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M]
    (S T : Submonoid R) :
    Nonempty
      (LocalizedModule (productSubmonoid T S) M ≃ₗ[R]
        LocalizedModule (T.map (algebraMap R (Localization S)))
          (LocalizedModule S M)) := by
  let A := Localization S
  let U := productSubmonoid T S
  let V : Submonoid A := T.map (algebraMap R A)
  let N := LocalizedModule V (LocalizedModule S M)
  let inner := LocalizedModule.mkLinearMap S M
  let outer := LocalizedModule.mkLinearMap V (LocalizedModule S M)
  let f : M →ₗ[R] N := outer.restrictScalars R ∘ₗ inner
  have hU : ∀ u : U,
      IsUnit (algebraMap R (Module.End R N) u) := by
    rintro ⟨u, hu⟩
    rcases Submonoid.mem_sup.mp hu with ⟨t, ht, s, hs, rfl⟩
    have ht' := IsLocalizedModule.map_units outer
      ⟨algebraMap R A t, Submonoid.mem_map.mpr ⟨t, ht, rfl⟩⟩
    have hs' := (IsLocalization.map_units A ⟨s, hs⟩).map
      (algebraMap A (Module.End A N))
    have ht_fun :
        (algebraMap R (Module.End R N) t : N → N) =
          (algebraMap A (Module.End A N) (algebraMap R A t) : N → N) := by
      funext x
      simp [Module.algebraMap_end_apply]
    have hs_fun :
        (algebraMap R (Module.End R N) s : N → N) =
          (algebraMap A (Module.End A N) (algebraMap R A s) : N → N) := by
      funext x
      simp [Module.algebraMap_end_apply]
    have htR : IsUnit (algebraMap R (Module.End R N) t) := by
      rw [Module.End.isUnit_iff]
      rw [ht_fun]
      exact (Module.End.isUnit_iff _).mp ht'
    have hsR : IsUnit (algebraMap R (Module.End R N) s) := by
      rw [Module.End.isUnit_iff]
      rw [hs_fun]
      exact (Module.End.isUnit_iff _).mp hs'
    rw [map_mul]
    exact htR.mul hsR
  have hsurj : ∀ y : N, ∃ x : M × U, x.2 • y = f x.1 := by
    intro y
    refine y.induction_on ?_
    intro y₀ v
    refine y₀.induction_on ?_
    intro m s
    obtain ⟨t, ht, hv⟩ := Submonoid.mem_map.mp v.property
    let v' : V := ⟨algebraMap R A t, Submonoid.mem_map.mpr ⟨t, ht, rfl⟩⟩
    have hv' : v' = v := Subtype.ext hv
    refine ⟨⟨m, ⟨t * s, Submonoid.mul_mem_sup ht s.property⟩⟩, ?_⟩
    rw [← hv']
    change (t * s : R) • LocalizedModule.mk (LocalizedModule.mk m s) v' =
      LocalizedModule.mk (LocalizedModule.mk m 1) 1
    rw [LocalizedModule.smul'_mk, mul_smul]
    have hinner : (s : R) • LocalizedModule.mk m s = LocalizedModule.mk m 1 := by
      rw [LocalizedModule.smul'_mk]
      exact LocalizedModule.mk_cancel s m
    change LocalizedModule.mk (t • ((s : R) • LocalizedModule.mk m s)) v' =
      LocalizedModule.mk (LocalizedModule.mk m 1) 1
    rw [hinner, ← IsScalarTower.algebraMap_smul A]
    change LocalizedModule.mk ((v' : A) • LocalizedModule.mk m 1) v' =
      LocalizedModule.mk (LocalizedModule.mk m 1) 1
    rw [← Submonoid.smul_def]
    exact LocalizedModule.mk_cancel v' (LocalizedModule.mk m 1)
  have heq : ∀ {x₁ x₂ : M}, f x₁ = f x₂ →
      ∃ c : V, c • inner x₁ = c • inner x₂ := by
    intro x₁ x₂ h
    change LocalizedModule.mk (LocalizedModule.mk x₁ 1) 1 =
      LocalizedModule.mk (LocalizedModule.mk x₂ 1) 1 at h
    obtain ⟨c, hc⟩ := LocalizedModule.mk_eq.mp h
    refine ⟨c, ?_⟩
    change c • LocalizedModule.mk x₁ 1 = c • LocalizedModule.mk x₂ 1
    simpa only [one_smul] using hc
  have hexists : ∀ {x₁ x₂ : M}, f x₁ = f x₂ →
      ∃ c : U, c • x₁ = c • x₂ := by
    intro x₁ x₂ h
    obtain ⟨c, hc⟩ := heq h
    obtain ⟨t, ht, htc⟩ := Submonoid.mem_map.mp c.property
    let c' : V := ⟨algebraMap R A t, Submonoid.mem_map.mpr ⟨t, ht, rfl⟩⟩
    have hcc : c' = c := Subtype.ext htc
    rw [← hcc] at hc
    change (algebraMap R A t) •
        LocalizedModule.mk (R := R) (S := S) (M := M) x₁ (1 : S) =
      (algebraMap R A t) •
        LocalizedModule.mk (R := R) (S := S) (M := M) x₂ (1 : S) at hc
    rw [IsScalarTower.algebraMap_smul A, IsScalarTower.algebraMap_smul A] at hc
    have hmk :
        LocalizedModule.mk (S := S) (t • x₁) (1 : S) =
          LocalizedModule.mk (S := S) (t • x₂) (1 : S) := by
      simpa only [LocalizedModule.smul'_mk] using hc
    obtain ⟨s, hs⟩ :=
      (LocalizedModule.mk_eq (R := R) (S := S) (M := M)).mp hmk
    have hs' : (s : R) • (t • x₁) = (s : R) • (t • x₂) := by
      simpa only [Submonoid.smul_def, one_smul] using hs
    refine ⟨⟨t * s, Submonoid.mul_mem_sup ht s.property⟩, ?_⟩
    change (t * (s : R)) • x₁ = (t * (s : R)) • x₂
    calc
      (t * (s : R)) • x₁ = (s : R) • (t • x₁) := by
        rw [mul_smul, smul_comm]
      _ = (s : R) • (t • x₂) := hs'
      _ = (t * (s : R)) • x₂ := by
        rw [smul_comm, ← mul_smul]
  have : IsLocalizedModule U f :=
    { map_units := hU
      surj := hsurj
      exists_of_eq := hexists }
  exact ⟨IsLocalizedModule.linearEquiv U (LocalizedModule.mkLinearMap U M) f⟩

theorem localized_ideal_quotient_equiv
    {R : Type u} [CommRing R] (S : Submonoid R) (I : Ideal R) :
    Nonempty
      ((Localization S ⧸ Ideal.map (algebraMap R (Localization S)) I) ≃+*
        Localization (S.map (Ideal.Quotient.mk I))) := by
  have hQ : Algebra.algebraMapSubmonoid (R ⧸ I) S =
      S.map (Ideal.Quotient.mk I) := by
    ext x
    simp [Algebra.algebraMapSubmonoid]
  rw [← hQ]
  exact ⟨(IsLocalization.algEquiv (Algebra.algebraMapSubmonoid (R ⧸ I) S)
    (Localization S ⧸ Ideal.map (algebraMap R (Localization S)) I)
    (Localization (Algebra.algebraMapSubmonoid (R ⧸ I) S))).toRingEquiv⟩

theorem ideal_in_localization_eq_map_under
    {R : Type u} [CommRing R] (S : Submonoid R) (J : Ideal (Localization S)) :
    Ideal.map (algebraMap R (Localization S)) (J.under R) = J := by
  exact IsLocalization.map_under S (Localization S) J

theorem submodule_in_localizedModule_eq_localized
    {R : Type u} {M : Type v} [CommSemiring R] [AddCommMonoid M] [Module R M]
    (S : Submonoid R)
    (N' : Submodule (Localization S) (LocalizedModule S M)) :
    N' =
      Submodule.localized' (Localization S) S (LocalizedModule.mkLinearMap S M)
        ((N'.restrictScalars R).comap (LocalizedModule.mkLinearMap S M)) := by
  exact ((Submodule.localized'gi (Localization S) S
    (LocalizedModule.mkLinearMap S M)).l_u_eq N').symm

abbrev localizationAway {R : Type u} [CommSemiring R] (f : R) : Type u :=
  Localization.Away f

abbrev localizedModuleAway {R M : Type*} [CommSemiring R]
    [AddCommMonoid M] [Module R M] (f : R) : Type _ :=
  LocalizedModule (Submonoid.powers f) M

abbrev localizationAtPrime {R : Type u} [CommSemiring R]
    (p : Ideal R) [p.IsPrime] : Type u :=
  Localization.AtPrime p

abbrev localizedModuleAtPrime {R M : Type*} [CommSemiring R]
    [AddCommMonoid M] [Module R M] (p : Ideal R) [p.IsPrime] : Type _ :=
  LocalizedModule p.primeCompl M

/-! ### Local and semilocal rings, residue fields, and tensor products -/

theorem isLocalRing_iff_unique_maximalIdeal
    {R : Type u} [CommSemiring R] :
    IsLocalRing R ↔ ∃! I : Ideal R, I.IsMaximal := by
  constructor
  · intro h
    exact @IsLocalRing.maximal_ideal_unique R _ h
  · exact IsLocalRing.of_unique_max_ideal

abbrev IsSemilocalRing (R : Type u) [CommRing R] : Prop :=
  Finite (MaximalSpectrum R)

theorem localization_atPrime_isLocalRing
    {R : Type u} [CommRing R] (p : Ideal R) [p.IsPrime] :
    IsLocalRing (Localization.AtPrime p) := by
  infer_instance

theorem localization_atPrime_maximalIdeal_eq
    {R : Type u} [CommRing R] (p : Ideal R) [p.IsPrime] :
    Ideal.map (algebraMap R (Localization.AtPrime p)) p =
      IsLocalRing.maximalIdeal (Localization.AtPrime p) := by
  exact IsLocalization.AtPrime.map_eq_maximalIdeal p (Localization.AtPrime p)

theorem residueField_isFractionRing
    {R : Type u} [CommRing R] (p : Ideal R) [p.IsPrime] :
    IsFractionRing (R ⧸ p) p.ResidueField := by
  infer_instance

theorem residueField_eq_atPrime_quotient
    {R : Type u} [CommRing R] (p : Ideal R) [p.IsPrime] :
    p.ResidueField =
      (Localization.AtPrime p ⧸
        Ideal.map (algebraMap R (Localization.AtPrime p)) p) := by
  calc
    p.ResidueField =
        (Localization.AtPrime p ⧸ IsLocalRing.maximalIdeal (Localization.AtPrime p)) := rfl
    _ = (Localization.AtPrime p ⧸
        Ideal.map (algebraMap R (Localization.AtPrime p)) p) := by
      rw [localization_atPrime_maximalIdeal_eq p]

-- The tensor product is Mathlib's `TensorProduct R M₁ M₂`, written
-- `M₁ ⊗[R] M₂`.

/-! ### Cauchy--Binet -/

noncomputable def columnMinor
    {R : Type u} [CommRing R] {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) R)
    (S : {s : Finset (Fin n) // s.card = m}) : R :=
  (A.submatrix id (fun i => (S.1.orderIsoOfFin S.2 i : Fin n))).det

noncomputable def rowMinor
    {R : Type u} [CommRing R] {m n : ℕ}
    (B : Matrix (Fin n) (Fin m) R)
    (S : {s : Finset (Fin n) // s.card = m}) : R :=
  (B.submatrix (fun i => (S.1.orderIsoOfFin S.2 i : Fin n)) id).det

theorem cauchyBinet
    {R : Type u} [CommRing R] {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) R) (B : Matrix (Fin n) (Fin m) R) :
    (A * B).det =
      ∑ S : {s : Finset (Fin n) // s.card = m},
        columnMinor A S * rowMinor B S := by
  classical
  rw [Matrix.det_apply']
  simp_rw [Matrix.mul_apply]
  simp_rw [Fintype.prod_sum]
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  let F (p : Fin m → Fin n) : R :=
    ∑ σ : Equiv.Perm (Fin m),
      (Equiv.Perm.sign σ : R) * ∏ x, A (σ x) (p x) * B (p x) x
  change (∑ p : Fin m → Fin n, F p) =
    ∑ S : {s : Finset (Fin n) // s.card = m},
      columnMinor A S * rowMinor B S
  have hnoninj {p : Fin m → Fin n} (hp : ¬ Function.Injective p) :
      (∑ σ : Equiv.Perm (Fin m),
        (Equiv.Perm.sign σ : R) *
          ∏ x, A (σ x) (p x) * B (p x) x) = 0 := by
    obtain ⟨i, j, hpij, hij⟩ := Function.not_injective_iff.mp hp
    refine Finset.sum_involution (fun σ _ => σ * Equiv.swap i j)
      (fun σ _ => by
        have hprod :
            (∏ x, A (σ x) (p x)) =
              ∏ x, A ((σ * Equiv.swap i j) x) (p x) := by
          exact Fintype.prod_equiv (Equiv.swap i j) _ _ (by
            simp [Equiv.apply_swap_eq_self hpij])
        simp [hprod, Equiv.Perm.sign_mul, Equiv.Perm.sign_swap hij,
          -Equiv.Perm.sign_swap', Finset.prod_mul_distrib])
      (fun σ _ _ => (not_congr Equiv.mul_swap_eq_iff).mpr hij)
      (fun _ _ => Finset.mem_univ _) fun σ _ =>
        Equiv.mul_swap_involutive i j σ
  rw [show
      (∑ p : Fin m → Fin n, F p) =
        (∑ p ∈ Finset.filter Function.Injective (Finset.univ : Finset (Fin m → Fin n)),
          F p) by
    refine (Finset.sum_subset (Finset.filter_subset _ _) ?_).symm
    intro p _ hp
    exact hnoninj (by
      simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using hp)]
  have hfixed (S : {s : Finset (Fin n) // s.card = m}) :
      (∑ q : Equiv.Perm (Fin m),
          F (fun i => (S.1.orderIsoOfFin S.2) (q i))) =
        columnMinor A S * rowMinor B S := by
    dsimp [F, columnMinor, rowMinor]
    rw [Matrix.det_apply', Matrix.det_apply']
    simp only [Matrix.submatrix_apply]
    rw [Finset.sum_mul]
    simp_rw [Finset.mul_sum]
    simp_rw [Finset.prod_mul_distrib]
    conv_rhs => rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro q hq
    refine Fintype.sum_equiv (Equiv.mulRight q⁻¹) _ _ ?_
    intro σ
    have hA :
        (∏ x, A (σ x) (S.1.orderEmbOfFin S.2 (q x))) =
          ∏ i, A ((σ * q⁻¹) i) (S.1.orderEmbOfFin S.2 i) := by
      exact Fintype.prod_equiv q
        (fun x => A (σ x) (S.1.orderEmbOfFin S.2 (q x)))
        (fun i => A ((σ * q⁻¹) i) (S.1.orderEmbOfFin S.2 i))
        (fun i => by
          simp only [Equiv.Perm.mul_apply, Equiv.Perm.coe_inv,
            Equiv.symm_apply_apply])
    have hsign :
        (Equiv.Perm.sign (σ * q⁻¹) : R) * (Equiv.Perm.sign q : R) =
          (Equiv.Perm.sign σ : R) := by
      calc
        (Equiv.Perm.sign (σ * q⁻¹) : R) * (Equiv.Perm.sign q : R) =
            (Equiv.Perm.sign σ : R) *
              (Equiv.Perm.sign q⁻¹ : R) * (Equiv.Perm.sign q : R) := by
                rw [Equiv.Perm.sign_mul]
                simp only [Int.cast_mul, Units.val_mul]
        _ = (Equiv.Perm.sign σ : R) *
              (Equiv.Perm.sign (q⁻¹ * q) : R) := by
                simp only [Equiv.Perm.sign_mul, Int.cast_mul, Units.val_mul,
                  mul_assoc]
        _ = (Equiv.Perm.sign σ : R) := by simp
    simp only [Equiv.coe_mulRight, id_eq]
    (rw [hA, ← hsign]; ring)
  let sp (p : Fin m → Fin n) (hp : Function.Injective p) :
      {s : Finset (Fin n) // s.card = m} :=
    ⟨Finset.univ.image p,
      (Finset.card_image_of_injective _ hp).trans (Finset.card_fin m)⟩
  let p' (p : Fin m → Fin n) (hp : Function.Injective p) :
      Fin m → (Finset.univ.image p : Finset (Fin n)) :=
    fun i => ⟨p i, Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩⟩
  have p'_bij (p : Fin m → Fin n) (hp : Function.Injective p) :
      Function.Bijective (p' p hp) := by
    constructor
    · intro i j h
      exact hp (Subtype.ext_iff.mp h)
    · intro x
      rcases Finset.mem_image.mp x.property with ⟨i, hi, hix⟩
      exact ⟨i, Subtype.ext hix⟩
  let e (p : Fin m → Fin n) (hp : Function.Injective p) :
      Fin m ≃ (sp p hp).1 :=
    (sp p hp).1.orderIsoOfFin (sp p hp).2 |>.toEquiv
  let qdef (p : Fin m → Fin n) (hp : Function.Injective p) : Equiv.Perm (Fin m) :=
    (Equiv.ofBijective (p' p hp) (p'_bij p hp)).trans (e p hp).symm
  have p_eq (p : Fin m → Fin n) (hp : Function.Injective p) (i : Fin m) :
      p i = (e p hp) (qdef p hp i) := by
    change (p' p hp i : Fin n) = _
    dsimp [qdef]
    simp
  let inv (z : Σ S : {s : Finset (Fin n) // s.card = m}, Equiv.Perm (Fin m)) :
      Fin m → Fin n :=
    fun i => (z.1.1.orderIsoOfFin z.1.2 (z.2 i) : Fin n)
  let G (z : Σ S : {s : Finset (Fin n) // s.card = m}, Equiv.Perm (Fin m)) : R :=
    F (inv z)
  have himage (S : {s : Finset (Fin n) // s.card = m})
      (q0 : Equiv.Perm (Fin m)) :
      Finset.univ.image
          (fun i => (S.1.orderIsoOfFin S.2 (q0 i) : Fin n)) = S.1 := by
    rw [show (fun i => (S.1.orderIsoOfFin S.2 (q0 i) : Fin n)) =
        (fun i => (S.1.orderIsoOfFin S.2 i : Fin n)) ∘ q0 by
          funext i
          rfl]
    rw [← Finset.image_image]
    simp
  have hsum :
      (Finset.univ : Finset
        (Σ S : {s : Finset (Fin n) // s.card = m}, Equiv.Perm (Fin m))).sum G =
        (Finset.filter Function.Injective (Finset.univ : Finset (Fin m → Fin n))).sum F := by
    refine Finset.sum_bij (fun z _ => inv z)
      (fun z _ => ?_) ?_ ?_ ?_
    · refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
      rcases z with ⟨S, q⟩
      intro i j hij
      exact q.injective ((S.1.orderIsoOfFin S.2).injective (Subtype.ext hij))
    · intro a ha b hb hab
      rcases a with ⟨S, q⟩
      rcases b with ⟨T, r⟩
      dsimp [inv] at hab
      have hST : S = T := by
        apply Subtype.ext
        have hab' :
            (fun i => (S.1.orderIsoOfFin S.2 (q i) : Fin n)) =
              (fun i => (T.1.orderIsoOfFin T.2 (r i) : Fin n)) := hab
        calc
          S.1 = Finset.univ.image
              (fun i => (S.1.orderIsoOfFin S.2 (q i) : Fin n)) :=
            (himage S q).symm
          _ = Finset.univ.image
              (fun i => (T.1.orderIsoOfFin T.2 (r i) : Fin n)) := by
            rw [hab']
          _ = T.1 := himage T r
      subst T
      have hqr : q = r := by
        apply Equiv.ext
        intro i
        apply (S.1.orderIsoOfFin S.2).injective
        exact Subtype.ext (congrFun hab i)
      subst r
      rfl
    · intro p hp_mem
      have hp := (Finset.mem_filter.mp hp_mem).2
      refine ⟨⟨sp p hp, qdef p hp⟩, Finset.mem_univ _, ?_⟩
      funext i
      dsimp [inv, e]
      exact (p_eq p hp i).symm
    · intro z hz
      rfl
  have hfinal :
      (Finset.univ : Finset
        (Σ S : {s : Finset (Fin n) // s.card = m}, Equiv.Perm (Fin m))).sum G =
        (Finset.univ : Finset {s : Finset (Fin n) // s.card = m}).sum
          (fun S => columnMinor A S * rowMinor B S) := by
    rw [Fintype.sum_sigma]
    apply Finset.sum_congr rfl
    intro S hS
    simpa [G, inv] using hfixed S
  calc
    _ = (Finset.univ : Finset
        (Σ S : {s : Finset (Fin n) // s.card = m}, Equiv.Perm (Fin m))).sum G :=
      hsum.symm
    _ = _ := hfinal

end Formalization.Books.Algebra.Unit03
