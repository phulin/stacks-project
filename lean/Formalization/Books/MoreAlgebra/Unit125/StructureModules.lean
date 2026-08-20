/-
# More on Algebra, Chapter 125: Structure of modules over a PID
-/

import Mathlib.RingTheory.Valuation.ValuationRing
import Mathlib.Algebra.DirectSum.Module
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.Algebra.Module.FinitePresentation
import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Basic
import Mathlib.LinearAlgebra.Projection
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.PrincipalIdealDomain

/-!
This file records the definitions and theorem interfaces in the source chapter.
The standard module, localization, torsion, direct-sum, and matrix APIs are used
directly; the proofs of the structural results are left to the proving stage.
-/

namespace Formalization.Books.MoreAlgebra.Unit125

noncomputable section

open Set
open CategoryTheory
open scoped DirectSum

universe u v w

/-! ## Cyclic modules and summands -/

/-- The module denoted by `R / fR` in the source. -/
abbrev principalQuotient (R : Type u) [CommRing R] (f : R) : Type u :=
  R ⧸ Ideal.span ({f} : Set R)

/-- A finite direct sum of principal cyclic modules. -/
abbrev finiteCyclicDirectSum (R : Type u) [CommRing R] (n : ℕ)
    (f : Fin n → R) : Type u :=
  ⨁ i : Fin n, principalQuotient R (f i)

/-- A module is a linear direct summand of another module. -/
def IsLinearSummandOf (R : Type u) (T : Type v) (N : Type w) [CommRing R]
    [AddCommGroup T] [Module R T] [AddCommGroup N] [Module R N] : Prop :=
  ∃ K : Submodule R N,
    IsComplemented K ∧ Nonempty (T ≃ₗ[R] K)

/-- A module is a summand of a possibly infinite direct sum of cyclic modules. -/
def IsCyclicDirectSummand (R : Type u) (T : Type v) [CommRing R]
    [AddCommGroup T] [Module R T] : Prop :=
  ∃ (ι : Type (max u v)) (f : ι → R),
    IsLinearSummandOf R T (⨁ i : ι, principalQuotient R (f i))

/-- A module is a summand of a finite direct sum of cyclic modules. -/
def IsFiniteCyclicSummand (R : Type u) (T : Type v) [CommRing R]
    [AddCommGroup T] [Module R T] : Prop :=
  ∃ (n : ℕ) (f : Fin n → R),
    IsLinearSummandOf R T (finiteCyclicDirectSum R n f)

/-- A module is a summand of a finite direct sum of cyclic torsion modules
whose defining scalars are nonzero. -/
def IsFiniteNonzeroCyclicSummand (R : Type u) (T : Type v) [CommRing R]
    [AddCommGroup T] [Module R T] : Prop :=
  ∃ (n : ℕ) (f : Fin n → R),
    (∀ i, f i ≠ 0) ∧
      IsLinearSummandOf R T (finiteCyclicDirectSum R n f)

/-! ## The PD-module lifting criterion -/

/-- The condition `fA = A ∩ fB` for the first map of a module short complex. -/
def IsPureFirstMap {R : Type u} [CommRing R]
    (S : ShortComplex (ModuleCat.{v} R)) : Prop :=
  ∀ f : R, ∀ x : (S.X₁ : Type v),
    (∃ y : (S.X₁ : Type v), f • y = x) ↔
      ∃ y : (S.X₂ : Type v), f • y = S.f.hom x

/-- Postcomposition with the second map of a module short complex. -/
def homToThirdMap {R : Type u} {P : Type v} [CommRing R]
    [AddCommGroup P] [Module R P]
    (S : ShortComplex (ModuleCat.{v} R)) :
    (P →ₗ[R] (S.X₂ : Type v)) → (P →ₗ[R] (S.X₃ : Type v)) :=
  fun φ => S.g.hom.comp φ

private lemma cyclic_quotient_lift_of_pure
    {R : Type u} [CommRing R] {S : ShortComplex (ModuleCat.{v} R)}
    (hS : S.ShortExact) (hP : IsPureFirstMap S) (r : R)
    (φ : principalQuotient R r →ₗ[R] (S.X₃ : Type v)) :
    ∃ ψ : principalQuotient R r →ₗ[R] (S.X₂ : Type v),
      S.g.hom.comp ψ = φ := by
  let q₁ : principalQuotient R r := Ideal.Quotient.mk _ 1
  have hq₁ : r • q₁ = 0 := by
    change Ideal.Quotient.mk (Ideal.span ({r} : Set R)) (r * 1) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.subset_span (by simp)
  let x := φ q₁
  have hx : r • x = 0 := by
    rw [← φ.map_smul, hq₁, map_zero]
  obtain ⟨b, hb⟩ := hS.moduleCat_surjective_g x
  have hkernel : r • b ∈ LinearMap.ker S.g.hom := by
    rw [LinearMap.mem_ker, map_smul, hb, hx]
  have hexact : Function.Exact S.f.hom S.g.hom :=
    (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact S).mp hS.exact
  obtain ⟨a, ha⟩ := (hexact (r • b)).mp ((LinearMap.mem_ker).mp hkernel)
  obtain ⟨c, hc⟩ := (hP r a).mpr ⟨b, ha.symm⟩
  let b₀ := b - S.f.hom c
  have hb₀ : r • b₀ = 0 := by
    dsimp [b₀]
    rw [smul_sub, ← map_smul, hc, ha, sub_self]
  have hgb₀ : S.g.hom b₀ = x := by
    dsimp [b₀]
    rw [map_sub, hb, S.moduleCat_zero_apply, sub_zero]
  have hbψ : ((LinearMap.id (R := R) (M := R)).smulRight b₀) r = 0 := by
    simpa [LinearMap.smulRight_apply] using hb₀
  let ψ : principalQuotient R r →ₗ[R] (S.X₂ : Type v) :=
    Submodule.liftQSpanSingleton r
      ((LinearMap.id (R := R) (M := R)).smulRight b₀) hbψ
  refine ⟨ψ, ?_⟩
  apply LinearMap.ext
  intro z
  obtain ⟨z, rfl⟩ := (Ideal.span ({r} : Set R) : Submodule R R).mkQ_surjective z
  dsimp [ψ]
  change S.g.hom
      ((Submodule.liftQSpanSingleton r
        ((LinearMap.id (R := R) (M := R)).smulRight b₀) hbψ)
        (Submodule.Quotient.mk z)) =
      φ (Submodule.Quotient.mk z)
  rw [Submodule.liftQSpanSingleton_apply, LinearMap.smulRight_apply,
    map_smul, hgb₀, ← φ.map_smul]
  have hz : (Submodule.Quotient.mk z : principalQuotient R r) =
      z • (Submodule.Quotient.mk (1 : R)) := by
    rw [← Submodule.Quotient.mk_smul]
    simp
  rw [hz]
  simp [q₁]

/-- The source's characterization of modules which are summands of sums of cyclic modules. -/
theorem characterize_pd_modules
    {R : Type u} {P : Type v} [CommRing R] [AddCommGroup P] [Module R P] :
    IsCyclicDirectSummand R P ↔
      ∀ (S : ShortComplex (ModuleCat.{v} R)),
        S.ShortExact → IsPureFirstMap S →
          Function.Surjective (homToThirdMap (P := P) S) := by
  constructor
  · rintro ⟨ι, f, K, hK, ⟨eP⟩⟩
    classical
    obtain ⟨L, hKL⟩ := hK
    intro S hS hPure φ
    let proj : (⨁ i : ι, principalQuotient R (f i)) →ₗ[R] K :=
      K.projectionOnto L hKL
    let φK : K →ₗ[R] (S.X₃ : Type v) := φ.comp eP.symm.toLinearMap
    let φN : (⨁ i : ι, principalQuotient R (f i)) →ₗ[R] (S.X₃ : Type v) :=
      φK.comp proj
    choose ψ hψ using fun i =>
      cyclic_quotient_lift_of_pure hS hPure (f i)
        (φN.comp (DirectSum.lof R ι (fun i => principalQuotient R (f i)) i))
    let liftN : (⨁ i : ι, principalQuotient R (f i)) →ₗ[R] (S.X₂ : Type v) :=
      DirectSum.toModule R ι (S.X₂ : Type v) ψ
    have hlift : S.g.hom.comp liftN = φN := by
      apply LinearMap.ext
      intro z
      rw [DirectSum.toModule.unique (ψ := S.g.hom.comp liftN),
        DirectSum.toModule.unique (ψ := φN)]
      have hfamilies :
          (fun i => (S.g.hom.comp liftN).comp
            (DirectSum.lof R ι (fun i => principalQuotient R (f i)) i)) =
            (fun i => φN.comp
              (DirectSum.lof R ι (fun i => principalQuotient R (f i)) i)) := by
        funext i
        rw [LinearMap.comp_assoc]
        apply LinearMap.ext
        intro z
        change S.g.hom (liftN (DirectSum.lof R ι
          (fun i => principalQuotient R (f i)) i z)) =
          φN (DirectSum.lof R ι (fun i => principalQuotient R (f i)) i z)
        rw [DirectSum.toModule_lof]
        exact LinearMap.congr_fun (hψ i) z
      rw [hfamilies]
    refine ⟨liftN.comp (K.subtype.comp eP.toLinearMap), ?_⟩
    change S.g.hom.comp (liftN.comp (K.subtype.comp eP.toLinearMap)) = φ
    rw [show S.g.hom.comp (liftN.comp (K.subtype.comp eP.toLinearMap)) =
      (S.g.hom.comp liftN).comp (K.subtype.comp eP.toLinearMap) by rfl, hlift]
    dsimp [φN, φK, proj]
    apply LinearMap.ext
    intro p
    change φ (eP.symm (K.projectionOnto L hKL (K.subtype (eP p)))) = φ p
    have hproj : K.projectionOnto L hKL (K.subtype (eP p)) = eP p :=
      Submodule.projectionOnto_apply_of_mem_left hKL (eP p).property
    rw [hproj]
    simp
  · intro hP
    classical
    let ι : Type (max u v) :=
      Σ f : R, (principalQuotient R f →ₗ[R] P)
    let q : ι → R := Sigma.fst
    let N : Type (max u v) := ⨁ i : ι, principalQuotient R (q i)
    let e : N →ₗ[R] P :=
      DirectSum.toModule R ι P (fun i => i.2)
    sorry

/-! ## Generalized valuation rings -/

/- The source's generalized valuation-ring condition is Mathlib's
`PreValuationRing`, which deliberately does not require a domain. -/

/-- The divisibility characterization is equivalent to locality and the Bézout property. -/
theorem generalizedValuationRing_iff_local_bezout
    (R : Type u) [CommRing R] [Nontrivial R] :
    PreValuationRing R ↔ IsLocalRing R ∧ IsBezout R := by
  constructor
  · intro hR
    have hlocal : IsLocalRing R :=
      IsLocalRing.of_isUnit_or_isUnit_one_sub_self (fun a => by
        obtain ⟨c, h | h⟩ := @PreValuationRing.cond R _ hR a (1 - a)
        · left
          refine .of_mul_eq_one (c + 1) ?_
          simp [mul_add, h]
        · right
          refine .of_mul_eq_one (c + 1) ?_
          simp [mul_add, h])
    refine ⟨hlocal, ?_⟩
    rw [IsBezout.iff_span_pair_isPrincipal]
    intro a b
    rw [Ideal.span_insert]
    rcases (PreValuationRing.iff_ideal_total.mp hR).total
        (Ideal.span {a} : Ideal R) (Ideal.span {b}) with h | h
    · rw [sup_eq_right.mpr h]
      exact ⟨⟨b, rfl⟩⟩
    · rw [sup_eq_left.mpr h]
      exact ⟨⟨a, rfl⟩⟩
  · rintro ⟨hlocal, hbezout⟩
    refine ⟨fun a b => ?_⟩
    obtain ⟨g, hg⟩ := @IsBezout.span_pair_isPrincipal R _ hbezout a b
    have ha : a ∈ Ideal.span {g} := by
      change a ∈ R ∙ g
      rw [← hg]
      exact Ideal.subset_span (by simp)
    have hb : b ∈ Ideal.span {g} := by
      change b ∈ R ∙ g
      rw [← hg]
      exact Ideal.subset_span (by simp)
    obtain ⟨x, rfl⟩ := Ideal.mem_span_singleton'.mp ha
    obtain ⟨y, rfl⟩ := Ideal.mem_span_singleton'.mp hb
    obtain ⟨u, v, huv⟩ := Ideal.mem_span_pair.mp
      (show g ∈ Ideal.span {x * g, y * g} by
        rw [hg]
        change g ∈ Ideal.span ({g} : Set R)
        exact Ideal.subset_span (by simp))
    rcases eq_or_ne g 0 with rfl | hg0
    · exact ⟨0, by simp⟩
    have hunit : IsUnit (u * x + v * y) := by
      have hnot : ¬ IsUnit (1 - (u * x + v * y)) := by
        intro h
        have : (1 - (u * x + v * y)) * g = 0 := by
          calc
            (1 - (u * x + v * y)) * g =
                g - (u * (x * g) + v * (y * g)) := by ring
            _ = 0 := by rw [huv, sub_self]
        exact hg0 (h.mul_left_cancel (by simpa using this))
      rcases hlocal.isUnit_or_isUnit_of_add_one
          (show u * x + v * y + (1 - (u * x + v * y)) = 1 by ring) with h | h
      · exact h
      · exact False.elim (hnot h)
    rcases @IsLocalRing.isUnit_or_isUnit_of_isUnit_add R _ hlocal
        (a := u * x) (b := v * y) hunit with h | h
    · have hx : IsUnit x := isUnit_of_mul_isUnit_right h
      refine ⟨(↑(hx.unit⁻¹) : R) * y, Or.inl ?_⟩
      simp [mul_assoc, mul_comm, mul_left_comm]
    · have hy : IsUnit y := isUnit_of_mul_isUnit_right h
      refine ⟨(↑(hy.unit⁻¹) : R) * x, Or.inr ?_⟩
      simp [mul_assoc, mul_comm, mul_left_comm]

/-- The divisibility characterization is equivalent to the linear order on ideals. -/
theorem generalizedValuationRing_iff_ideal_chain
    (R : Type u) [CommRing R] [Nontrivial R] :
    PreValuationRing R ↔
      ∀ I J : Ideal R, I ≤ J ∨ J ≤ I := by
  constructor
  · intro hR I J
    exact (PreValuationRing.iff_ideal_total.mp hR).total I J
  · intro hR
    apply PreValuationRing.iff_ideal_total.mpr
    exact ⟨hR⟩

/-- A valuation ring satisfies the generalized valuation-ring condition. -/
theorem valuationRing_isGeneralizedValuationRing
    (R : Type u) [CommRing R] [IsDomain R] [ValuationRing R] :
    PreValuationRing R := by
  exact ValuationRing.toPreValuationRing

/-! ## Finitely presented modules over generalized valuation rings -/

/-- A finitely presented module over a generalized valuation ring is a finite
direct sum of principal cyclic modules. -/
theorem generalizedValuationRing_finitePresentation
    {R : Type u} {M : Type v} [CommRing R] [Nontrivial R]
    [AddCommGroup M] [Module R M]
    (hR : PreValuationRing R)
    [Module.FinitePresentation R M] :
    ∃ (n : ℕ) (f : Fin n → R),
      Nonempty (M ≃ₗ[R] finiteCyclicDirectSum R n f) := by
  sorry

/-! ## Warfield's local-to-global summand theorem -/

/-- Warfield's theorem: the local generalized valuation-ring hypothesis makes
a finitely presented module a summand of a finite cyclic direct sum. -/
theorem warfield
    {R : Type u} {M : Type v} [CommRing R]
    [AddCommGroup M] [Module R M]
    (hlocal : ∀ m : MaximalSpectrum R,
      PreValuationRing (Localization.AtPrime m.asIdeal))
    [Module.FinitePresentation R M] :
    IsFiniteCyclicSummand R M := by
  sorry

/-! ## Bézout and elementary divisor domains -/

/-- A Bézout domain, using Mathlib's canonical Bézout predicate. -/
def IsBezoutDomain (R : Type u) [CommRing R] : Prop :=
  IsDomain R ∧ IsBezout R

/-- The rectangular diagonal matrix with diagonal entries indexed by
`Fin (min n m)`. -/
def rectangularDiagonal {n m : ℕ} {R : Type u} [CommRing R]
    (f : Fin (min n m) → R) : Matrix (Fin n) (Fin m) R :=
  fun i j =>
    if _h : i.1 = j.1 then
      if h' : i.1 < min n m then f ⟨i.1, h'⟩ else 0
    else 0

/-- An elementary divisor domain, expressed by Smith normal forms of matrices. -/
def IsElementaryDivisorDomain (R : Type u) [CommRing R] : Prop :=
  IsDomain R ∧
    ∀ {n m : ℕ}, 0 < n → 0 < m →
      ∀ A : Matrix (Fin n) (Fin m) R,
        ∃ U : Matrix.GeneralLinearGroup (Fin n) R,
          ∃ V : Matrix.GeneralLinearGroup (Fin m) R,
            ∃ f : Fin (min n m) → R,
              (∀ ⦃i j : Fin (min n m)⦄, i.1 ≤ j.1 → f i ∣ f j) ∧
                (U : Matrix (Fin n) (Fin n) R) * A *
                    (V : Matrix (Fin m) (Fin m) R) = rectangularDiagonal f

/-- The module-theoretic formulation equivalent to the elementary-divisor property. -/
def EveryFinitelyPresentedModuleIsFiniteCyclicSum
    (R : Type u) [CommRing R] : Prop :=
  ∀ (M : Type u) [AddCommGroup M] [Module R M],
    Module.FinitePresentation R M →
      ∃ (n : ℕ) (f : Fin n → R),
        Nonempty (M ≃ₗ[R] finiteCyclicDirectSum R n f)

/-- The open-question formulation in the source is equivalent over a Bézout domain. -/
theorem elementaryDivisorDomain_iff_finiteCyclicDecomposition
    {R : Type u} [CommRing R] (hR : IsBezoutDomain R) :
    IsElementaryDivisorDomain R ↔
      EveryFinitelyPresentedModuleIsFiniteCyclicSum R := by
  sorry

/-- An elementary divisor domain is a Bézout domain. -/
theorem elementaryDivisorDomain_isBezoutDomain
    {R : Type u} [CommRing R]
    (hR : IsElementaryDivisorDomain R) :
    IsBezoutDomain R := by
  sorry

/-- A PID is an elementary divisor domain. -/
theorem principalIdealDomain_isElementaryDivisorDomain
    (R : Type u) [CommRing R] [IsDomain R] [IsPrincipalIdealRing R] :
    IsElementaryDivisorDomain R := by
  sorry

/-! ## Localizations and valuation rings -/

/-- Localization preserves the Bézout ideal property. -/
theorem localization_isBezout
    {R : Type u} [CommRing R] (hR : IsBezoutDomain R) (S : Submonoid R) :
    IsBezout (Localization S) := by
  sorry

/-- A localization away from zero divisors of a Bézout domain is again a
Bézout domain.  The explicit hypothesis excludes the zero localization. -/
theorem localization_isBezoutDomain
    {R : Type u} [CommRing R] (hR : IsBezoutDomain R) (S : Submonoid R)
    (hS : S ≤ nonZeroDivisors R) :
    IsBezoutDomain (Localization S) := by
  sorry

/-- Localizations at maximal ideals of a Bézout domain are valuation rings. -/
theorem localizations_of_bezoutDomain_are_valuationRings
    {R : Type u} [CommRing R] [IsDomain R]
    (hR : IsBezoutDomain R) :
    ∀ m : MaximalSpectrum R, ValuationRing (Localization.AtPrime m.asIdeal) := by
  sorry

/-- For a local domain, the Bézout and valuation-ring conditions coincide. -/
theorem localDomain_isBezout_iff_valuationRing
    (R : Type u) [CommRing R] [IsDomain R] [IsLocalRing R] :
    IsBezout R ↔ ValuationRing R := by
  sorry

/-! ## Splitting off the free and torsion parts -/

/-- A finite submodule of a free module over a Bézout domain is free. -/
theorem finite_submodule_of_free_isFree
    {R M : Type u} [CommRing R]
    [AddCommGroup M] [Module R M]
    (hR : IsBezoutDomain R) (N : Submodule R M)
    [Module.Finite R N] [Module.Free R M] :
    Module.Free R N := by
  sorry

/-- A finitely presented module over a Bézout domain splits as a finite free
module and its canonical torsion submodule, which is a finite cyclic summand. -/
theorem finitelyPresented_split_free_torsion
    {R : Type u} {M : Type v} [CommRing R]
    [AddCommGroup M] [Module R M]
    (hR : IsBezoutDomain R)
    [Module.FinitePresentation R M] :
    ∃ r : ℕ,
        Nonempty
            (M ≃ₗ[R] (Fin r →₀ R) × (Submodule.torsion R M)) ∧
        Module.IsTorsion R (Submodule.torsion R M) ∧
        IsFiniteNonzeroCyclicSummand R (Submodule.torsion R M) := by
  sorry

/-! ## The structure theorem over a PID -/

/-- Every finite module over a PID is a finite free module plus finitely many
cyclic torsion modules. -/
theorem finiteModule_over_pid_structure
    {R : Type u} {M : Type v} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
    [AddCommGroup M] [Module R M] [Module.Finite R M] :
    ∃ (r n : ℕ) (f : Fin n → R),
      (∀ i, f i ≠ 0) ∧
        Nonempty
          (M ≃ₗ[R] (Fin r →₀ R) × finiteCyclicDirectSum R n f) := by
  sorry

/-! ## Unimodular vectors -/

/-- The first index in a nonempty finite index type. -/
def firstIndex {n : ℕ} (hn : 0 < n) : Fin n :=
  ⟨0, hn⟩

/-- A unimodular row over a Bézout domain extends to an invertible matrix. -/
theorem unimodular_vector
    {R : Type u} [CommRing R] (hR : IsBezoutDomain R)
    {n : ℕ} (hn : 0 < n) (f : Fin n → R)
    (hgen : Ideal.span (Set.range f) = ⊤) :
    ∃ U : Matrix.GeneralLinearGroup (Fin n) R,
      ∀ j : Fin n,
        (U : Matrix (Fin n) (Fin n) R) (firstIndex hn) j = f j := by
  sorry

end

end Formalization.Books.MoreAlgebra.Unit125
