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
    (S : ShortComplex (ModuleCat.{w} R)) :
    (P →ₗ[R] (S.X₂ : Type w)) → (P →ₗ[R] (S.X₃ : Type w)) :=
  fun φ => S.g.hom.comp φ

private lemma cyclic_quotient_lift_of_pure
    {R : Type u} [CommRing R] {S : ShortComplex (ModuleCat.{max u v} R)}
    (hS : S.ShortExact) (hP : IsPureFirstMap S) (r : R)
    (φ : principalQuotient R r →ₗ[R] (S.X₃ : Type (max u v))) :
    ∃ ψ : principalQuotient R r →ₗ[R] (S.X₂ : Type (max u v)),
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
  let ψ : principalQuotient R r →ₗ[R] (S.X₂ : Type (max u v)) :=
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
      ∀ (S : ShortComplex (ModuleCat.{max u v} R)),
        S.ShortExact → IsPureFirstMap S →
          Function.Surjective (homToThirdMap (P := P) S) := by
  constructor
  · rintro ⟨ι, f, K, hK, ⟨eP⟩⟩
    classical
    obtain ⟨L, hKL⟩ := hK
    intro S hS hPure φ
    let proj : (⨁ i : ι, principalQuotient R (f i)) →ₗ[R] K :=
      K.projectionOnto L hKL
    let φK : K →ₗ[R] (S.X₃ : Type (max u v)) := φ.comp eP.symm.toLinearMap
    let φN : (⨁ i : ι, principalQuotient R (f i)) →ₗ[R] (S.X₃ : Type (max u v)) :=
      φK.comp proj
    choose ψ hψ using fun i =>
      cyclic_quotient_lift_of_pure hS hPure (f i)
        (φN.comp (DirectSum.lof R ι (fun i => principalQuotient R (f i)) i))
    let liftN : (⨁ i : ι, principalQuotient R (f i)) →ₗ[R] (S.X₂ : Type (max u v)) :=
      DirectSum.toModule R ι (S.X₂ : Type (max u v)) ψ
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
    let up : P →ₗ[R] ULift P :=
      { toFun := ULift.up
        map_add' := by intros; rfl
        map_smul' := by intros; rfl }
    let down : ULift P →ₗ[R] P :=
      { toFun := ULift.down
        map_add' := by intros; rfl
        map_smul' := by intros; rfl }
    let e' : N →ₗ[R] ULift P := up.comp e
    let A : Submodule R N := LinearMap.ker e
    let fS : (ModuleCat.of R A) ⟶ (ModuleCat.of R N) := ModuleCat.ofHom A.subtype
    let gS : (ModuleCat.of R N) ⟶ (ModuleCat.of R (ULift P)) := ModuleCat.ofHom e'
    let S : ShortComplex (ModuleCat.{max u v} R) :=
      ShortComplex.mk fS gS (by
        ext x
        simp [fS, gS, e', up, A])
    have he_surj : Function.Surjective e := by
      intro p
      let φ : principalQuotient R 0 →ₗ[R] P :=
        Submodule.liftQSpanSingleton 0
          ((LinearMap.id (R := R) (M := R)).smulRight p)
          (by simp [LinearMap.smulRight_apply])
      let i : ι := ⟨0, φ⟩
      let z : principalQuotient R 0 := Submodule.Quotient.mk 1
      refine ⟨DirectSum.lof R ι (fun i => principalQuotient R (q i)) i z, ?_⟩
      dsimp [e, i]
      rw [DirectSum.toModule_lof]
      change φ (Submodule.Quotient.mk (1 : R)) = p
      rw [Submodule.liftQSpanSingleton_apply, LinearMap.smulRight_apply]
      simp
    have hPure : IsPureFirstMap S := by
      intro r x
      constructor
      · rintro ⟨y, hy⟩
        refine ⟨(y : N), ?_⟩
        exact congrArg Subtype.val hy
      · rintro ⟨y, hy⟩
        change r • y = (x : N) at hy
        have hp : ((LinearMap.id (R := R) (M := R)).smulRight (e y)) r = 0 := by
          simpa [LinearMap.smulRight_apply] using show r • e y = 0 from by
            calc
              r • e y = e (r • y) := (e.map_smul r y).symm
              _ = e (x : N) := by rw [hy]
              _ = 0 := x.property
        let φ : principalQuotient R r →ₗ[R] P :=
          Submodule.liftQSpanSingleton r
            ((LinearMap.id (R := R) (M := R)).smulRight (e y)) hp
        let i : ι := ⟨r, φ⟩
        let z : principalQuotient R r := Submodule.Quotient.mk 1
        let zN : N :=
          DirectSum.lof R ι (fun i => principalQuotient R (q i)) i z
        have hz : r • zN = 0 := by
          dsimp [zN, z]
          rw [← map_smul]
          have : r • (Ideal.Quotient.mk (Ideal.span ({r} : Set R)) (1 : R)) =
              (0 : principalQuotient R r) := by
            change Ideal.Quotient.mk (Ideal.span ({r} : Set R)) (r * 1) = 0
            rw [Ideal.Quotient.eq_zero_iff_mem]
            exact Ideal.subset_span (by simp)
          rw [this, map_zero]
        have hez : e zN = e y := by
          dsimp [e, zN, i]
          rw [DirectSum.toModule_lof]
          change φ (Submodule.Quotient.mk (1 : R)) = e y
          rw [Submodule.liftQSpanSingleton_apply, LinearMap.smulRight_apply]
          change (1 : R) • e y = e y
          simp
        have hzA : e (y - zN) = 0 := by rw [map_sub, hez, sub_self]
        let a : A := ⟨y - zN, hzA⟩
        refine ⟨a, ?_⟩
        apply Subtype.ext
        change r • (y - zN) = (x : N)
        rw [smul_sub, hy, hz, sub_zero]
    have hS : S.ShortExact := by
      apply ShortComplex.ShortExact.mk'
      · apply (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact S).mpr
        intro x
        constructor
        · intro hx
          change e' x = 0 at hx
          have hx' : e x = 0 := by
            apply_fun ULift.down at hx
            simpa [e', up, down] using hx
          exact ⟨⟨x, hx'⟩, rfl⟩
        · rintro ⟨x, rfl⟩
          exact congrArg ULift.up x.property
      · rw [ModuleCat.mono_iff_injective]
        exact A.subtype_injective
      · rw [ModuleCat.epi_iff_surjective]
        rintro ⟨p⟩
        obtain ⟨x, hx⟩ := he_surj p
        refine ⟨x, ?_⟩
        change e' x = ULift.up p
        exact congrArg ULift.up hx
    obtain ⟨s, hs⟩ := hP S hS hPure up
    have hs' : e.comp s = LinearMap.id := by
      apply LinearMap.ext
      intro p
      have hsp := congrArg ULift.down (LinearMap.congr_fun hs p)
      change down (e' (s p)) = p at hsp
      simpa [e', up, down] using hsp
    refine ⟨ι, q, ?_⟩
    refine ⟨LinearMap.range s, ?_, ?_⟩
    · refine ⟨A, ?_⟩
      constructor
      · rw [disjoint_iff_inf_le]
        intro x hx
        rcases hx with ⟨hx1, hx2⟩
        rcases hx1 with ⟨y, hy⟩
        have hsy : e (s y) = 0 := by
          calc
            e (s y) = e x := by rw [hy]
            _ = 0 := hx2
        have hy0 : y = 0 := by
          calc
            y = e (s y) := (LinearMap.congr_fun hs' y).symm
            _ = 0 := hsy
        rw [← hy, hy0]
        simp
      · intro L hLs hLA x hx
        have hxA : x - s (e x) ∈ A := by
          change e (x - s (e x)) = 0
          have hsex : e (s (e x)) = e x := by
            simpa [LinearMap.comp_apply] using LinearMap.congr_fun hs' (e x)
          rw [map_sub, hsex, sub_self]
        have hdecomp : x = s (e x) + (x - s (e x)) := by
          calc
            x = (x - s (e x)) + s (e x) := (sub_add_cancel x _).symm
            _ = s (e x) + (x - s (e x)) := add_comm _ _
        rw [hdecomp]
        exact add_mem (hLs ⟨e x, rfl⟩) (hLA hxA)
    · let es : P ≃ₗ[R] LinearMap.range s :=
        LinearEquiv.ofBijective s.rangeRestrict ⟨
          fun x y hxy => by
            have hxy' : s x = s y := congrArg Subtype.val hxy
            apply_fun e at hxy'
            have hx' : e (s x) = x := by
              simpa [LinearMap.comp_apply] using LinearMap.congr_fun hs' x
            have hy' : e (s y) = y := by
              simpa [LinearMap.comp_apply] using LinearMap.congr_fun hs' y
            exact hx'.symm.trans (hxy'.trans hy'),
          fun x => by
            rcases x.property with ⟨p, hp⟩
            exact ⟨p, Subtype.ext hp⟩⟩
      exact ⟨es⟩

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

/- The matrix helper is placed before the first structure theorem so its
diagonal-cokernel API can be shared by the chain-ring and elementary-divisor
proofs without a duplicate private diagonal convention. -/

/-- The rectangular diagonal matrix with diagonal entries indexed by
`Fin (min n m)`. -/
def rectangularDiagonal {n m : ℕ} {R : Type u} [CommRing R]
    (f : Fin (min n m) → R) : Matrix (Fin n) (Fin m) R :=
  fun i j =>
    if _h : i.1 = j.1 then
      if h' : i.1 < min n m then f ⟨i.1, h'⟩ else 0
    else 0

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
  /-
  Proof roadmap (chain-ring decomposition).

  Interface audit: the statement has the hypotheses needed by the matrix
  argument.  In particular `PreValuationRing` does not contain nontriviality,
  so `[Nontrivial R]` must remain, while no domain hypothesis may be added:
  generalized valuation rings here are allowed to have zero divisors.  The
  different universes `R : Type u` and `M : Type v` are harmless because a
  `LinearEquiv` may relate types in different universes.

  1. Add the focused imports
     `Mathlib.LinearAlgebra.Matrix.ToLin`,
     `Mathlib.LinearAlgebra.Matrix.Permutation`,
     `Mathlib.LinearAlgebra.Matrix.Transvection`, and
     `Mathlib.LinearAlgebra.Quotient.Pi`.  First prove a private rectangular
     chain-ring Smith lemma, before this declaration, with the precise output

       ∃ U : Matrix.GeneralLinearGroup (Fin n) R,
         ∃ V : Matrix.GeneralLinearGroup (Fin m) R,
           ∃ d : Fin (min n m) → R,
             (∀ ⦃i j⦄, i.1 ≤ j.1 → d i ∣ d j) ∧
             (U : Matrix (Fin n) (Fin n) R) * A *
               (V : Matrix (Fin m) (Fin m) R) = rectangularDiagonal d.

     Install `letI : PreValuationRing R := hR` only inside that helper.  Induct
     on `min n m`.  For the successor step, use
     `PreValuationRing.cond` and a `Finset` induction on the entries of `A` to
     choose an entry `p` dividing every entry.  Move it to `(0, 0)` with
     `Equiv.Perm.swap` and `Equiv.Perm.permMatrix`; package the permutation and
     its inverse as matrix units using `Matrix.permMatrix_mul`.  If all
     entries vanish, take both units to be `1` and all diagonal entries `0`.

     Write every first-row and first-column entry as a multiple of `p`, then
     clear them with products of `Matrix.transvection`.  A transvection at
     distinct indices has inverse with the negated coefficient by
     `Matrix.transvection_mul_transvection_same`; this packages each clearing
     matrix in `Matrix.GeneralLinearGroup`.  Recurse on the `Fin.succ`/`Fin.succ`
     submatrix.  Embed the recursive units with `Matrix.fromBlocks`, reindexing
     along `finSumFinEquiv` and `finCongr`, and multiply all accumulated units.
     Since `p` divided every old entry, it divides every entry of the lower
     block after clearing; hence it divides every recursive diagonal entry.
     This supplies the displayed divisibility chain without a domain
     cancellation argument.

  2. Prove a separate, ring-independent diagonal-cokernel helper.  Extend
     `d : Fin (min n m) → R` to

       d' : Fin n → R := fun i =>
         if hi : i.1 < min n m then d ⟨i.1, hi⟩ else 0.

     Using `Matrix.toLin'_apply`, prove

       LinearMap.range (Matrix.toLin' (rectangularDiagonal d)) =
         Submodule.pi Set.univ
           (fun i => (Ideal.span ({d' i} : Set R) : Submodule R R)).

     The reverse inclusion is obtained coordinatewise: choose the coefficient
     of `d' i` for `i < min n m` and put zero in unused source coordinates.
     Transport the quotient across this equality with
     `Submodule.Quotient.equiv`, apply `Submodule.quotientPi` from
     `Mathlib/LinearAlgebra/Quotient/Pi.lean`, and finally apply
     `(DirectSum.linearEquivFunOnFintype R (Fin n)
       (fun i => principalQuotient R (d' i))).symm`.  Record the resulting
     equivalence from the cokernel of the diagonal map to
     `finiteCyclicDirectSum R n d'` as a small private definition/lemma.

  3. Obtain
     `⟨n, m, q, g, hq, hgq⟩ :=
       Module.FinitePresentation.exists_fin' R M` from
     `Mathlib/Algebra/Module/FinitePresentation.lean`.  Give the important
     intermediate term the explicit type

       A : Matrix (Fin n) (Fin m) R := LinearMap.toMatrix' g.

     Apply the chain-ring Smith helper to `A`.  The identities
     `Matrix.toLin'_toMatrix'` and `Matrix.toLin'_mul` translate the matrix
     equality into pre- and postcomposition by linear automorphisms.  Right
     multiplication does not change the range (use the linear equivalence's
     `surjective.range_comp` lemma),
     and left multiplication transports it by the automorphism; use
     `Submodule.Quotient.equiv` to identify the two cokernels.

  4. Convert `Function.Exact g q` to
     `LinearMap.range g = LinearMap.ker q` with `LinearMap.exact_iff`.
     Then `LinearMap.quotKerEquivOfSurjective q hq` identifies the cokernel of
     `g` with `M`.  Compose its inverse, the quotient equivalence induced by
     `U` and `V`, and the diagonal-cokernel equivalence from step 2.  Return
     `n`, `d'`, and this composite in `Nonempty`.
  -/
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
  /-
  Proof roadmap (Warfield local-to-global descent).

  Interface audit: the interface is sound.  A global `[Nontrivial R]` is not
  required: if a maximal ideal is present, its localization is nontrivial by
  `IsLocalization.AtPrime.nontrivial`; for the zero ring the maximal spectrum
  is empty and every module is subsingleton.  Finite presentation, rather than
  mere finite generation, is essential for localization of the two Hom
  modules below.

  1. Add the focused imports
     `Mathlib.Algebra.Category.ModuleCat.Localization` and
     `Mathlib.RingTheory.LocalProperties.Exactness`.  Prove a private lemma
     saying that `IsPureFirstMap S` is preserved by
     `S.map (ModuleCat.localizedModuleFunctor p.primeCompl)`.  A direct proof
     should represent localized scalars and vectors with
     `IsLocalization.mk'_surjective` and `IsLocalizedModule.mk'_surjective`,
     clear the common denominator using `IsLocalizedModule.exists_of_eq`, and
     invoke the original purity equivalence.  Units introduced by denominators
     are cancelled with `IsLocalizedModule.map_units`.  Keep this lemma
     separate: unfolding this denominator calculation in `warfield` makes the
     Hom-localization goal prohibitively large.

  2. Apply `characterize_pd_modules.mpr`.  For a short exact pure complex `S`,
     put, with explicit universes,

       F : (M →ₗ[R] (S.X₂ : Type (max u v))) →ₗ[R]
             (M →ₗ[R] (S.X₃ : Type (max u v))) :=
         LinearMap.llcomp R M (S.X₂ : Type (max u v))
           (S.X₃ : Type (max u v)) S.g.hom.

     It is definitionally the linear form of `homToThirdMap`.  It remains to
     prove `Function.Surjective F`.

  3. Fix `p : Ideal R` with `[p.IsMaximal]`, and write
     `Rp := Localization.AtPrime p` and
     `Sp := S.map (ModuleCat.localizedModuleFunctor p.primeCompl)`.
     Exactness is
     `hS.map_of_exact (ModuleCat.localizedModuleFunctor p.primeCompl)`; purity
     is step 1.  The instance in
     `Mathlib/Algebra/Module/FinitePresentation.lean` makes
     `LocalizedModule p.primeCompl M` finitely presented over `Rp`.
     Set `m : MaximalSpectrum R := ⟨p, inferInstance⟩`, install
     `letI : PreValuationRing Rp := hlocal m`, and apply
     `generalizedValuationRing_finitePresentation` to that localized module.

     Regard the resulting finite cyclic direct sum as a cyclic direct summand
     of itself (submodule `⊤`, complement `⊥`).  The forward implication of
     `characterize_pd_modules` over `Rp`, applied to `Sp`, gives surjectivity of
     postcomposition with `Sp.g.hom` on localized Hom modules.

  4. For `i = 2, 3`, use as localization maps

       IsLocalizedModule.map p.primeCompl
         (LocalizedModule.mkLinearMap p.primeCompl M)
         (LocalizedModule.mkLinearMap p.primeCompl (S.Xᵢ : Type (max u v))).

     `Module.FinitePresentation.isLocalizedModule_map` states exactly that
     these maps make the localized Hom spaces localizations of the original
     Hom spaces.  Prove, as a named compatibility lemma, that the localization
     of `F` is postcomposition with `Sp.g.hom`.  Use
     `IsLocalizedModule.linearMap_ext`, `IsLocalizedModule.map_apply`,
     `IsLocalizedModule.map_comp'`, and `LinearMap.llcomp_apply`; an `ext` on a
     localized generator is enough.

     Feed the local surjectivity from step 3 through this compatibility lemma,
     for every maximal `p`, and conclude `Function.Surjective F` with
     `surjective_of_isLocalized_maximal` from
     `Mathlib/RingTheory/LocalProperties/Exactness.lean`.  This closes the
     `characterize_pd_modules` criterion and yields
     `IsCyclicDirectSummand R M`.

     Do not try `LinearMap.split_surjective_of_localization_maximal`: that
     theorem requires finite presentation of `S.X₃`, which is not among the
     hypotheses.  Localizing the Hom map is what uses finite presentation of
     `M` in the correct variance.

  5. Shrink the possibly infinite direct sum in that conclusion.  Unpack it as
     `⟨ι, f, K, ⟨L, hKL⟩, ⟨e⟩⟩`.  From the inherited
     `Module.Finite R M`, choose generators
     `g : Fin q → M` with `Module.Finite.exists_fin`.  Let `t : Finset ι`
     be the union of the `DFinsupp.support`s of
     `K.subtype (e (g j))`.  Support lemmas for addition and scalar
     multiplication show that every element of `K` is supported in `t`.

     Define the inclusion of the finite direct sum indexed by `t` with
     `DirectSum.toModule`, project it to `K` with
     `K.projectionOnto L hKL`, and use the support bound to corestrict the result
     back to the finite direct sum.  The resulting endomorphism is idempotent;
     `LinearMap.IsIdempotentElem.isCompl` from
     `Mathlib/LinearAlgebra/Projection.lean` complements its range by its
     kernel.  The range is linearly equivalent to `M` via `e`.  Finally reindex
     `t` by `Finset.equivFin`, using `DirectSum.lequivCongrLeft` and
     `DirectSum.congrLinearEquiv`, and return the resulting
     `IsFiniteCyclicSummand R M`.
  -/
  sorry

/-! ## Bézout and elementary divisor domains -/

/-- A Bézout domain, using Mathlib's canonical Bézout predicate. -/
def IsBezoutDomain (R : Type u) [CommRing R] : Prop :=
  IsDomain R ∧ IsBezout R

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
  /-
  Proof roadmap (matrix/presentation equivalence).

  Interface audit: no hypothesis is missing.  In each implication install
  `letI : IsDomain R := hR.1` and `letI : IsBezout R := hR.2` locally.  The
  quantification `M : Type u` in
  `EveryFinitelyPresentedModuleIsFiniteCyclicSum` is deliberate and sufficient:
  all finite free modules and matrix cokernels used in the converse also live
  in `Type u`.

  Put the substantial argument in a private matrix/presentation lemma before
  this theorem.  It should use the focused imports
  `Mathlib.Algebra.Module.Presentation.Finite`,
  `Mathlib.LinearAlgebra.Matrix.ToLin`, and
  `Mathlib.LinearAlgebra.Quotient.Pi` and establish, over a Bézout domain, the
  equivalence between rectangular Smith reduction and decomposition of every
  finite matrix cokernel.  The two directions are as follows.

  Forward direction (Smith form gives cyclic presentations):

  1. Given `M` and `hM : Module.FinitePresentation R M`, install `letI := hM`
     and obtain
     `⟨n, m, q, g, hq, hgq⟩ :=
       Module.FinitePresentation.exists_fin' R M`.  Set
     `A : Matrix (Fin n) (Fin m) R := LinearMap.toMatrix' g`.
     If `n = 0`, surjectivity of `q` makes `M` subsingleton; return the empty
     direct sum.  If `m = 0`, exactness makes `q` bijective; return `n` copies
     of `principalQuotient R 0`.  These two branches are necessary because
     `IsElementaryDivisorDomain` only exposes matrices with positive sizes.

  2. In the positive branch apply the matrix component of the elementary
     divisor hypothesis to `A`.  Use `Matrix.toLin'_toMatrix'`,
     `Matrix.toLin'_mul`, the relevant linear equivalence's
     `surjective.range_comp` lemma, and
     `Submodule.Quotient.equiv` to transport the cokernel of `g` to the
     cokernel of `rectangularDiagonal d`.  Use the diagonal-cokernel helper
     described at `generalizedValuationRing_finitePresentation`; it pads `d`
     by zero through the unused codomain coordinates and returns a finite
     cyclic direct sum.

  3. `LinearMap.exact_iff` changes `hgq` into
     `LinearMap.range g = LinearMap.ker q`, and
     `LinearMap.quotKerEquivOfSurjective q hq` identifies this cokernel with
     `M`.  Compose the three equivalences and return them in `Nonempty`.

  Reverse direction (cyclic presentations give Smith form):

  4. For a positive `A : Matrix (Fin n) (Fin m) R`, let

       lA : (Fin m → R) →ₗ[R] (Fin n → R) := Matrix.toLin' A,
       C  : Type u := (Fin n → R) ⧸ LinearMap.range lA.

     Give `C` its finite-presentation instance with
     `Module.finitePresentation_of_surjective` applied to
     `(LinearMap.range lA).mkQ`; the kernel is the range, which is finitely
     generated by `Submodule.fg_range` because `Fin m → R` is finite.
     Apply the module hypothesis to `C`.

  5. Encode the two presentations explicitly.  The presentation of `C` has
     generators `Fin n`, relations `Fin m`, and relation map `lA`; equivalently
     use `Module.Relations` and `Module.Relations.map` from
     `Mathlib/Algebra/Module/Presentation/Basic.lean`.  For
     `⨁ i, principalQuotient R (d i)`, use generators and relations both
     indexed by `Fin k`, with relation `i` equal to
     `Finsupp.single i (d i)`.  `Submodule.quotientPi` and
     `DirectSum.linearEquivFunOnFintype` identify its relations quotient with
     the stated direct sum.

  6. Prove a private finite-presentation comparison lemma with this exact
     input: an equivalence between the quotients of two maps between finite
     free modules.  Choose lifts of each finite generator through the other
     quotient map using `Submodule.mkQ_surjective`; the two composites differ
     from the identity by maps landing in the relation submodules.  Choose
     preimages of those finitely many differences under the relation maps.
     Writing the lifts and correction homotopies with
     `LinearMap.toMatrix'` gives invertible block row and column matrices and a
     stable equivalence between the two presentation matrices.  This is the
     concrete matrix form of the usual Tietze moves: adding/removing a
     generator together with the relation setting it equal to the chosen
     lift, and changing a finite generator or relation basis.  Verify each
     block inverse with `Matrix.fromBlocks_multiply` and translate compositions by
     `LinearMap.toMatrix'_comp`.

  7. Cancel the identity generator-relation pairs introduced in step 6 one at
     a time.  Move a unit diagonal entry to the final position with permutation
     matrices, clear its row and column by `Matrix.transvection`, and delete
     that `1` block.  Thus the original `n × m` matrix, not merely a
     stabilization of it, is equivalent to a rectangular diagonal matrix.

  8. Normalize the diagonal factors into a divisibility chain.  With
     `classical`, install the noncomputable GCD structure
     `letI := IsBezout.toGCDDomain R`.  For two diagonal entries `a,b`, use
     `IsBezout.gcd_eq_sum`, `gcd_dvd_left`, `gcd_dvd_right`, and
     `gcd_mul_lcm` from
     `Mathlib/RingTheory/PrincipalIdealDomain.lean` to write explicit invertible
     `2 × 2` row and column matrices replacing
     `diag(a,b)` by `diag(gcd a b, lcm a b)` (absorb the associated unit from
     `gcd_mul_lcm` into one row).  A finite induction first makes the initial
     entry divide every later entry and then recurses on the tail.  Pad with
     unit entries for killed generator-relation pairs and with zero entries for
     the free cokernel coordinates; after the cancellations in step 7 the
     function has type `Fin (min n m) → R`.  Compose all accumulated units to
     obtain the `U`, `V`, divisibility proof, and matrix equality required by
     `IsElementaryDivisorDomain`.

  Finally the public theorem is a short wrapper around that private
  matrix/presentation lemma.  In the forward implication discard `hR` after
  installing its instances; in the reverse implication return `hR.1` as the
  domain component and the Smith result as the matrix component.
  -/
  sorry

private def matrixEntrySet {R : Type u} [CommRing R] {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) R) : Set R :=
  Set.range (fun p : Fin m × Fin n => A p.1 p.2)

private lemma matrixEntrySpan_mul_le_left {R : Type u} [CommRing R]
    {m n l : ℕ} (A : Matrix (Fin m) (Fin n) R)
    (B : Matrix (Fin n) (Fin l) R) :
    Ideal.span (matrixEntrySet (A * B)) ≤ Ideal.span (matrixEntrySet A) := by
  refine Ideal.span_le.2 ?_
  rintro z ⟨⟨i, j⟩, rfl⟩
  change (A * B) i j ∈ Ideal.span (matrixEntrySet A)
  rw [Matrix.mul_apply]
  apply Ideal.sum_mem
  intro k hk
  apply Ideal.mul_mem_right
  exact Ideal.subset_span ⟨⟨i, k⟩, rfl⟩

private lemma matrixEntrySpan_mul_le_right {R : Type u} [CommRing R]
    {m n l : ℕ} (A : Matrix (Fin m) (Fin n) R)
    (B : Matrix (Fin n) (Fin l) R) :
    Ideal.span (matrixEntrySet (A * B)) ≤ Ideal.span (matrixEntrySet B) := by
  refine Ideal.span_le.2 ?_
  rintro z ⟨⟨i, j⟩, rfl⟩
  change (A * B) i j ∈ Ideal.span (matrixEntrySet B)
  rw [Matrix.mul_apply]
  apply Ideal.sum_mem
  intro k hk
  apply Ideal.mul_mem_left
  exact Ideal.subset_span ⟨⟨k, j⟩, rfl⟩

private lemma matrixEntrySpan_mul_left_gl {R : Type u} [CommRing R]
    {m n : ℕ} (U : Matrix.GeneralLinearGroup (Fin m) R)
    (A : Matrix (Fin m) (Fin n) R) :
    Ideal.span (matrixEntrySet ((U : Matrix (Fin m) (Fin m) R) * A)) =
      Ideal.span (matrixEntrySet A) := by
  apply le_antisymm
  · exact matrixEntrySpan_mul_le_right _ _
  · have hi := matrixEntrySpan_mul_le_right
      ((U⁻¹ : Matrix.GeneralLinearGroup (Fin m) R) :
        Matrix (Fin m) (Fin m) R)
      ((U : Matrix (Fin m) (Fin m) R) * A)
    simpa [← Matrix.mul_assoc] using hi

private lemma matrixEntrySpan_mul_right_gl {R : Type u} [CommRing R]
    {m n : ℕ} (A : Matrix (Fin m) (Fin n) R)
    (V : Matrix.GeneralLinearGroup (Fin n) R) :
    Ideal.span (matrixEntrySet (A * (V : Matrix (Fin n) (Fin n) R))) =
      Ideal.span (matrixEntrySet A) := by
  apply le_antisymm
  · exact matrixEntrySpan_mul_le_left _ _
  · have hi := matrixEntrySpan_mul_le_left
      (A * (V : Matrix (Fin n) (Fin n) R))
      ((V⁻¹ : Matrix.GeneralLinearGroup (Fin n) R) :
        Matrix (Fin n) (Fin n) R)
    simpa [Matrix.mul_assoc] using hi

/-- An elementary divisor domain is a Bézout domain. -/
theorem elementaryDivisorDomain_isBezoutDomain
    {R : Type u} [CommRing R]
    (hR : IsElementaryDivisorDomain R) :
    IsBezoutDomain R := by
  rcases hR with ⟨hdom, hmat⟩
  refine ⟨hdom, ?_⟩
  rw [IsBezout.iff_span_pair_isPrincipal]
  intro a b
  let A : Matrix (Fin 1) (Fin 2) R :=
    fun i j => if j.1 = 0 then a else b
  have hA : Ideal.span (matrixEntrySet A) = Ideal.span ({a, b} : Set R) := by
    apply le_antisymm
    · refine Ideal.span_le.2 ?_
      rintro z ⟨⟨i, j⟩, rfl⟩
      have hi : i = 0 := Fin.eq_zero i
      subst i
      fin_cases j
      · exact Ideal.subset_span (by simp [A])
      · exact Ideal.subset_span (by simp [A])
    · refine Ideal.span_le.2 ?_
      rintro z hz
      rcases (Set.mem_insert_iff.mp hz) with (rfl | hz)
      · exact Ideal.subset_span ⟨⟨0, ⟨0, by decide⟩⟩, by simp [A]⟩
      · rcases Set.mem_singleton_iff.mp hz with rfl
        exact Ideal.subset_span ⟨⟨0, ⟨1, by decide⟩⟩, by simp [A]⟩
  obtain ⟨U, V, f, hf, hUV⟩ :=
    hmat (n := 1) (m := 2) (by decide) (by decide) A
  let i0 : Fin (min 1 2) := ⟨0, by decide⟩
  have hD : Ideal.span (matrixEntrySet (rectangularDiagonal f)) =
      Ideal.span ({f i0} : Set R) := by
    apply le_antisymm
    · refine Ideal.span_le.2 ?_
      rintro z ⟨⟨i, j⟩, rfl⟩
      have hi : i = 0 := Fin.eq_zero i
      subst i
      fin_cases j
      · exact Ideal.subset_span (by simp [rectangularDiagonal, i0])
      · simpa [rectangularDiagonal, i0] using
          (Ideal.zero_mem (Ideal.span ({f i0} : Set R)))
    · refine Ideal.span_le.2 ?_
      intro z hz
      rcases Set.mem_singleton_iff.mp hz with rfl
      exact Ideal.subset_span
        ⟨⟨0, ⟨0, by decide⟩⟩, by simp [rectangularDiagonal, i0]⟩
  have hspan : Ideal.span (matrixEntrySet A) =
      Ideal.span (matrixEntrySet (rectangularDiagonal f)) := by
    calc
      Ideal.span (matrixEntrySet A) =
          Ideal.span (matrixEntrySet
            ((U : Matrix (Fin 1) (Fin 1) R) * A)) :=
        (matrixEntrySpan_mul_left_gl U A).symm
      _ = Ideal.span (matrixEntrySet
          (((U : Matrix (Fin 1) (Fin 1) R) * A) *
            (V : Matrix (Fin 2) (Fin 2) R))) :=
        (matrixEntrySpan_mul_right_gl
          ((U : Matrix (Fin 1) (Fin 1) R) * A) V).symm
      _ = Ideal.span (matrixEntrySet (rectangularDiagonal f)) := by
        rw [hUV]
  have hp : Ideal.span ({a, b} : Set R) = Ideal.span ({f i0} : Set R) := by
    calc
      Ideal.span ({a, b} : Set R) = Ideal.span (matrixEntrySet A) := hA.symm
      _ = Ideal.span (matrixEntrySet (rectangularDiagonal f)) := hspan
      _ = Ideal.span ({f i0} : Set R) := hD
  exact ⟨⟨f i0, by simpa using hp⟩⟩

/-- A PID is an elementary divisor domain. -/
theorem principalIdealDomain_isElementaryDivisorDomain
    (R : Type u) [CommRing R] [IsDomain R] [IsPrincipalIdealRing R] :
    IsElementaryDivisorDomain R := by
  /-
  Proof roadmap (PID rectangular Smith normal form).

  Interface audit: `[IsDomain R] [IsPrincipalIdealRing R]` is Mathlib's
  canonical PID interface (see
  `Mathlib/RingTheory/PrincipalIdealDomain.lean`), and it supplies both
  nontriviality and the Bézout instance.  No Euclidean-domain hypothesis should
  be added.

  1. Reuse the reverse implication of
     `elementaryDivisorDomain_iff_finiteCyclicDecomposition`.  Set

       hBezout : IsBezoutDomain R :=
         ⟨inferInstance, (inferInstance : IsBezout R)⟩

     and apply
     `(elementaryDivisorDomain_iff_finiteCyclicDecomposition hBezout).2`.
     Thus it is enough to decompose an arbitrary finitely presented PID module;
     the preceding theorem then performs the presentation comparison and
     returns rectangular Smith matrices with the required divisibility chain.

  2. Add the focused imports
     `Mathlib.LinearAlgebra.FreeModule.PID` and
     `Mathlib.LinearAlgebra.Quotient.Pi`.  Given `M : Type u` and an explicit
     `hM : Module.FinitePresentation R M`, install `letI := hM` and obtain

       ⟨n, K, e, hK⟩ := Module.FinitePresentation.exists_fin R M,
       e : M ≃ₗ[R] (Fin n → R) ⧸ K.

     Let

       snf := K.smithNormalForm (Pi.basisFun R (Fin n)).

     Its second component has the explicit type
     `Module.Basis.SmithNormalForm K (Fin n) r`; its fields are `bM`, `bN`,
     `f : Fin r ↪ Fin n`, `a : Fin r → R`, and `snf`.

  3. Extend the Smith coefficients to every codomain coordinate:

       d j := if hj : j ∈ Set.range snf.f
         then snf.a (Classical.choose hj) else 0.

     The choice is independent of the witness by `snf.f.injective`.  Prove

       Submodule.map snf.bM.equivFun.toLinearMap K =
         Submodule.pi Set.univ
           (fun j => (Ideal.span ({d j} : Set R) : Submodule R R)).

     On coordinates in the range of `snf.f`, use the defining equation
     `snf.snf` and expansion in the basis `snf.bN`; off that range use
     `Module.Basis.SmithNormalForm.repr_eq_zero_of_notMem_range`, all from
     `Mathlib/LinearAlgebra/FreeModule/PID.lean`.

  4. Transport `(Fin n → R) ⧸ K` along `snf.bM.equivFun` with
     `Submodule.Quotient.equiv`, rewrite by the equality in step 3, and apply
     `Submodule.quotientPi`.  Then apply
     `(DirectSum.linearEquivFunOnFintype R (Fin n)
       (fun j => principalQuotient R (d j))).symm`.
     Composing with `e` gives
     `M ≃ₗ[R] finiteCyclicDirectSum R n d`; return `n`, `d`, and this
     equivalence in `Nonempty`.

  5. The result of step 4 proves
     `EveryFinitelyPresentedModuleIsFiniteCyclicSum R`; applying step 1 finishes
     the theorem.  Do not use `Submodule.quotientEquivDirectSum` directly: the
     version in
     `Mathlib/LinearAlgebra/FreeModule/Finite/Quotient.lean` assumes that `K`
     has full rank, while a general finitely presented module has a free
     quotient part.  Also, Mathlib's `Submodule.smithNormalForm` diagonalizes
     the inclusion but does not order its coefficients by divisibility; that
     ordering is supplied by the preceding matrix/presentation theorem, not by
     the Mathlib structure.
  -/
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
