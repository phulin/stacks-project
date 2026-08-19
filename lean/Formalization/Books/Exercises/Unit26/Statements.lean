import Formalization.Books.Exercises.Unit26.Core
import Mathlib.Algebra.Homology.ShortComplex.ConcreteCategory
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.Algebra.Module.PID
import Mathlib.Algebra.Module.FinitePresentation
import Mathlib.Algebra.Order.Antidiag.FinsuppEquiv
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.LinearAlgebra.DirectSum.Finite
import Mathlib.LinearAlgebra.Dimension.RankNullity
import Mathlib.LinearAlgebra.Dimension.Torsion.Basic
import Mathlib.LinearAlgebra.Dimension.Torsion.Finite
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.RingTheory.Ideal.Quotient.Noetherian
import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.RingTheory.Finiteness.Prod
import Mathlib.RingTheory.MvPolynomial.Ideal
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
/- The quotient examples below use the canonical ideal-quotient ring API. -/

/-!
# Exercises, Chapter 26: Hilbert functions

The propositions below are the formal interfaces for the chapter's seven
exercises.  Their proofs are intentionally deferred to the proving stage.
-/

noncomputable section

universe u v

open CategoryTheory
open scoped nonZeroDivisors

namespace Formalization.Books.Exercises.Unit26

/-! ## Exercise 1: Euler–Poincaré functions over a field -/

/-- The value of an Euler–Poincaré function on the one-dimensional vector space. -/
def fieldEulerParameter {k : Type u} [Field k]
    (φ : EulerPoincareFunction k) : ℤ :=
  φ (FGModuleCat.of k k)

private theorem exact_ker_subtype_rangeRestrict
    {R M N : Type u} [Semiring R]
    [AddCommMonoid M] [AddCommMonoid N]
    [Module R M] [Module R N] (f : M →ₗ[R] N) :
    Function.Exact (Submodule.subtype (LinearMap.ker f)) f.rangeRestrict := by
  rw [LinearMap.exact_iff, LinearMap.ker_rangeRestrict,
    Submodule.range_subtype]

private def fgmodule_shortComplex
    (A M N P : Type u) [CommRing A] [IsNoetherianRing A]
    [AddCommGroup M] [Module A M] [Module.Finite A M]
    [AddCommGroup N] [Module A N] [Module.Finite A N]
    [AddCommGroup P] [Module A P] [Module.Finite A P]
    (f : M →ₗ[A] N) (g : N →ₗ[A] P)
    (hfg : Function.Exact f g) : ShortComplex (FGModuleCat A) :=
  ShortComplex.mk
    (FGModuleCat.ofHom f) (FGModuleCat.ofHom g) (by
      apply FGModuleCat.hom_ext
      apply LinearMap.ext
      intro z
      change g (f z) = 0
      exact congr_fun hfg.comp_eq_zero z)

private theorem fgmodule_shortExact_of_linear_maps
    (A M N P : Type u) [CommRing A] [IsNoetherianRing A]
    [AddCommGroup M] [Module A M] [Module.Finite A M]
    [AddCommGroup N] [Module A N] [Module.Finite A N]
    [AddCommGroup P] [Module A P] [Module.Finite A P]
    (f : M →ₗ[A] N) (g : N →ₗ[A] P)
    (hfg : Function.Exact f g) (hf : Function.Injective f)
    (hg : Function.Surjective g) :
    (fgmodule_shortComplex A M N P f g hfg).ShortExact := by
  let S : ShortComplex (FGModuleCat A) :=
    fgmodule_shortComplex A M N P f g hfg
  change S.ShortExact
  let F := forget₂ (FGModuleCat A) (ModuleCat A)
  apply ShortComplex.ShortExact.mk'
  · apply (ShortComplex.exact_map_iff_of_faithful S F).1
    apply (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact (S.map F)).2
    change Function.Exact f g
    exact hfg
  · apply F.mono_of_mono_map
    apply (ModuleCat.mono_iff_injective _).2
    exact hf
  · apply F.epi_of_epi_map
    apply (ModuleCat.epi_iff_surjective _).2
    exact hg

private theorem fgmodule_shortExact_data
    (A : Type u) [CommRing A] [IsNoetherianRing A]
    (S : ShortComplex (FGModuleCat A)) (hS : S.ShortExact) :
    Function.Exact S.f.hom.hom S.g.hom.hom ∧
      Function.Injective S.f.hom.hom ∧ Function.Surjective S.g.hom.hom := by
  let F := forget₂ (FGModuleCat A) (ModuleCat A)
  let S' := S.map F
  have hExact : S'.Exact :=
    (ShortComplex.exact_map_iff_of_faithful S F).2 hS.exact
  let : Mono S.f := hS.mono_f
  let : Epi S.g := hS.epi_g
  let : CategoryTheory.Limits.PreservesLimitsOfShape
      CategoryTheory.Limits.WalkingCospan F := by infer_instance
  let : CategoryTheory.Limits.PreservesColimitsOfShape
      CategoryTheory.Limits.WalkingSpan F := by infer_instance
  have hf : Function.Injective S.f.hom.hom := by
    change Function.Injective (F.map S.f).hom
    apply (ModuleCat.mono_iff_injective _).1
    exact F.map_mono S.f
  have hg : Function.Surjective S.g.hom.hom := by
    change Function.Surjective (F.map S.g).hom
    apply (ModuleCat.epi_iff_surjective _).1
    exact F.map_epi S.g
  have hfun : Function.Exact S.f.hom.hom S.g.hom.hom := by
    change Function.Exact (F.map S.f).hom (F.map S.g).hom
    exact (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact S').1 hExact
  exact ⟨hfun, hf, hg⟩

private theorem compHom_submodule_smul_compat
    {R S V : Type u} [Semiring R] [Semiring S]
    [AddCommMonoid V] [Module R V]
    (P : Submodule R V) (s : S →+* R) (q : R →+* S)
    (hcompat : ∀ (a : R) (z : P),
      s (q a) • (z : V) = a • (z : V)) :
    letI : Module S P := Module.compHom P s
    ∀ (a : R) (z : P), q a • z = a • z := by
  let : Module S P := Module.compHom P s
  intro a z
  apply Subtype.ext
  change s (q a) • (z : V) = a • (z : V)
  exact hcompat a z

private theorem finite_of_scalar_compat
    {R S Q : Type u} [Semiring R] [Semiring S]
    [AddCommGroup Q] [Module R Q] [Module.Finite R Q]
    [Module S Q] (q : R →+* S)
    (hcompat : ∀ (a : R) (z : Q), q a • z = a • z) :
    Module.Finite S Q := by
  let f : Q →ₛₗ[q] Q :=
    { toFun := id
      map_add' := by intro z w; rfl
      map_smul' := by
        intro a z
        exact (hcompat a z).symm }
  exact Module.Finite.of_surjective f (by
    intro z
    exact ⟨z, rfl⟩)

private theorem euler_value_of_fgmodule_shortExact
    (A M N P : Type u) [CommRing A] [IsNoetherianRing A]
    [AddCommGroup M] [Module A M] [Module.Finite A M]
    [AddCommGroup N] [Module A N] [Module.Finite A N]
    [AddCommGroup P] [Module A P] [Module.Finite A P]
    (θ : EulerPoincareFunction A)
    (f : M →ₗ[A] N) (g : N →ₗ[A] P)
    (hfg : Function.Exact f g)
    (hS : (fgmodule_shortComplex A M N P f g hfg).ShortExact) :
    θ (FGModuleCat.of A N) = θ (FGModuleCat.of A M) +
      θ (FGModuleCat.of A P) := by
  simpa [fgmodule_shortComplex] using
    θ.map_shortExact' (fgmodule_shortComplex A M N P f g hfg) hS

private theorem eulerPoincareFunction_ext
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    {φ ψ : EulerPoincareFunction A} (h : φ.toFun = ψ.toFun) : φ = ψ := by
  cases φ
  cases ψ
  cases h
  rfl

private def quotient_kernel_ringHom_linearEquiv
    {A B : Type u} [CommRing A] [CommRing B]
    (q : A →+* B) (s : B →+* A) (I : Ideal A)
    (hker : RingHom.ker q = I) (hqs : q.comp s = RingHom.id B) :
    letI : Module A B := Module.compHom B q
    letI : Module B (A ⧸ I) := Module.compHom (A ⧸ I) s
    (A ⧸ I) ≃ₗ[B] B := by
  letI : Module A B := Module.compHom B q
  letI : Module B (A ⧸ I) := Module.compHom (A ⧸ I) s
  let qLin : A →ₗ[A] B :=
    { toFun := q
      map_add' := by intro a b; exact q.map_add a b
      map_smul' := by
        intro a b
        change q (a * b) = q a • q b
        simp [smul_eq_mul] }
  have hI : I ≤ LinearMap.ker qLin := by
    intro a ha
    change q a = 0
    rw [← RingHom.mem_ker, hker]
    exact ha
  let l : (A ⧸ I) →ₗ[A] B := I.liftQ qLin hI
  let lB : (A ⧸ I) →ₗ[B] B :=
    { toFun := l
      map_add' := by intro z w; exact l.map_add z w
      map_smul' := by
        intro c z
        refine Submodule.Quotient.induction_on I z ?_
        intro a
        change q (s c * a) = c * q a
        rw [map_mul]
        simpa only [RingHom.comp_apply, RingHom.id_apply] using
          congrArg (fun t : B => t * q a) (RingHom.congr_fun hqs c) }
  let r : B →ₗ[B] (A ⧸ I) :=
    { toFun := fun b => Submodule.Quotient.mk (s b)
      map_add' := by
        intro b c
        change Submodule.Quotient.mk (s (b + c)) = _
        rw [map_add]
        rfl
      map_smul' := by
        intro b c
        change Submodule.Quotient.mk (s (b * c)) = _
        rw [map_mul]
        rfl }
  have hlr : lB.comp r = LinearMap.id := by
    apply LinearMap.ext
    intro b
    change q (s b) = b
    simpa only [RingHom.comp_apply, RingHom.id_apply] using
      RingHom.congr_fun hqs b
  have hrl : r.comp lB = LinearMap.id := by
    apply LinearMap.ext
    intro z
    refine Submodule.Quotient.induction_on I z ?_
    intro a
    change Submodule.Quotient.mk (s (q a)) = Submodule.Quotient.mk a
    apply (Submodule.Quotient.eq I).2
    rw [← hker, RingHom.mem_ker, map_sub]
    exact sub_eq_zero.mpr (by
      simpa only [RingHom.comp_apply, RingHom.id_apply] using
        RingHom.congr_fun hqs (q a))
  exact LinearEquiv.ofLinear lB r hlr hrl

private theorem finrank_kernel_component_quotient_eq_one
    {A B : Type u} [CommRing A] [CommRing B] [IsDomain B]
    (q : A →+* B) (s : B →+* A) (I : Ideal A) (a : A)
    (hker : RingHom.ker q = I) (hqs : q.comp s = RingHom.id B)
    (ha : a ∈ I) :
    letI : Module A B := Module.compHom B q
    letI : Module B (A ⧸ I) := Module.compHom (A ⧸ I) s
    let m : (A ⧸ I) →ₗ[A] (A ⧸ I) :=
      { toFun := fun z => a • z
        map_add' := by intro z w; simp
        map_smul' := by
          intro c z
          simp only [smul_smul, RingHom.id_apply, mul_comm] }
    let Q : Type u := (A ⧸ I) ⧸ LinearMap.range m
    letI : Module B Q := Module.compHom Q s
    Module.finrank B Q = 1 := by
  let : Module A B := Module.compHom B q
  let : Module B A := Module.compHom A s
  let : Module B (A ⧸ I) := Module.compHom (A ⧸ I) s
  let : IsScalarTower B A (A ⧸ I) := SMul.comp.isScalarTower s
  let m : (A ⧸ I) →ₗ[A] (A ⧸ I) :=
    { toFun := fun z => a • z
      map_add' := by intro z w; simp
      map_smul' := by
        intro c z
        simp only [smul_smul, RingHom.id_apply, mul_comm] }
  let Q : Type u := (A ⧸ I) ⧸ LinearMap.range m
  let : Module B Q := Module.compHom Q s
  have hm : m = 0 := by
    apply LinearMap.ext
    intro z
    refine Submodule.Quotient.induction_on I z ?_
    intro c
    change (Submodule.Quotient.mk (a * c) : A ⧸ I) = 0
    apply (Submodule.Quotient.mk_eq_zero I).2
    simpa [mul_comm] using I.mul_mem_left c ha
  let pA : Submodule A (A ⧸ I) := LinearMap.range m
  have hpA : pA = ⊥ := by
    dsimp [pA]
    rw [hm, LinearMap.range_zero]
  let pB : Submodule B (A ⧸ I) := pA.restrictScalars B
  have hpB : pB = ⊥ := by simp [pB, hpA]
  let eQ : Q ≃ₗ[B] (A ⧸ I) :=
    (Submodule.Quotient.restrictScalarsEquiv B pA).symm.trans
      (pB.quotEquivOfEqBot hpB)
  let eC : (A ⧸ I) ≃ₗ[B] B :=
    quotient_kernel_ringHom_linearEquiv q s I hker hqs
  have he : Q ≃ₗ[B] B := eQ.trans eC
  simpa [Q, pA, m] using he.finrank_eq

private theorem finrank_component_quotient_eq_zero_of_scalar_mem
    {A B : Type u} [CommRing A] [CommRing B] [IsDomain B]
    (s : B →+* A) (I : Ideal A) (a : A) (b : B⁰)
    (hscalar : s (b : B) ∈ I)
    (hfinite :
      let m : (A ⧸ I) →ₗ[A] (A ⧸ I) :=
        { toFun := fun z => a • z
          map_add' := by intro z w; simp
          map_smul' := by
            intro c z
            simp only [smul_smul, RingHom.id_apply, mul_comm] }
      let Q : Type u := (A ⧸ I) ⧸ LinearMap.range m
      letI : Module B Q := Module.compHom Q s
      Module.Finite B Q) :
    letI : Module B (A ⧸ I) := Module.compHom (A ⧸ I) s
    let m : (A ⧸ I) →ₗ[A] (A ⧸ I) :=
      { toFun := fun z => a • z
        map_add' := by intro z w; simp
        map_smul' := by
          intro c z
          simp only [smul_smul, RingHom.id_apply, mul_comm] }
    let Q : Type u := (A ⧸ I) ⧸ LinearMap.range m
    letI : Module B Q := Module.compHom Q s
    Module.finrank B Q = 0 := by
  let : Module B A := Module.compHom A s
  let : Module B (A ⧸ I) := Module.compHom (A ⧸ I) s
  let : IsScalarTower B A (A ⧸ I) := SMul.comp.isScalarTower s
  let m : (A ⧸ I) →ₗ[A] (A ⧸ I) :=
    { toFun := fun z => a • z
      map_add' := by intro z w; simp
      map_smul' := by
        intro c z
        simp only [smul_smul, RingHom.id_apply, mul_comm] }
  let Q : Type u := (A ⧸ I) ⧸ LinearMap.range m
  let : Module B Q := Module.compHom Q s
  have hzero : ∀ z : A ⧸ I, (b : B) • z = 0 := by
    intro z
    refine Submodule.Quotient.induction_on I z ?_
    intro c
    change (Submodule.Quotient.mk (s (b : B) * c) : A ⧸ I) = 0
    apply (Submodule.Quotient.mk_eq_zero I).2
    simpa [mul_comm] using I.mul_mem_left c hscalar
  have htor : Module.IsTorsion B Q := by
    intro z
    refine ⟨b, ?_⟩
    obtain ⟨w, rfl⟩ :=
      Submodule.Quotient.mk_surjective (LinearMap.range m) z
    change (b : B) • (Submodule.Quotient.mk w : Q) = 0
    rw [← Submodule.Quotient.mk_smul]
    apply (Submodule.Quotient.mk_eq_zero (LinearMap.range m)).2
    rw [hzero]
    exact (LinearMap.range m).zero_mem
  let : Module.Finite B Q := by
    simpa [Q, m] using hfinite
  exact htor.finrank_eq_zero

private theorem finrank_quotient_add_of_exact
    {A B M N P : Type u} [CommRing A] [CommRing B] [IsDomain B]
    [AddCommGroup M] [Module A M]
    [AddCommGroup N] [Module A N]
    [AddCommGroup P] [Module A P]
    (s : B →+* A)
    (pM : Submodule A M) (pN : Submodule A N) (pP : Submodule A P)
    (f : M →ₗ[A] N) (g : N →ₗ[A] P)
    (hfg : Function.Exact f g) (hf : Function.Injective f)
    (hg : Function.Surjective g)
    (hmapf : pM ≤ pN.comap f)
    (hmapg : pN ≤ pP.comap g)
    (b : B⁰)
    (hTorsionN : ∀ z : N, z ∈ pN → s (b : B) • z = 0)
    (hTorsionP : ∀ z : P, z ∈ pP → s (b : B) • z = 0)
    (hfiniteM :
      letI : Module B (M ⧸ pM) := Module.compHom (M ⧸ pM) s
      Module.Finite B (M ⧸ pM))
    (hfiniteN :
      letI : Module B (N ⧸ pN) := Module.compHom (N ⧸ pN) s
      Module.Finite B (N ⧸ pN))
    (hfiniteP :
      letI : Module B (P ⧸ pP) := Module.compHom (P ⧸ pP) s
      Module.Finite B (P ⧸ pP)) :
    letI : Module B (M ⧸ pM) := Module.compHom (M ⧸ pM) s
    letI : Module B (N ⧸ pN) := Module.compHom (N ⧸ pN) s
    letI : Module B (P ⧸ pP) := Module.compHom (P ⧸ pP) s
    Module.finrank B (N ⧸ pN) =
      Module.finrank B (M ⧸ pM) + Module.finrank B (P ⧸ pP) := by
  let : Module B A := Module.compHom A s
  let : Module B M := Module.compHom M s
  let : Module B N := Module.compHom N s
  let : Module B P := Module.compHom P s
  let : IsScalarTower B A M := SMul.comp.isScalarTower s
  let : IsScalarTower B A N := SMul.comp.isScalarTower s
  let : IsScalarTower B A P := SMul.comp.isScalarTower s
  let pM' : Submodule B M := pM.restrictScalars B
  let pN' : Submodule B N := pN.restrictScalars B
  let pP' : Submodule B P := pP.restrictScalars B
  let fB : M →ₗ[B] N :=
    { toFun := f
      map_add' := by intro z w; exact f.map_add z w
      map_smul' := by
        intro c z
        change f (s c • z) = s c • f z
        exact f.map_smul (s c) z }
  let gB : N →ₗ[B] P :=
    { toFun := g
      map_add' := by intro z w; exact g.map_add z w
      map_smul' := by
        intro c z
        change g (s c • z) = s c • g z
        exact g.map_smul (s c) z }
  have hfgB : Function.Exact fB gB := by
    simpa [fB, gB] using hfg
  have hfB : Function.Injective fB := by
    simpa [fB] using hf
  have hgB : Function.Surjective gB := by
    simpa [gB] using hg
  have hmapfB : pM' ≤ pN'.comap fB := by
    intro z hz
    exact hmapf hz
  have hmapgB : pN' ≤ pP'.comap gB := by
    intro z hz
    exact hmapg hz
  have hrange : LinearMap.range fB = LinearMap.ker gB :=
    hfgB.linearMap_ker_eq.symm
  let rN : Submodule B N := Submodule.map fB pM'
  have hrN : rN ≤ pN' := by
    apply Submodule.map_le_iff_le_comap.mpr
    exact hmapfB
  have htor : pN'.map rN.mkQ ≤ Submodule.torsion B (N ⧸ rN) := by
    intro z hz
    rw [Submodule.mem_torsion_iff]
    obtain ⟨w, hw, rfl⟩ := hz
    refine ⟨b, ?_⟩
    change (b : B) • (Submodule.Quotient.mk w : N ⧸ rN) = 0
    rw [← Submodule.Quotient.mk_smul]
    apply (Submodule.Quotient.mk_eq_zero rN).mpr
    have hw' : (w : N) ∈ pN := hw
    have hzero : (b : B) • w = 0 := by
      change s (b : B) • w = 0
      exact hTorsionN (w : N) hw'
    rw [hzero]
    exact rN.zero_mem
  let eN : ((N ⧸ rN) ⧸ pN'.map rN.mkQ) ≃ₗ[B] N ⧸ pN' :=
    Submodule.quotientQuotientEquivQuotient rN pN' hrN
  have hrankN : Module.rank B (N ⧸ pN') = Module.rank B (N ⧸ rN) := by
    calc
      Module.rank B (N ⧸ pN') =
          Module.rank B ((N ⧸ rN) ⧸ pN'.map rN.mkQ) := eN.rank_eq.symm
      _ = Module.rank B (N ⧸ rN) := rank_quotient_eq_of_le_torsion htor
  let eP : (N ⧸ LinearMap.range fB) ≃ₗ[B] P :=
    (Submodule.quotEquivOfEq (LinearMap.range fB) (LinearMap.ker gB) hrange).trans
      (gB.quotKerEquivOfSurjective hgB)
  have hrankP : Module.rank B (N ⧸ LinearMap.range fB) = Module.rank B P :=
    eP.rank_eq
  let qM : M →ₗ[B]
      (LinearMap.range fB ⧸ Submodule.map fB.rangeRestrict pM') :=
    (Submodule.map fB.rangeRestrict pM').mkQ.comp fB.rangeRestrict
  have hqM : Function.Surjective qM := by
    exact (Submodule.Quotient.mk_surjective _).comp fB.surjective_rangeRestrict
  have hkerfB : LinearMap.ker fB = ⊥ := LinearMap.ker_eq_bot.mpr hfB
  have hkerrestrict : LinearMap.ker fB.rangeRestrict ≤ pM' := by
    rw [LinearMap.ker_rangeRestrict, hkerfB]
    exact bot_le
  have hkerqM : LinearMap.ker qM = pM' := by
    dsimp [qM]
    rw [LinearMap.ker_comp, Submodule.ker_mkQ]
    exact Submodule.comap_map_eq_self hkerrestrict
  let eM : (M ⧸ pM') ≃ₗ[B]
      (LinearMap.range fB ⧸ Submodule.map fB.rangeRestrict pM') :=
    (Submodule.quotEquivOfEq pM' (LinearMap.ker qM) hkerqM.symm).trans
      (qM.quotKerEquivOfSurjective hqM)
  have hrankM :
      Module.rank B (LinearMap.range fB ⧸ Submodule.map fB.rangeRestrict pM') =
        Module.rank B (M ⧸ pM') :=
    eM.rank_eq.symm
  have hrankMap : Module.rank B (N ⧸ rN) =
      Module.rank B (N ⧸ LinearMap.range fB) +
        Module.rank B
          (LinearMap.range fB ⧸ Submodule.map fB.rangeRestrict pM') := by
    simpa [rN] using
      (LinearMap.rank_quot_submodule_map_eq (R := B) (f := fB) pM')
  have htorP : pP' ≤ Submodule.torsion B P := by
    intro z hz
    rw [Submodule.mem_torsion_iff]
    refine ⟨b, ?_⟩
    exact hTorsionP z hz
  have hrankPquot : Module.rank B (P ⧸ pP') = Module.rank B P :=
    rank_quotient_eq_of_le_torsion htorP
  have hrankM0 : Module.rank B (M ⧸ pM') = Module.rank B (M ⧸ pM) := by
    simpa [pM'] using (Submodule.Quotient.restrictScalarsEquiv B pM).rank_eq
  have hrankN0 : Module.rank B (N ⧸ pN') = Module.rank B (N ⧸ pN) := by
    simpa [pN'] using (Submodule.Quotient.restrictScalarsEquiv B pN).rank_eq
  have hrankP0 : Module.rank B (P ⧸ pP') = Module.rank B (P ⧸ pP) := by
    simpa [pP'] using (Submodule.Quotient.restrictScalarsEquiv B pP).rank_eq
  have hrank : Module.rank B (N ⧸ pN) =
      Module.rank B (M ⧸ pM) + Module.rank B (P ⧸ pP) := by
    calc
      Module.rank B (N ⧸ pN) = Module.rank B (N ⧸ pN') := hrankN0.symm
      _ = Module.rank B (N ⧸ rN) := hrankN
      _ = Module.rank B (N ⧸ LinearMap.range fB) +
          Module.rank B
            (LinearMap.range fB ⧸ Submodule.map fB.rangeRestrict pM') := hrankMap
      _ = Module.rank B P + Module.rank B (M ⧸ pM') := by
        rw [hrankP, hrankM]
      _ = Module.rank B (M ⧸ pM) + Module.rank B (P ⧸ pP) := by
        rw [← hrankM0, ← hrankP0, hrankPquot]
        ac_rfl
  let : Module B (M ⧸ pM) := Module.compHom (M ⧸ pM) s
  let : Module B (N ⧸ pN) := Module.compHom (N ⧸ pN) s
  let : Module B (P ⧸ pP) := Module.compHom (P ⧸ pP) s
  let : Module.Finite B (M ⧸ pM) := hfiniteM
  let : Module.Finite B (N ⧸ pN) := hfiniteN
  let : Module.Finite B (P ⧸ pP) := hfiniteP
  apply Nat.cast_injective (R := Cardinal)
  rw [Nat.cast_add, Module.finrank_eq_rank, Module.finrank_eq_rank,
    Module.finrank_eq_rank]
  exact hrank

private theorem finrank_multiplication_quotient_add
    {A B M N P : Type u} [CommRing A] [CommRing B] [IsDomain B]
    [AddCommGroup M] [Module A M]
    [AddCommGroup N] [Module A N]
    [AddCommGroup P] [Module A P]
    (a : A) (s : B →+* A) (b : B⁰)
    (hba : s (b : B) * a = 0)
    (f : M →ₗ[A] N) (g : N →ₗ[A] P)
    (hfg : Function.Exact f g) (hf : Function.Injective f)
    (hg : Function.Surjective g)
    (hfiniteM :
      let m : M →ₗ[A] M :=
        { toFun := fun z => a • z
          map_add' := by intro z w; simp
          map_smul' := by
            intro c z
            simp only [smul_smul, RingHom.id_apply, mul_comm] }
      let Q : Type u := M ⧸ LinearMap.range m
      letI : Module B Q := Module.compHom Q s
      Module.Finite B Q)
    (hfiniteN :
      let m : N →ₗ[A] N :=
        { toFun := fun z => a • z
          map_add' := by intro z w; simp
          map_smul' := by
            intro c z
            simp only [smul_smul, RingHom.id_apply, mul_comm] }
      let Q : Type u := N ⧸ LinearMap.range m
      letI : Module B Q := Module.compHom Q s
      Module.Finite B Q)
    (hfiniteP :
      let m : P →ₗ[A] P :=
        { toFun := fun z => a • z
          map_add' := by intro z w; simp
          map_smul' := by
            intro c z
            simp only [smul_smul, RingHom.id_apply, mul_comm] }
      let Q : Type u := P ⧸ LinearMap.range m
      letI : Module B Q := Module.compHom Q s
      Module.Finite B Q) :
    let mM : M →ₗ[A] M :=
      { toFun := fun z => a • z
        map_add' := by intro z w; simp
        map_smul' := by
          intro c z
          simp only [smul_smul, RingHom.id_apply, mul_comm] }
    let mN : N →ₗ[A] N :=
      { toFun := fun z => a • z
        map_add' := by intro z w; simp
        map_smul' := by
          intro c z
          simp only [smul_smul, RingHom.id_apply, mul_comm] }
    let mP : P →ₗ[A] P :=
      { toFun := fun z => a • z
        map_add' := by intro z w; simp
        map_smul' := by
          intro c z
          simp only [smul_smul, RingHom.id_apply, mul_comm] }
    letI : Module B (M ⧸ LinearMap.range mM) :=
      Module.compHom (M ⧸ LinearMap.range mM) s
    letI : Module B (N ⧸ LinearMap.range mN) :=
      Module.compHom (N ⧸ LinearMap.range mN) s
    letI : Module B (P ⧸ LinearMap.range mP) :=
      Module.compHom (P ⧸ LinearMap.range mP) s
    Module.finrank B (N ⧸ LinearMap.range mN) =
      Module.finrank B (M ⧸ LinearMap.range mM) +
        Module.finrank B (P ⧸ LinearMap.range mP) := by
  let mM : M →ₗ[A] M :=
    { toFun := fun z => a • z
      map_add' := by intro z w; simp
      map_smul' := by
        intro c z
        simp only [smul_smul, RingHom.id_apply, mul_comm] }
  let mN : N →ₗ[A] N :=
    { toFun := fun z => a • z
      map_add' := by intro z w; simp
      map_smul' := by
        intro c z
        simp only [smul_smul, RingHom.id_apply, mul_comm] }
  let mP : P →ₗ[A] P :=
    { toFun := fun z => a • z
      map_add' := by intro z w; simp
      map_smul' := by
        intro c z
        simp only [smul_smul, RingHom.id_apply, mul_comm] }
  let pM : Submodule A M := LinearMap.range mM
  let pN : Submodule A N := LinearMap.range mN
  let pP : Submodule A P := LinearMap.range mP
  have hmapf : pM ≤ pN.comap f := by
    intro z hz
    obtain ⟨w, rfl⟩ := hz
    refine ⟨f w, ?_⟩
    simp [mM, mN]
  have hmapg : pN ≤ pP.comap g := by
    intro z hz
    obtain ⟨w, rfl⟩ := hz
    refine ⟨g w, ?_⟩
    simp [mN, mP]
  have hTorsionN : ∀ z : N, z ∈ pN → s (b : B) • z = 0 := by
    intro z hz
    obtain ⟨w, rfl⟩ := hz
    change s (b : B) • (a • w) = 0
    rw [smul_smul, hba, zero_smul]
  have hTorsionP : ∀ z : P, z ∈ pP → s (b : B) • z = 0 := by
    intro z hz
    obtain ⟨w, rfl⟩ := hz
    change s (b : B) • (a • w) = 0
    rw [smul_smul, hba, zero_smul]
  have hfiniteM' :
      letI : Module B (M ⧸ pM) := Module.compHom (M ⧸ pM) s
      Module.Finite B (M ⧸ pM) := by
    simpa [pM, mM] using hfiniteM
  have hfiniteN' :
      letI : Module B (N ⧸ pN) := Module.compHom (N ⧸ pN) s
      Module.Finite B (N ⧸ pN) := by
    simpa [pN, mN] using hfiniteN
  have hfiniteP' :
      letI : Module B (P ⧸ pP) := Module.compHom (P ⧸ pP) s
      Module.Finite B (P ⧸ pP) := by
    simpa [pP, mP] using hfiniteP
  dsimp [mM, mN, mP]
  exact finrank_quotient_add_of_exact s pM pN pP f g hfg hf hg
    hmapf hmapg b hTorsionN hTorsionP hfiniteM' hfiniteN' hfiniteP'

private def multiplicationQuotientFinrank
    (A B M : Type u) [CommRing A] [CommRing B]
    [AddCommGroup M] [Module A M] (a : A) (s : B →+* A) : ℕ :=
  let m : M →ₗ[A] M :=
    { toFun := fun z => a • z
      map_add' := by intro z w; simp
      map_smul' := by
        intro c z
        simp only [smul_smul, RingHom.id_apply, mul_comm] }
  let Q : Type u := M ⧸ LinearMap.range m
  @Module.finrank B Q (inferInstance : Semiring B)
    (inferInstance : AddCommMonoid Q) (Module.compHom Q s)

private theorem multiplicationQuotientFinrank_add
    (A B : Type u) [CommRing A] [IsNoetherianRing A] [Module A A]
    [CommRing B] [IsDomain B]
    (a : A) (s : B →+* A) (b : B⁰) (hba : s (b : B) * a = 0)
    (S : ShortComplex (FGModuleCat A)) (hS : S.ShortExact)
    (hfinite :
      ∀ (M : Type u) [AddCommGroup M] [Module A M] [Module.Finite A M],
        let m : M →ₗ[A] M :=
          { toFun := fun z => a • z
            map_add' := by intro z w; simp
            map_smul' := by
              intro c z
              simp only [smul_smul, RingHom.id_apply, mul_comm] }
        let Q : Type u := M ⧸ LinearMap.range m
        letI : Module B Q := Module.compHom Q s
        Module.Finite B Q) :
    multiplicationQuotientFinrank A B (S.X₂ : Type u) a s =
      multiplicationQuotientFinrank A B (S.X₁ : Type u) a s +
        multiplicationQuotientFinrank A B (S.X₃ : Type u) a s := by
  let f : (S.X₁ : Type u) →ₗ[A] (S.X₂ : Type u) := S.f.hom.hom
  let g : (S.X₂ : Type u) →ₗ[A] (S.X₃ : Type u) := S.g.hom.hom
  obtain ⟨hfg₀, hf₀, hg₀⟩ := fgmodule_shortExact_data A S hS
  have hfg : Function.Exact f g := by simpa [f, g] using hfg₀
  have hf : Function.Injective f := by simpa [f] using hf₀
  have hg : Function.Surjective g := by simpa [g] using hg₀
  have hrank :=
    finrank_multiplication_quotient_add (a := a) (s := s) b hba
      f g hfg hf hg (hfinite (S.X₁ : Type u)) (hfinite (S.X₂ : Type u))
      (hfinite (S.X₃ : Type u))
  simpa [multiplicationQuotientFinrank] using hrank

private theorem node_multiplicationQuotientFinrank_add
    (A B : Type u) [CommRing A] [IsNoetherianRing A]
    [CommRing B] [IsDomain B]
    (x y : A) (sY sX : B →+* A) (b : B⁰)
    (hxy : x * y = 0) (hyx : y * x = 0)
    (hsY_X : sY (b : B) = y) (hsX_X : sX (b : B) = x)
    (qY qX : A →+* B)
    (hkerY : RingHom.ker qY = Ideal.span {x})
    (hqsY : qY.comp sY = RingHom.id B)
    (hkerX : RingHom.ker qX = Ideal.span {y})
    (hqsX : qX.comp sX = RingHom.id B)
    (hfinite :
      ∀ (M : Type u) [AddCommGroup M] [Module A M] [Module.Finite A M]
        (a : A) (s : B →+* A) (q : A →+* B),
        RingHom.ker q = Ideal.span {a} → q.comp s = RingHom.id B →
          let m : M →ₗ[A] M :=
            { toFun := fun z => a • z
              map_add' := by intro z w; simp
              map_smul' := by
                intro c z
                simp only [smul_smul, RingHom.id_apply, mul_comm] }
          let Q : Type u := M ⧸ LinearMap.range m
          letI : Module B Q := Module.compHom Q s
          Module.Finite B Q) :
    ∀ (S : ShortComplex (FGModuleCat A)) (_hS : S.ShortExact),
      multiplicationQuotientFinrank A B (S.X₂ : Type u) x sY =
          multiplicationQuotientFinrank A B (S.X₁ : Type u) x sY +
            multiplicationQuotientFinrank A B (S.X₃ : Type u) x sY ∧
      multiplicationQuotientFinrank A B (S.X₂ : Type u) y sX =
          multiplicationQuotientFinrank A B (S.X₁ : Type u) y sX +
            multiplicationQuotientFinrank A B (S.X₃ : Type u) y sX := by
  intro S hS
  have hbaY : sY (b : B) * x = 0 := by
    rw [hsY_X]
    exact hyx
  have hbaX : sX (b : B) * y = 0 := by
    rw [hsX_X]
    exact hxy
  constructor
  · exact multiplicationQuotientFinrank_add A B x sY b hbaY S hS
      (fun M _ _ _ => hfinite M x sY qY hkerY hqsY)
  · exact multiplicationQuotientFinrank_add A B y sX b hbaX S hS
      (fun M _ _ _ => hfinite M y sX qX hkerX hqsX)

private theorem eulerPoincareFunction_exists_of_multiplication_quotient
    (A B X Y : Type u) [CommRing A] [IsNoetherianRing A]
    [CommRing B] [IsDomain B]
    [AddCommGroup X] [Module A X] [Module.Finite A X]
    [AddCommGroup Y] [Module A Y] [Module.Finite A Y]
    (x y : A) (sY sX : B →+* A) (b : B⁰)
    (hxy : x * y = 0) (hyx : y * x = 0)
    (hsYb : sY (b : B) = y) (hsXb : sX (b : B) = x)
    (qY qX : A →+* B)
    (hkerY : RingHom.ker qY = Ideal.span {x})
    (hqsY : qY.comp sY = RingHom.id B)
    (hkerX : RingHom.ker qX = Ideal.span {y})
    (hqsX : qX.comp sX = RingHom.id B)
    (hfinite :
      ∀ (M : Type u) [AddCommGroup M] [Module A M] [Module.Finite A M]
        (a : A) (s : B →+* A) (q : A →+* B),
        RingHom.ker q = Ideal.span {a} → q.comp s = RingHom.id B →
          let m : M →ₗ[A] M :=
            { toFun := fun z => a • z
              map_add' := by intro z w; simp
              map_smul' := by
                intro c z
                simp only [smul_smul, RingHom.id_apply, mul_comm] }
          let Q : Type u := M ⧸ LinearMap.range m
          letI : Module B Q := Module.compHom Q s
          Module.Finite B Q)
    (hXX : multiplicationQuotientFinrank A B X x sY = 1)
    (hXY : multiplicationQuotientFinrank A B Y x sY = 0)
    (hYX : multiplicationQuotientFinrank A B X y sX = 0)
    (hYY : multiplicationQuotientFinrank A B Y y sX = 1) :
    ∀ z : ℤ × ℤ, ∃ φ : EulerPoincareFunction A,
      (φ (FGModuleCat.of A X), φ (FGModuleCat.of A Y)) = z := by
  let rX : ∀ (M : Type u) [AddCommGroup M] [Module A M], ℕ :=
    fun M _ _ => multiplicationQuotientFinrank A B M x sY
  let rY : ∀ (M : Type u) [AddCommGroup M] [Module A M], ℕ :=
    fun M _ _ => multiplicationQuotientFinrank A B M y sX
  have hadd := node_multiplicationQuotientFinrank_add A B x y sY sX b hxy hyx
    hsYb hsXb qY qX hkerY hqsY hkerX hqsX hfinite
  have hX : ∀ (S : ShortComplex (FGModuleCat A)) (hS : S.ShortExact),
      (rX (S.X₂ : Type u) : ℤ) =
        (rX (S.X₁ : Type u) : ℤ) + (rX (S.X₃ : Type u) : ℤ) := by
    intro S hS
    exact_mod_cast (hadd S hS).1
  have hY : ∀ (S : ShortComplex (FGModuleCat A)) (hS : S.ShortExact),
      (rY (S.X₂ : Type u) : ℤ) =
        (rY (S.X₁ : Type u) : ℤ) + (rY (S.X₃ : Type u) : ℤ) := by
    intro S hS
    exact_mod_cast (hadd S hS).2
  intro z
  let φX : EulerPoincareFunction A :=
    { toFun := fun M => (rX (M : Type u) : ℤ)
      map_shortExact' := by
        intro S hS
        exact hX S hS }
  let φY : EulerPoincareFunction A :=
    { toFun := fun M => (rY (M : Type u) : ℤ)
      map_shortExact' := by
        intro S hS
        exact hY S hS }
  refine ⟨
    { toFun := fun M => z.1 * φX M + z.2 * φY M
      map_shortExact' := by
        intro S hS
        rw [φX.map_shortExact' S hS, φY.map_shortExact' S hS]
        ring },
    ?_⟩
  change
    (z.1 * (rX X : ℤ) + z.2 * (rY X : ℤ),
      z.1 * (rX Y : ℤ) + z.2 * (rY Y : ℤ)) = z
  simp [rX, rY, hXX, hXY, hYX, hYY]

private theorem multiplication_component_rank_values
    (A B : Type u) [CommRing A] [IsNoetherianRing A]
    [CommRing B] [IsDomain B]
    (x y : A) (sY sX : B →+* A) (b : B⁰)
    (I J : Ideal A) (qY qX : A →+* B)
    (hkerY : RingHom.ker qY = I) (hqsY : qY.comp sY = RingHom.id B)
    (hkerX : RingHom.ker qX = J) (hqsX : qX.comp sX = RingHom.id B)
    (hIspan : I = Ideal.span {x}) (hJspan : J = Ideal.span {y})
    (hsYb : sY (b : B) = y) (hsXb : sX (b : B) = x)
    (hfinite :
      ∀ (M : Type u) [AddCommGroup M] [Module A M] [Module.Finite A M]
        (a : A) (s : B →+* A) (q : A →+* B),
        RingHom.ker q = Ideal.span {a} → q.comp s = RingHom.id B →
          let m : M →ₗ[A] M :=
            { toFun := fun z => a • z
              map_add' := by intro z w; simp
              map_smul' := by
                intro c z
                simp only [smul_smul, RingHom.id_apply, mul_comm] }
          let Q : Type u := M ⧸ LinearMap.range m
          letI : Module B Q := Module.compHom Q s
          Module.Finite B Q) :
    multiplicationQuotientFinrank A B (A ⧸ I) x sY = 1 ∧
      multiplicationQuotientFinrank A B (A ⧸ J) x sY = 0 ∧
      multiplicationQuotientFinrank A B (A ⧸ I) y sX = 0 ∧
      multiplicationQuotientFinrank A B (A ⧸ J) y sX = 1 := by
  have hxI : x ∈ I := by
    rw [hIspan]
    exact Ideal.subset_span (by rfl)
  have hyJ : y ∈ J := by
    rw [hJspan]
    exact Ideal.subset_span (by rfl)
  have hXX : multiplicationQuotientFinrank A B (A ⧸ I) x sY = 1 := by
    simpa [multiplicationQuotientFinrank] using
      (finrank_kernel_component_quotient_eq_one
        (A := A) (B := B) (q := qY) (s := sY) (I := I) (a := x)
        hkerY hqsY hxI)
  have hYY : multiplicationQuotientFinrank A B (A ⧸ J) y sX = 1 := by
    simpa [multiplicationQuotientFinrank] using
      (finrank_kernel_component_quotient_eq_one
        (A := A) (B := B) (q := qX) (s := sX) (I := J) (a := y)
        hkerX hqsX hyJ)
  have hXY : multiplicationQuotientFinrank A B (A ⧸ J) x sY = 0 := by
    have hscalar : sY (b : B) ∈ J := by
      rw [hsYb]
      exact hyJ
    simpa [multiplicationQuotientFinrank] using
      (finrank_component_quotient_eq_zero_of_scalar_mem
        (A := A) (B := B) (s := sY) (I := J) (a := x) (b := b)
        hscalar (hfinite (A ⧸ J) x sY qY (hkerY.trans hIspan) hqsY))
  have hYX : multiplicationQuotientFinrank A B (A ⧸ I) y sX = 0 := by
    have hscalar : sX (b : B) ∈ I := by
      rw [hsXb]
      exact hxI
    simpa [multiplicationQuotientFinrank] using
      (finrank_component_quotient_eq_zero_of_scalar_mem
        (A := A) (B := B) (s := sX) (I := I) (a := y) (b := b)
        hscalar (hfinite (A ⧸ I) y sX qX (hkerX.trans hJspan) hqsX))
  exact ⟨hXX, hXY, hYX, hYY⟩

private theorem eulerPoincareFunction_exists_from_multiplication_data
    (A B : Type u) [CommRing A] [IsNoetherianRing A]
    [CommRing B] [IsDomain B]
    (I J : Ideal A)
    (x y : A) (sY sX : B →+* A) (b : B⁰)
    (qY qX : A →+* B)
    (hxy : x * y = 0) (hyx : y * x = 0)
    (hkerY : RingHom.ker qY = I) (hqsY : qY.comp sY = RingHom.id B)
    (hkerX : RingHom.ker qX = J) (hqsX : qX.comp sX = RingHom.id B)
    (hIspan : I = Ideal.span {x}) (hJspan : J = Ideal.span {y})
    (hsYb : sY (b : B) = y) (hsXb : sX (b : B) = x)
    (hfinite :
      ∀ (M : Type u) [AddCommGroup M] [Module A M] [Module.Finite A M]
        (a : A) (s : B →+* A) (q : A →+* B),
        RingHom.ker q = Ideal.span {a} → q.comp s = RingHom.id B →
          let m : M →ₗ[A] M :=
            { toFun := fun z => a • z
              map_add' := by intro z w; simp
              map_smul' := by
                intro c z
                simp only [smul_smul, RingHom.id_apply, mul_comm] }
          let Q : Type u := M ⧸ LinearMap.range m
          letI : Module B Q := Module.compHom Q s
          Module.Finite B Q) :
    ∀ z : ℤ × ℤ, ∃ φ : EulerPoincareFunction A,
      (φ (FGModuleCat.of A (A ⧸ I)),
        φ (FGModuleCat.of A (A ⧸ J))) = z := by
  have hvals := multiplication_component_rank_values
    A B x y sY sX b I J qY qX hkerY hqsY hkerX hqsX hIspan hJspan
      hsYb hsXb hfinite
  exact eulerPoincareFunction_exists_of_multiplication_quotient
    A B (A ⧸ I) (A ⧸ J)
      x y sY sX b hxy hyx hsYb hsXb qY qX
      (hkerY.trans hIspan) hqsY (hkerX.trans hJspan) hqsX hfinite
      hvals.1 hvals.2.1 hvals.2.2.1 hvals.2.2.2

private theorem euler_formula_of_multiplication_sequence
    (A B X Y V : Type u) [CommRing A] [IsNoetherianRing A]
    [Semiring B]
    [AddCommGroup X] [Module A X] [Module.Finite A X]
    [AddCommGroup Y] [Module A Y] [Module.Finite A Y]
    [AddCommGroup V] [Module A V] [Module.Finite A V]
    (θ : EulerPoincareFunction A)
    (qY : A →+* B) (sY : B →+* A)
    (qX : A →+* B) (sX : B →+* A)
    (branchY :
      ∀ (θ : EulerPoincareFunction A) {Q : Type u}
        [AddCommGroup Q] [Module A Q] [Module.Finite A Q]
        [Module B Q] [Module.Finite B Q],
        (∀ (a : A) (z : Q), qY a • z = a • z) →
          θ (FGModuleCat.of A Q) =
            θ (FGModuleCat.of A X) * (Module.finrank B Q : ℤ))
    (branchX :
      ∀ (θ : EulerPoincareFunction A) {Q : Type u}
        [AddCommGroup Q] [Module A Q] [Module.Finite A Q]
        [Module B Q] [Module.Finite B Q],
        (∀ (a : A) (z : Q), qX a • z = a • z) →
          θ (FGModuleCat.of A Q) =
            θ (FGModuleCat.of A Y) * (Module.finrank B Q : ℤ))
    (m : V →ₗ[A] V)
    (hcompatK0 : ∀ (a : A) (z : LinearMap.ker m),
      sY (qY a) • (z : V) = a • (z : V))
    (hcompatI0 : ∀ (a : A) (z : LinearMap.range m),
      sX (qX a) • (z : V) = a • (z : V)) :
    letI : Module B (LinearMap.ker m) := Module.compHom (LinearMap.ker m) sY
    letI : Module B (LinearMap.range m) := Module.compHom (LinearMap.range m) sX
    θ (FGModuleCat.of A V) =
      θ (FGModuleCat.of A X) *
          (Module.finrank B (LinearMap.ker m) : ℤ) +
        θ (FGModuleCat.of A Y) *
          (Module.finrank B (LinearMap.range m) : ℤ) := by
  have hExact : Function.Exact
      (Submodule.subtype (LinearMap.ker m)) m.rangeRestrict :=
    exact_ker_subtype_rangeRestrict (R := A) (M := V) (N := V) m
  let S : ShortComplex (FGModuleCat A) :=
    fgmodule_shortComplex A (LinearMap.ker m) V (LinearMap.range m)
      (Submodule.subtype (LinearMap.ker m)) m.rangeRestrict hExact
  have hS : S.ShortExact := by
    simpa [S] using
      (fgmodule_shortExact_of_linear_maps A (LinearMap.ker m) V
        (LinearMap.range m) (Submodule.subtype (LinearMap.ker m))
        m.rangeRestrict hExact
        (by
          intro z w hzw
          exact Subtype.val_injective hzw)
        m.surjective_rangeRestrict)
  have hval : θ (FGModuleCat.of A V) =
      θ (FGModuleCat.of A (LinearMap.ker m)) +
        θ (FGModuleCat.of A (LinearMap.range m)) :=
    euler_value_of_fgmodule_shortExact A (LinearMap.ker m) V
      (LinearMap.range m) θ (Submodule.subtype (LinearMap.ker m))
      m.rangeRestrict hExact hS
  let : Module B (LinearMap.ker m) := Module.compHom (LinearMap.ker m) sY
  let : Module B (LinearMap.range m) := Module.compHom (LinearMap.range m) sX
  have hcompatK : ∀ (a : A) (z : LinearMap.ker m), qY a • z = a • z :=
    compHom_submodule_smul_compat (R := A) (S := B) (V := V)
      (P := LinearMap.ker m) sY qY hcompatK0
  let : Module.Finite B (LinearMap.ker m) :=
    finite_of_scalar_compat (R := A) (S := B)
      (Q := LinearMap.ker m) qY hcompatK
  have hcompatI : ∀ (a : A) (z : LinearMap.range m), qX a • z = a • z :=
    compHom_submodule_smul_compat (R := A) (S := B) (V := V)
      (P := LinearMap.range m) sX qX hcompatI0
  let : Module.Finite B (LinearMap.range m) :=
    finite_of_scalar_compat (R := A) (S := B)
      (Q := LinearMap.range m) qX hcompatI
  have hK := branchY θ hcompatK
  have hI := branchX θ hcompatI
  calc
    θ (FGModuleCat.of A V) =
        θ (FGModuleCat.of A (LinearMap.ker m)) +
          θ (FGModuleCat.of A (LinearMap.range m)) := hval
    _ = θ (FGModuleCat.of A X) *
          (Module.finrank B (LinearMap.ker m) : ℤ) +
        θ (FGModuleCat.of A Y) *
          (Module.finrank B (LinearMap.range m) : ℤ) := by rw [hK, hI]

private theorem fgmodule_shortExact_finrank_add (k : Type u) [Field k]
    (S : ShortComplex (FGModuleCat k)) (hS : S.ShortExact) :
    Module.finrank k (S.X₂ : Type u) =
      Module.finrank k (S.X₁ : Type u) + Module.finrank k (S.X₃ : Type u) := by
  let F := forget₂ (FGModuleCat k) (ModuleCat k)
  let S' := S.map F
  have hExact : S'.Exact :=
    (ShortComplex.exact_map_iff_of_faithful S F).2 hS.exact
  let : Mono S.f := hS.mono_f
  let : Epi S.g := hS.epi_g
  let : CategoryTheory.Limits.PreservesLimitsOfShape
      CategoryTheory.Limits.WalkingCospan F := by infer_instance
  let : CategoryTheory.Limits.PreservesColimitsOfShape
      CategoryTheory.Limits.WalkingSpan F := by infer_instance
  let f : (S.X₁ : Type u) →ₗ[k] (S.X₂ : Type u) := S.f.hom.hom
  let g : (S.X₂ : Type u) →ₗ[k] (S.X₃ : Type u) := S.g.hom.hom
  have hf : Function.Injective f := by
    change Function.Injective (F.map S.f).hom
    apply (ModuleCat.mono_iff_injective _).1
    exact F.map_mono S.f
  have hg : Function.Surjective g := by
    change Function.Surjective (F.map S.g).hom
    apply (ModuleCat.epi_iff_surjective _).1
    exact F.map_epi S.g
  have hfun : Function.Exact f g := by
    change Function.Exact (F.map S.f).hom (F.map S.g).hom
    exact (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact S').1 hExact
  have hrange : LinearMap.range f = LinearMap.ker g := hfun.linearMap_ker_eq.symm
  have hdim := g.finrank_range_add_finrank_ker
  have hrangeg : Module.finrank k (LinearMap.range g) =
      Module.finrank k (S.X₃ : Type u) := by
    rw [LinearMap.range_eq_top.mpr hg, finrank_top]
  have hker : Module.finrank k (LinearMap.ker g) =
      Module.finrank k (LinearMap.range f) := by
    rw [← hrange]
  have hrangef : Module.finrank k (LinearMap.range f) =
      Module.finrank k (S.X₁ : Type u) := LinearMap.finrank_range_of_inj hf
  change Module.finrank k (S.X₂ : Type u) =
    Module.finrank k (S.X₁ : Type u) + Module.finrank k (S.X₃ : Type u)
  calc
    Module.finrank k (S.X₂ : Type u) =
        Module.finrank k (LinearMap.range g) +
          Module.finrank k (LinearMap.ker g) := hdim.symm
    _ = Module.finrank k (S.X₃ : Type u) +
        Module.finrank k (LinearMap.range f) := by
      rw [show LinearMap.range g = ⊤ from LinearMap.range_eq_top.mpr hg,
        finrank_top, hker]
    _ = Module.finrank k (S.X₁ : Type u) +
        Module.finrank k (S.X₃ : Type u) := by rw [hrangef]; ac_rfl


/-- Explicit form of the field classification. -/
theorem eulerPoincareFunction_field_formula (k : Type u) [Field k]
    (φ : EulerPoincareFunction k) (M : FGModuleCat.{u} k) :
    φ M = fieldEulerParameter φ * (Module.finrank k (M : Type u) : ℤ) := by
  classical
  let F := forget₂ (FGModuleCat k) (ModuleCat k)
  have hzero : φ (FGModuleCat.of k (Fin 0 → k)) = 0 := by
    let Z : Type u := Fin 0 → k
    let : Subsingleton Z := by
      dsimp [Z]
      infer_instance
    let S : ShortComplex (FGModuleCat k) :=
        ShortComplex.mk
        (FGModuleCat.ofHom (LinearMap.id : Z →ₗ[k] Z))
        (FGModuleCat.ofHom (0 : Z →ₗ[k] Z)) (by
          apply FGModuleCat.hom_ext
          apply LinearMap.ext
          intro x
          change (0 : Z) = 0
          rfl)
    have hS : S.ShortExact := by
      apply ShortComplex.ShortExact.mk'
      · apply (ShortComplex.exact_map_iff_of_faithful S F).1
        apply (ShortComplex.moduleCat_exact_iff (S.map F)).2
        intro x _
        exact ⟨x, by change x = x; rfl⟩
      · apply F.mono_of_mono_map
        apply (ModuleCat.mono_iff_injective _).2
        intro x y h
        exact h
      · apply F.epi_of_epi_map
        apply (ModuleCat.epi_iff_surjective _).2
        intro y
        exact ⟨0, by change (0 : Z) = y; exact Subsingleton.elim _ _⟩
    have h := φ.map_shortExact' S hS
    have h' : φ (FGModuleCat.of k Z) =
        φ (FGModuleCat.of k Z) + φ (FGModuleCat.of k Z) := by
      simpa [S] using h
    have : φ (FGModuleCat.of k Z) = 0 := by omega
    simpa [Z] using this
  have hIso : ∀ {V W : Type u} [AddCommGroup V] [Module k V]
      [Module.Finite k V] [AddCommGroup W] [Module k W] [Module.Finite k W],
      (V ≃ₗ[k] W) →
        φ (FGModuleCat.of k V) = φ (FGModuleCat.of k W) := by
    intro V W _ _ _ _ _ _ e
    let Z : Type u := Fin 0 → k
    let : Subsingleton Z := by
      dsimp [Z]
      infer_instance
    let S : ShortComplex (FGModuleCat k) :=
        ShortComplex.mk
        (FGModuleCat.ofHom (0 : Z →ₗ[k] V))
        (FGModuleCat.ofHom e.toLinearMap) (by
          apply FGModuleCat.hom_ext
          apply LinearMap.ext
          intro x
          change e.toLinearMap (0 : V) = 0
          simp)
    have hS : S.ShortExact := by
      apply ShortComplex.ShortExact.mk'
      · apply (ShortComplex.exact_map_iff_of_faithful S F).1
        apply (ShortComplex.moduleCat_exact_iff (S.map F)).2
        intro x hx
        change e x = 0 at hx
        have hx0 : x = 0 := e.injective (hx.trans e.map_zero.symm)
        exact ⟨0, by change (0 : V) = x; rw [hx0]; rfl⟩
      · apply F.mono_of_mono_map
        apply (ModuleCat.mono_iff_injective _).2
        intro x y h
        exact @Subsingleton.elim Z this (x : Z) (y : Z)
      · apply F.epi_of_epi_map
        apply (ModuleCat.epi_iff_surjective _).2
        exact e.surjective
    have h := φ.map_shortExact' S hS
    have h' : φ (FGModuleCat.of k V) =
        φ (FGModuleCat.of k Z) + φ (FGModuleCat.of k W) := by
      simpa [S] using h
    simpa [Z, hzero, add_zero] using h'
  have hformula : ∀ (n : ℕ) (V : Type u) [AddCommGroup V] [Module k V]
      [Module.Finite k V], Module.finrank k V = n →
        φ (FGModuleCat.of k V) = fieldEulerParameter φ * (n : ℤ) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
        intro V _ _ _ hV
        by_cases hn : n = 0
        · have hsub : Subsingleton V :=
            Module.finrank_zero_iff.mp (by simpa [hn] using hV)
          let S : ShortComplex (FGModuleCat k) :=
            ShortComplex.mk
              (FGModuleCat.ofHom (LinearMap.id : V →ₗ[k] V))
              (FGModuleCat.ofHom (0 : V →ₗ[k] V)) (by
                apply FGModuleCat.hom_ext
                apply LinearMap.ext
                intro x
                change (0 : V) = 0
                rfl)
          have hS : S.ShortExact := by
            apply ShortComplex.ShortExact.mk'
            · apply (ShortComplex.exact_map_iff_of_faithful S F).1
              apply (ShortComplex.moduleCat_exact_iff (S.map F)).2
              intro x _
              exact ⟨x, by change x = x; rfl⟩
            · apply F.mono_of_mono_map
              apply (ModuleCat.mono_iff_injective _).2
              intro x y h
              exact h
            · apply F.epi_of_epi_map
              apply (ModuleCat.epi_iff_surjective _).2
              intro y
              exact ⟨0, by change (0 : V) = y; exact hsub.elim _ _⟩
          have h := φ.map_shortExact' S hS
          have h' : φ (FGModuleCat.of k V) =
              φ (FGModuleCat.of k V) + φ (FGModuleCat.of k V) := by
            simpa [S] using h
          have hz : φ (FGModuleCat.of k V) = 0 := by omega
          simp [hz, hn]
        · have hnpos : 0 < Module.finrank k V := by
            rw [hV]
            exact Nat.pos_of_ne_zero hn
          obtain ⟨x, hx⟩ := Module.finrank_pos_iff_exists_ne_zero.mp hnpos
          let L : Submodule k V := k ∙ x
          let Q : Type u := V ⧸ L
          have hL : Module.finrank k L = 1 := by
            exact finrank_span_singleton hx
          have hdim := Submodule.finrank_quotient_add_finrank L
          have hdim' : Module.finrank k Q + 1 = n := by
            simpa [Q, hL, hV] using hdim
          have hQlt : Module.finrank k Q < n := by omega
          have hQ := ih (Module.finrank k Q) hQlt Q rfl
          have hLφ : φ (FGModuleCat.of k L) = fieldEulerParameter φ := by
            simpa [L, fieldEulerParameter] using
              (hIso (LinearEquiv.toSpanNonzeroSingleton k V x hx)).symm
          let S : ShortComplex (FGModuleCat k) :=
            ShortComplex.mk
              (FGModuleCat.ofHom L.subtype)
              (FGModuleCat.ofHom L.mkQ) (by
                ext x
                change L.mkQ (L.subtype x) = 0
                simp)
          have hS : S.ShortExact := by
            apply ShortComplex.ShortExact.mk'
            · apply (ShortComplex.exact_map_iff_of_faithful S F).1
              apply (ShortComplex.moduleCat_exact_iff (S.map F)).2
              intro v hv
              change L.mkQ v = 0 at hv
              have hv' : v ∈ L := (Submodule.Quotient.mk_eq_zero L).mp hv
              exact ⟨⟨v, hv'⟩, rfl⟩
            · apply F.mono_of_mono_map
              apply (ModuleCat.mono_iff_injective _).2
              intro x y h
              exact Subtype.ext h
            · apply F.epi_of_epi_map
              apply (ModuleCat.epi_iff_surjective _).2
              intro q
              obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective L q
              exact ⟨v, rfl⟩
          have h := φ.map_shortExact' S hS
          have h' : φ (FGModuleCat.of k V) =
              φ (FGModuleCat.of k L) + φ (FGModuleCat.of k Q) := by
            simpa [S] using h
          calc
            φ (FGModuleCat.of k V) =
                φ (FGModuleCat.of k L) + φ (FGModuleCat.of k Q) := h'
            _ = fieldEulerParameter φ +
                fieldEulerParameter φ * (Module.finrank k Q : ℤ) := by
              rw [hLφ, hQ]
            _ = fieldEulerParameter φ * (n : ℤ) := by
              rw [← hdim', Nat.cast_add]
              ring
  simpa [fieldEulerParameter] using
    hformula (Module.finrank k (M : Type u)) (M : Type u) rfl

/-- Over a field, an Euler–Poincaré function is determined by its value on `k`.
The bijectivity statement packages both the classification and the existence of
all integer-valued choices. -/
theorem eulerPoincareFunction_field_classification (k : Type u) [Field k] :
    Function.Bijective (fieldEulerParameter (k := k)) := by
  classical
  constructor
  · intro φ ψ h
    cases φ with
    | mk φ hφ =>
      cases ψ with
      | mk ψ hψ =>
        have hparam : φ (FGModuleCat.of k k) = ψ (FGModuleCat.of k k) := by
          simpa [fieldEulerParameter] using h
        have hfun : φ = ψ := by
          funext M
          have hφM := eulerPoincareFunction_field_formula k
            (⟨φ, hφ⟩ : EulerPoincareFunction k) M
          have hψM := eulerPoincareFunction_field_formula k
            (⟨ψ, hψ⟩ : EulerPoincareFunction k) M
          calc
            φ M = φ (FGModuleCat.of k k) *
                (Module.finrank k (M : Type u) : ℤ) := by
              simpa [fieldEulerParameter] using hφM
            _ = ψ (FGModuleCat.of k k) *
                (Module.finrank k (M : Type u) : ℤ) := by rw [hparam]
            _ = ψ M := by
              simpa [fieldEulerParameter] using hψM.symm
        cases hfun
        rfl
  · intro z
    let φz : EulerPoincareFunction k :=
      { toFun := fun M => z * (Module.finrank k (M : Type u) : ℤ)
        map_shortExact' := by
          intro S hS
          have hdim := fgmodule_shortExact_finrank_add k S hS
          change z * (Module.finrank k (S.X₂ : Type u) : ℤ) =
            z * (Module.finrank k (S.X₁ : Type u) : ℤ) +
              z * (Module.finrank k (S.X₃ : Type u) : ℤ)
          rw [hdim, Nat.cast_add, mul_add] }
    refine ⟨φz, ?_⟩
    simp [φz, fieldEulerParameter]


/-! ## Exercise 2: Euler–Poincaré functions over the integers -/

/-- The value of an Euler–Poincaré function on the rank-one free `ℤ`-module. -/
def integerEulerParameter (φ : EulerPoincareFunction ℤ) : ℤ :=
  φ (FGModuleCat.of ℤ ℤ)

/-- Additivity forces every finite torsion module to have value zero, so an
Euler–Poincaré function on finitely generated abelian groups is determined by
its single value on `ℤ`. -/
theorem eulerPoincareFunction_integer_classification :
    Function.Bijective integerEulerParameter := by
  classical
  let F := forget₂ (FGModuleCat ℤ) (ModuleCat ℤ)
  have hzero : ∀ (φ : EulerPoincareFunction ℤ),
      φ (FGModuleCat.of ℤ (Fin 0 → ℤ)) = 0 := by
    intro φ
    let Z : Type := Fin 0 → ℤ
    let : Subsingleton Z := by
      dsimp [Z]
      infer_instance
    let S : ShortComplex (FGModuleCat ℤ) :=
      ShortComplex.mk
        (FGModuleCat.ofHom (LinearMap.id : Z →ₗ[ℤ] Z))
        (FGModuleCat.ofHom (0 : Z →ₗ[ℤ] Z)) (by
          apply FGModuleCat.hom_ext
          apply LinearMap.ext
          intro x
          change (0 : Z) = 0
          rfl)
    have hS : S.ShortExact := by
      apply ShortComplex.ShortExact.mk'
      · apply (ShortComplex.exact_map_iff_of_faithful S F).1
        apply (ShortComplex.moduleCat_exact_iff (S.map F)).2
        intro x _
        exact ⟨x, by change x = x; rfl⟩
      · apply F.mono_of_mono_map
        apply (ModuleCat.mono_iff_injective _).2
        intro x y h
        exact h
      · apply F.epi_of_epi_map
        apply (ModuleCat.epi_iff_surjective _).2
        intro y
        exact ⟨0, by change (0 : Z) = y; exact Subsingleton.elim _ _⟩
    have h := φ.map_shortExact' S hS
    have h' : φ (FGModuleCat.of ℤ Z) =
        φ (FGModuleCat.of ℤ Z) + φ (FGModuleCat.of ℤ Z) := by
      simpa [S] using h
    have hz : φ (FGModuleCat.of ℤ Z) = 0 := by omega
    simpa [Z] using hz
  have hIso : ∀ (φ : EulerPoincareFunction ℤ)
      {V W : Type} [AddCommGroup V] [Module ℤ V]
      [Module.Finite ℤ V] [AddCommGroup W] [Module ℤ W]
      [Module.Finite ℤ W],
      (V ≃ₗ[ℤ] W) →
        φ (FGModuleCat.of ℤ V) = φ (FGModuleCat.of ℤ W) := by
    intro φ V W _ _ _ _ _ _ e
    let Z : Type := Fin 0 → ℤ
    let : Subsingleton Z := by
      dsimp [Z]
      infer_instance
    let S : ShortComplex (FGModuleCat ℤ) :=
      ShortComplex.mk
        (FGModuleCat.ofHom (0 : Z →ₗ[ℤ] V))
        (FGModuleCat.ofHom e.toLinearMap) (by
          apply FGModuleCat.hom_ext
          apply LinearMap.ext
          intro x
          change e.toLinearMap (0 : V) = 0
          simp)
    have hS : S.ShortExact := by
      apply ShortComplex.ShortExact.mk'
      · apply (ShortComplex.exact_map_iff_of_faithful S F).1
        apply (ShortComplex.moduleCat_exact_iff (S.map F)).2
        intro x hx
        change e x = 0 at hx
        have hx0 : x = 0 := e.injective (hx.trans e.map_zero.symm)
        exact ⟨0, by change (0 : V) = x; rw [hx0]; rfl⟩
      · apply F.mono_of_mono_map
        apply (ModuleCat.mono_iff_injective _).2
        intro x y h
        exact @Subsingleton.elim Z _ (x : Z) (y : Z)
      · apply F.epi_of_epi_map
        apply (ModuleCat.epi_iff_surjective _).2
        exact e.surjective
    have h := φ.map_shortExact' S hS
    have h' : φ (FGModuleCat.of ℤ V) =
        φ (FGModuleCat.of ℤ Z) + φ (FGModuleCat.of ℤ W) := by
      simpa [S] using h
    simpa [Z, hzero φ, add_zero] using h'
  have hprod : ∀ (φ : EulerPoincareFunction ℤ)
      {V W : Type} [AddCommGroup V] [Module ℤ V]
      [Module.Finite ℤ V] [AddCommGroup W] [Module ℤ W]
      [Module.Finite ℤ W],
      let P : Type := V × W
      letI : Module ℤ P := Prod.instModule
      φ (FGModuleCat.of ℤ P) =
        φ (FGModuleCat.of ℤ V) + φ (FGModuleCat.of ℤ W) := by
    intro φ V W _ _ _ _ _ _
    let P : Type := V × W
    let : Module ℤ P := Prod.instModule
    let : Module.Finite ℤ P := by infer_instance
    let S : ShortComplex (FGModuleCat ℤ) :=
      ShortComplex.mk
        (FGModuleCat.ofHom (LinearMap.inl ℤ V W))
        (FGModuleCat.ofHom (LinearMap.snd ℤ V W)) (by
          apply FGModuleCat.hom_ext
          apply LinearMap.ext
          intro x
          rfl)
    have hS : S.ShortExact := by
      apply ShortComplex.ShortExact.mk'
      · apply (ShortComplex.exact_map_iff_of_faithful S F).1
        apply (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact (S.map F)).2
        change Function.Exact (LinearMap.inl ℤ V W) (LinearMap.snd ℤ V W)
        exact Function.Exact.inl_snd
      · apply F.mono_of_mono_map
        apply (ModuleCat.mono_iff_injective _).2
        change Function.Injective (LinearMap.inl ℤ V W)
        exact LinearMap.inl_injective
      · apply F.epi_of_epi_map
        apply (ModuleCat.epi_iff_surjective _).2
        change Function.Surjective (LinearMap.snd ℤ V W)
        intro y
        exact ⟨(0, y), rfl⟩
    have h := φ.map_shortExact' S hS
    simpa [S] using h
  have hsubzero : ∀ (φ : EulerPoincareFunction ℤ)
      {V : Type} [AddCommGroup V] [Module ℤ V] [Module.Finite ℤ V]
      [Subsingleton V], φ (FGModuleCat.of ℤ V) = 0 := by
    intro φ V _ _ _ _
    let e : V ≃ₗ[ℤ] (Fin 0 → ℤ) :=
      LinearEquiv.ofBijective 0 (by
        constructor
        · intro x y _
          exact Subsingleton.elim _ _
        · intro y
          exact ⟨0, Subsingleton.elim _ _⟩)
    simpa [hzero φ] using hIso φ e
  have hDS : ∀ (ι : Type) [Fintype ι] (Q : ι → Type)
      [∀ i, AddCommGroup (Q i)] [∀ i, Module ℤ (Q i)]
      [∀ i, Module.Finite ℤ (Q i)]
      [Module.Finite ℤ (DirectSum ι Q)] (φ : EulerPoincareFunction ℤ),
      φ (FGModuleCat.of ℤ (DirectSum ι Q)) =
        ∑ i : ι, φ (FGModuleCat.of ℤ (Q i)) := by
    intro ι
    refine Fintype.induction_empty_option
      (P := fun ι _ => ∀ (Q : ι → Type)
        [∀ i, AddCommGroup (Q i)] [∀ i, Module ℤ (Q i)]
        [∀ i, Module.Finite ℤ (Q i)]
        [Module.Finite ℤ (DirectSum ι Q)] (φ : EulerPoincareFunction ℤ),
        φ (FGModuleCat.of ℤ (DirectSum ι Q)) =
          ∑ i : ι, φ (FGModuleCat.of ℤ (Q i))) ?_ ?_ ?_ ι
    · intro α β _ e h Q hQadd hQmod hQfinite hQdirect φ
      let : Fintype α := Fintype.ofEquiv β e.symm
      let : ∀ i, AddCommGroup (Q i) := hQadd
      let : ∀ i, Module ℤ (Q i) := hQmod
      let : ∀ i, Module.Finite ℤ (Q i) := hQfinite
      let : ∀ i, AddCommGroup (Q (e i)) := fun i => hQadd (e i)
      let : ∀ i, Module ℤ (Q (e i)) := fun i => hQmod (e i)
      let : ∀ i, Module.Finite ℤ (Q (e i)) := fun i => hQfinite (e i)
      let : Module ℤ (DirectSum α (fun i => Q (e i))) :=
        @DirectSum.instModule ℤ Int.instSemiring α (fun i => Q (e i))
          (fun i => @AddCommGroup.toAddCommMonoid _ (hQadd (e i)))
          (fun i => hQmod (e i))
      have hfiniteDS :
          @Module.Finite ℤ (DirectSum α (fun i => Q (e i))) Int.instSemiring
            (@AddCommGroup.toAddCommMonoid _
              (inferInstance : AddCommGroup (DirectSum α (fun i => Q (e i)))))
            (AddCommGroup.toIntModule _) := by
        exact @Module.Finite.equiv ℤ
          (DirectSum α (fun i => Q (e i)))
          (DirectSum α (fun i => Q (e i)))
          Int.instSemiring
          (@AddCommGroup.toAddCommMonoid _
            (inferInstance : AddCommGroup (DirectSum α (fun i => Q (e i)))))
          (@DirectSum.instModule ℤ Int.instSemiring α (fun i => Q (e i))
            (fun i => @AddCommGroup.toAddCommMonoid _ (hQadd (e i)))
            (fun i => hQmod (e i)))
          (@AddCommGroup.toAddCommMonoid _
            (inferInstance : AddCommGroup (DirectSum α (fun i => Q (e i)))))
          (AddCommGroup.toIntModule _)
          (@Module.Finite.instDirectSum ℤ α Int.instSemiring inferInstance
            (fun i => Q (e i))
            (fun i => @AddCommGroup.toAddCommMonoid _ (hQadd (e i)))
            (fun i => hQmod (e i))
            (fun i => hQfinite (e i)))
          ((AddEquiv.refl (DirectSum α (fun i => Q (e i)))).toIntLinearEquiv
            (modM := @DirectSum.instModule ℤ Int.instSemiring α
              (fun i => Q (e i))
              (fun i => @AddCommGroup.toAddCommMonoid _ (hQadd (e i)))
              (fun i => hQmod (e i)))
            (modM₂ := AddCommGroup.toIntModule _))
      let : Module ℤ (DirectSum α (fun i => Q (e i))) :=
        AddCommGroup.toIntModule _
      let : Module.Finite ℤ (DirectSum α (fun i => Q (e i))) := hfiniteDS
      have h' :=
        @h (fun i => Q (e i))
          (fun i => hQadd (e i))
          (fun i => hQmod (e i))
          (fun i => hQfinite (e i))
          hfiniteDS φ
      have he :
          φ (FGModuleCat.of ℤ (DirectSum β Q)) =
            φ (FGModuleCat.of ℤ (DirectSum α (fun i => Q (e i)))) :=
        hIso φ ((DirectSum.equivCongrLeft (β := Q) e.symm).toIntLinearEquiv)
      calc
        φ (FGModuleCat.of ℤ (DirectSum β Q)) =
            φ (FGModuleCat.of ℤ (DirectSum α (fun i => Q (e i)))) := he
        _ = ∑ i : α, φ (FGModuleCat.of ℤ (Q (e i))) := h'
        _ = ∑ i : β, φ (FGModuleCat.of ℤ (Q i)) := by
          exact e.sum_comp (fun i => φ (FGModuleCat.of ℤ (Q i)))
    · intro Q hQadd hQmod hQfinite hQdirect φ
      have h := hsubzero φ (V := DirectSum PEmpty Q)
      simpa using h
    · intro α _ h Q hQadd hQmod hQfinite hQdirect φ
      let : ∀ i, AddCommGroup (Q i) := hQadd
      let : ∀ i, Module ℤ (Q i) := hQmod
      let : ∀ i, Module.Finite ℤ (Q i) := hQfinite
      let : ∀ i, AddCommGroup (Q (some i)) := fun i => hQadd (some i)
      let : ∀ i, Module ℤ (Q (some i)) := fun i => hQmod (some i)
      let : ∀ i, Module.Finite ℤ (Q (some i)) := fun i => hQfinite (some i)
      let : Module ℤ (DirectSum α (fun i => Q (some i))) :=
        @DirectSum.instModule ℤ Int.instSemiring α (fun i => Q (some i))
          (fun i => @AddCommGroup.toAddCommMonoid _ (hQadd (some i)))
          (fun i => hQmod (some i))
      let : AddCommGroup (Q none) := hQadd none
      let : Module ℤ (Q none) := hQmod none
      let : Module.Finite ℤ (Q none) := hQfinite none
      have hfiniteDS :
          @Module.Finite ℤ (DirectSum α (fun i => Q (some i))) Int.instSemiring
            (@AddCommGroup.toAddCommMonoid _
              (inferInstance : AddCommGroup (DirectSum α (fun i => Q (some i)))))
            (AddCommGroup.toIntModule _) := by
        exact @Module.Finite.equiv ℤ
          (DirectSum α (fun i => Q (some i)))
          (DirectSum α (fun i => Q (some i)))
          Int.instSemiring
          (@AddCommGroup.toAddCommMonoid _
            (inferInstance : AddCommGroup (DirectSum α (fun i => Q (some i)))))
          (@DirectSum.instModule ℤ Int.instSemiring α (fun i => Q (some i))
            (fun i => @AddCommGroup.toAddCommMonoid _ (hQadd (some i)))
            (fun i => hQmod (some i)))
          (@AddCommGroup.toAddCommMonoid _
            (inferInstance : AddCommGroup (DirectSum α (fun i => Q (some i)))))
          (AddCommGroup.toIntModule _)
          (@Module.Finite.instDirectSum ℤ α Int.instSemiring inferInstance
            (fun i => Q (some i))
            (fun i => @AddCommGroup.toAddCommMonoid _ (hQadd (some i)))
            (fun i => hQmod (some i))
            (fun i => hQfinite (some i)))
          ((AddEquiv.refl (DirectSum α (fun i => Q (some i)))).toIntLinearEquiv
            (modM := @DirectSum.instModule ℤ Int.instSemiring α
              (fun i => Q (some i))
              (fun i => @AddCommGroup.toAddCommMonoid _ (hQadd (some i)))
              (fun i => hQmod (some i)))
            (modM₂ := AddCommGroup.toIntModule _))
      let : Module ℤ (DirectSum α (fun i => Q (some i))) :=
        AddCommGroup.toIntModule _
      let : Module.Finite ℤ (DirectSum α (fun i => Q (some i))) := hfiniteDS
      let : Module ℤ
          (Q none × DirectSum α (fun i => Q (some i))) :=
        @Prod.instModule ℤ (Q none) (DirectSum α (fun i => Q (some i)))
          Int.instSemiring
          (@AddCommGroup.toAddCommMonoid _ (hQadd none))
          (@AddCommGroup.toAddCommMonoid _
            (inferInstance : AddCommGroup (DirectSum α (fun i => Q (some i)))))
          (hQmod none) (AddCommGroup.toIntModule _)
      let : Module.Finite ℤ
          (Q none × DirectSum α (fun i => Q (some i))) := by
        exact @Module.Finite.prod ℤ (Q none)
          (DirectSum α (fun i => Q (some i))) Int.instSemiring
          (@AddCommGroup.toAddCommMonoid _ (hQadd none)) (hQmod none)
          (@AddCommGroup.toAddCommMonoid _
            (inferInstance : AddCommGroup (DirectSum α (fun i => Q (some i)))))
          (AddCommGroup.toIntModule _) (hQfinite none) hfiniteDS
      have h' :=
        @h (fun i => Q (some i))
          (fun i => hQadd (some i))
          (fun i => hQmod (some i))
          (fun i => hQfinite (some i))
          hfiniteDS φ
      have he :
        φ (FGModuleCat.of ℤ (DirectSum (Option α) Q)) =
            φ (FGModuleCat.of ℤ
              (Q none × DirectSum α (fun i => Q (some i)))) :=
        hIso φ ((DirectSum.addEquivProdDirectSum (α := Q)).toIntLinearEquiv)
      calc
        φ (FGModuleCat.of ℤ (DirectSum (Option α) Q)) =
            φ (FGModuleCat.of ℤ (Q none × DirectSum α (fun i => Q (some i)))) := he
        _ = φ (FGModuleCat.of ℤ (Q none)) +
            φ (FGModuleCat.of ℤ (DirectSum α (fun i => Q (some i)))) := by
          simpa only using
            (hprod φ (V := Q none)
              (W := DirectSum α (fun i => Q (some i))))
        _ = φ (FGModuleCat.of ℤ (Q none)) +
            ∑ i : α, φ (FGModuleCat.of ℤ (Q (some i))) := by rw [h']
        _ = ∑ i : Option α, φ (FGModuleCat.of ℤ (Q i)) := by
          simp [Fintype.sum_option]
  have hfree : ∀ (φ : EulerPoincareFunction ℤ) (n : ℕ),
      φ (FGModuleCat.of ℤ (Fin n →₀ ℤ)) =
        integerEulerParameter φ * (n : ℤ) := by
    intro φ n
    let : Module.Finite ℤ (DirectSum (Fin n) (fun _ => ℤ)) :=
      Module.Finite.instDirectSum _
    have h := hDS (Fin n) (fun _ => ℤ) φ
    change φ (FGModuleCat.of ℤ (Fin n →₀ ℤ)) =
      φ (FGModuleCat.of ℤ ℤ) * (n : ℤ)
    calc
      φ (FGModuleCat.of ℤ (Fin n →₀ ℤ)) =
          φ (FGModuleCat.of ℤ (DirectSum (Fin n) (fun _ => ℤ))) :=
        hIso φ (finsuppLEquivDirectSum ℤ ℤ (Fin n))
      _ = ∑ i : Fin n, φ (FGModuleCat.of ℤ ℤ) := h
      _ = φ (FGModuleCat.of ℤ ℤ) * (n : ℤ) := by
        simp [Finset.sum_const, mul_comm]
  have hcyclic : ∀ (φ : EulerPoincareFunction ℤ) (a : ℤ) (ha : a ≠ 0),
      φ (FGModuleCat.of ℤ (ℤ ⧸ ℤ ∙ a)) = 0 := by
    intro φ a ha
    let L : Submodule ℤ ℤ := ℤ ∙ a
    let Q : Type := ℤ ⧸ L
    let f : ℤ →ₗ[ℤ] ℤ := LinearMap.toSpanSingleton ℤ ℤ a
    let g : ℤ →ₗ[ℤ] Q := L.mkQ
    let : Module.Finite ℤ Q := by infer_instance
    have hcomp : g.comp f = 0 := by
      ext
      apply (Submodule.Quotient.mk_eq_zero L).mpr
      simp [f, LinearMap.toSpanSingleton_apply, L]
    have hker : ∀ x, g x = 0 → x ∈ LinearMap.range f := by
      intro x hx
      have hxL : x ∈ L := (Submodule.Quotient.mk_eq_zero L).mp hx
      rcases (Submodule.mem_span_singleton.mp hxL) with ⟨c, hc⟩
      refine ⟨c, ?_⟩
      simpa [f, LinearMap.toSpanSingleton_apply, L, smul_eq_mul] using hc
    have hfun : Function.Exact f g :=
      LinearMap.exact_of_comp_of_mem_range hcomp hker
    have hf : Function.Injective f := by
      intro x y hxy
      apply mul_right_cancel₀ ha
      simpa [f, LinearMap.toSpanSingleton_apply, smul_eq_mul] using hxy
    have hg : Function.Surjective g := by
      exact L.mkQ_surjective
    let S : ShortComplex (FGModuleCat ℤ) :=
      ShortComplex.mk
        (FGModuleCat.ofHom f)
        (FGModuleCat.ofHom g) (by
          apply FGModuleCat.hom_ext
          apply LinearMap.ext
          intro x
          change g (f x) = 0
          exact DFunLike.congr_fun hcomp x)
    have hS : S.ShortExact := by
      apply ShortComplex.ShortExact.mk'
      · apply (ShortComplex.exact_map_iff_of_faithful S F).1
        apply (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact (S.map F)).2
        exact hfun
      · apply F.mono_of_mono_map
        apply (ModuleCat.mono_iff_injective _).2
        exact hf
      · apply F.epi_of_epi_map
        apply (ModuleCat.epi_iff_surjective _).2
        exact hg
    have h := φ.map_shortExact' S hS
    have h' : φ (FGModuleCat.of ℤ ℤ) =
        φ (FGModuleCat.of ℤ ℤ) + φ (FGModuleCat.of ℤ Q) := by
      simpa only [S] using h
    have hz : φ (FGModuleCat.of ℤ Q) = 0 := by
      omega
    simpa [Q, L] using hz
  have hclass : ∀ (φ ψ : EulerPoincareFunction ℤ) (M : FGModuleCat ℤ),
      ∃ n : ℕ,
        φ M = integerEulerParameter φ * (n : ℤ) ∧
          ψ M = integerEulerParameter ψ * (n : ℤ) := by
    intro φ ψ M
    obtain ⟨n, ι, fι, p, hp, powExp, ⟨eM⟩⟩ :=
      Module.equiv_free_prod_directSum (R := ℤ) (M := (M : Type))
    let : Fintype ι := fι
    let Q : ι → Type := fun i => ℤ ⧸ ℤ ∙ p i ^ powExp i
    let : Module.Finite ℤ (DirectSum ι Q) :=
      Module.Finite.instDirectSum Q
    have hvalue : ∀ θ : EulerPoincareFunction ℤ,
        θ (FGModuleCat.of ℤ (M : Type)) =
          integerEulerParameter θ * (n : ℤ) := by
      intro θ
      have hsum : ∑ i : ι, θ (FGModuleCat.of ℤ (Q i)) = 0 := by
        apply Finset.sum_eq_zero
        intro i hi
        simpa [Q] using
          hcyclic θ (p i ^ powExp i) (pow_ne_zero _ (hp i).ne_zero)
      have hds := hDS ι Q θ
      change θ (FGModuleCat.of ℤ (M : Type)) =
        integerEulerParameter θ * (n : ℤ)
      calc
        θ (FGModuleCat.of ℤ (M : Type)) =
            θ (FGModuleCat.of ℤ ((Fin n →₀ ℤ) × DirectSum ι Q)) :=
          hIso θ eM
        _ = θ (FGModuleCat.of ℤ (Fin n →₀ ℤ)) +
            θ (FGModuleCat.of ℤ (DirectSum ι Q)) := hprod θ
        _ = integerEulerParameter θ * (n : ℤ) := by
          rw [hfree θ n, hds, hsum, add_zero]
    refine ⟨n, hvalue φ, hvalue ψ⟩
  have hdim_shortExact : ∀ (S : ShortComplex (FGModuleCat ℤ)),
      S.ShortExact →
        Module.finrank ℤ (S.X₂ : Type) =
          Module.finrank ℤ (S.X₁ : Type) + Module.finrank ℤ (S.X₃ : Type) := by
    intro S hS
    let S' := S.map F
    have hExact : S'.Exact :=
      (ShortComplex.exact_map_iff_of_faithful S F).2 hS.exact
    let : Mono S.f := hS.mono_f
    let : Epi S.g := hS.epi_g
    let : CategoryTheory.Limits.PreservesLimitsOfShape
        CategoryTheory.Limits.WalkingCospan F := by infer_instance
    let : CategoryTheory.Limits.PreservesColimitsOfShape
        CategoryTheory.Limits.WalkingSpan F := by infer_instance
    let f : (S.X₁ : Type) →ₗ[ℤ] (S.X₂ : Type) := S.f.hom.hom
    let g : (S.X₂ : Type) →ₗ[ℤ] (S.X₃ : Type) := S.g.hom.hom
    let : Module ℤ ((S.X₂ : Type) ⧸ g.ker) := Submodule.Quotient.module g.ker
    let : Module ℤ g.range := g.range.module
    let : Module ℤ g.ker := g.ker.module
    let : Module ℤ f.range := f.range.module
    have hf : Function.Injective f := by
      change Function.Injective (F.map S.f).hom
      apply (ModuleCat.mono_iff_injective _).1
      exact F.map_mono S.f
    have hg : Function.Surjective g := by
      change Function.Surjective (F.map S.g).hom
      apply (ModuleCat.epi_iff_surjective _).1
      exact F.map_epi S.g
    have hfun : Function.Exact f g := by
      change Function.Exact (F.map S.f).hom (F.map S.g).hom
      exact (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact S').1 hExact
    have hrange : LinearMap.range f = LinearMap.ker g := hfun.linearMap_ker_eq.symm
    have hdim := Submodule.finrank_quotient_add_finrank (LinearMap.ker g)
    rw [g.quotKerEquivRange.finrank_eq] at hdim
    have hker : Module.finrank ℤ (LinearMap.ker g) =
        Module.finrank ℤ (LinearMap.range f) := by
      exact (LinearEquiv.ofEq (LinearMap.range f) (LinearMap.ker g) hrange).finrank_eq.symm
    have hrangef_nat :
        @Module.finrank ℤ (LinearMap.range f) Int.instSemiring
            (LinearMap.range f).addCommMonoid f.range.module =
          Module.finrank ℤ (S.X₁ : Type) := LinearMap.finrank_range_of_inj hf
    have hrangeg : Module.finrank ℤ (LinearMap.range g) =
        Module.finrank ℤ (S.X₃ : Type) := by
      exact (LinearEquiv.ofTop (LinearMap.range g)
        (LinearMap.range_eq_top.mpr hg)).finrank_eq
    change Module.finrank ℤ (S.X₂ : Type) =
      Module.finrank ℤ (S.X₁ : Type) + Module.finrank ℤ (S.X₃ : Type)
    calc
      Module.finrank ℤ (S.X₂ : Type) =
          Module.finrank ℤ (LinearMap.range g) +
            Module.finrank ℤ (LinearMap.ker g) := hdim.symm
      _ = Module.finrank ℤ (S.X₃ : Type) +
          Module.finrank ℤ (LinearMap.range f) := by
        rw [hrangeg, hker]
      _ = Module.finrank ℤ (S.X₁ : Type) +
          Module.finrank ℤ (S.X₃ : Type) := by rw [hrangef_nat]; ac_rfl
  constructor
  · intro φ ψ h
    cases φ with
    | mk φ hφ =>
      cases ψ with
      | mk ψ hψ =>
        have hparam : φ (FGModuleCat.of ℤ ℤ) = ψ (FGModuleCat.of ℤ ℤ) := by
          simpa [integerEulerParameter] using h
        have hfun : φ = ψ := by
          funext M
          obtain ⟨n, hφM, hψM⟩ :=
            hclass (⟨φ, hφ⟩ : EulerPoincareFunction ℤ)
              (⟨ψ, hψ⟩ : EulerPoincareFunction ℤ) M
          calc
            φ M = φ (FGModuleCat.of ℤ ℤ) * (n : ℤ) := by
              simpa [integerEulerParameter] using hφM
            _ = ψ (FGModuleCat.of ℤ ℤ) * (n : ℤ) := by rw [hparam]
            _ = ψ M := by
              simpa [integerEulerParameter] using hψM.symm
        cases hfun
        rfl
  · intro z
    let φz : EulerPoincareFunction ℤ :=
      { toFun := fun M => z * (Module.finrank ℤ (M : Type) : ℤ)
        map_shortExact' := by
          intro S hS
          have hdim := hdim_shortExact S hS
          change z * (Module.finrank ℤ (S.X₂ : Type) : ℤ) =
            z * (Module.finrank ℤ (S.X₁ : Type) : ℤ) +
              z * (Module.finrank ℤ (S.X₃ : Type) : ℤ)
          rw [hdim, Nat.cast_add, mul_add] }
    refine ⟨φz, ?_⟩
    simp [φz, integerEulerParameter]

/-! ## Exercise 3: the node `k[x,y]/(xy)` -/

/-- The homogeneous relation defining the nodal affine curve. -/
def nodePolynomialIdeal (k : Type u) [Field k] :
    Ideal (MvPolynomial (Fin 2) k) :=
  Ideal.span {MvPolynomial.X 0 * MvPolynomial.X 1}

/-- The nodal ring `k[x,y]/(xy)`. -/
abbrev nodeRing (k : Type u) [Field k] : Type u :=
  MvPolynomial (Fin 2) k ⧸ nodePolynomialIdeal k

/-- The two component ideals in the nodal ring. -/
def nodeXIdeal (k : Type u) [Field k] : Ideal (nodeRing k) :=
  Ideal.span {Ideal.Quotient.mk (nodePolynomialIdeal k) (MvPolynomial.X 0)}

def nodeYIdeal (k : Type u) [Field k] : Ideal (nodeRing k) :=
  Ideal.span {Ideal.Quotient.mk (nodePolynomialIdeal k) (MvPolynomial.X 1)}

/-- The two cyclic modules supported on the irreducible components of the node. -/
abbrev nodeXComponent (k : Type u) [Field k] : Type u :=
  nodeRing k ⧸ nodeXIdeal k

abbrev nodeYComponent (k : Type u) [Field k] : Type u :=
  nodeRing k ⧸ nodeYIdeal k

/-- The two component values of an Euler–Poincaré function on the nodal ring. -/
def nodeEulerParameters (k : Type u) [Field k]
    (φ : EulerPoincareFunction (nodeRing k)) : ℤ × ℤ :=
  (φ (FGModuleCat.of (nodeRing k) (nodeXComponent k)),
    φ (FGModuleCat.of (nodeRing k) (nodeYComponent k)))

private structure nodeMultiplicationData (k : Type u) [Field k] where
  qY : nodeRing k →+* Polynomial k
  qX : nodeRing k →+* Polynomial k
  sY : Polynomial k →+* nodeRing k
  sX : Polynomial k →+* nodeRing k
  x : nodeRing k
  y : nodeRing k
  hkerY : RingHom.ker qY = nodeXIdeal k
  hqYsY : qY.comp sY = RingHom.id (Polynomial k)
  hkerX : RingHom.ker qX = nodeYIdeal k
  hqXsX : qX.comp sX = RingHom.id (Polynomial k)
  hxy : x * y = 0
  hyx : y * x = 0
  hkerY_span : RingHom.ker qY = Ideal.span ({x} : Set (nodeRing k))
  hkerX_span : RingHom.ker qX = Ideal.span ({y} : Set (nodeRing k))
  hIspan : nodeXIdeal k = Ideal.span ({x} : Set (nodeRing k))
  hJspan : nodeYIdeal k = Ideal.span ({y} : Set (nodeRing k))
  hsY_X : sY (Polynomial.X : Polynomial k) = y
  hsX_X : sX (Polynomial.X : Polynomial k) = x

private def nodeMultiplicationData_exists
    (k : Type u) [Field k] : nodeMultiplicationData k := by
  classical
  let A := nodeRing k
  let B := Polynomial k
  let q0 : MvPolynomial (Fin 2) k →+* MvPolynomial (Fin 1) k :=
    MvPolynomial.eval₂Hom MvPolynomial.C ![0, MvPolynomial.X 0]
  let r0 : MvPolynomial (Fin 1) k →+* MvPolynomial (Fin 2) k :=
    MvPolynomial.eval₂Hom MvPolynomial.C ![MvPolynomial.X 1]
  have hq0r0 : q0.comp r0 = RingHom.id (MvPolynomial (Fin 1) k) := by
    apply MvPolynomial.ringHom_ext'
    · ext r
      simp [q0, r0]
    · intro i
      fin_cases i; simp [q0, r0]
  have hq0r0_apply (p : MvPolynomial (Fin 1) k) :
      q0 (r0 p) = p := by
    simpa using RingHom.congr_fun hq0r0 p
  let e1 : MvPolynomial (Fin 2) k ≃+* Polynomial (MvPolynomial (Fin 1) k) :=
    MvPolynomial.finSuccEquiv k 1
  have hq0 : q0 =
      (Polynomial.evalRingHom (0 : MvPolynomial (Fin 1) k)).comp e1.toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp [q0, e1, MvPolynomial.finSuccEquiv_apply]
    · intro i
      simp only [q0, MvPolynomial.eval₂Hom_X', RingHom.comp_apply]
      fin_cases i
      · change (0 : MvPolynomial (Fin 1) k) =
          Polynomial.eval 0 (e1 (MvPolynomial.X 0))
        rw [show e1 (MvPolynomial.X 0) = Polynomial.X by
          simpa [e1] using
            (MvPolynomial.finSuccEquiv_X_zero (R := k) (n := 1))]
        simp
      · change MvPolynomial.X 0 =
          Polynomial.eval 0 (e1 (MvPolynomial.X 1))
        rw [show e1 (MvPolynomial.X (1 : Fin 2)) =
          Polynomial.C (MvPolynomial.X (0 : Fin 1)) by
            simpa [e1] using
              (MvPolynomial.finSuccEquiv_X_succ (R := k) (n := 1) (j := 0))]
        simp
  have hker0 : RingHom.ker q0 = Ideal.span {MvPolynomial.X 0} := by
    rw [hq0, ← RingHom.comap_ker, Polynomial.ker_evalRingHom]
    change (Ideal.span {Polynomial.X - Polynomial.C 0}).comap
        (e1 : MvPolynomial (Fin 2) k →+* Polynomial (MvPolynomial (Fin 1) k)) = _
    rw [show (Ideal.span {Polynomial.X - Polynomial.C 0}).comap
          (e1 : MvPolynomial (Fin 2) k →+* Polynomial (MvPolynomial (Fin 1) k)) =
          (Ideal.span {Polynomial.X - Polynomial.C 0}).map e1.symm from
        (Ideal.map_symm e1).symm, Ideal.map_span]
    have he1symm :
        e1.symm (Polynomial.X : Polynomial (MvPolynomial (Fin 1) k)) =
          MvPolynomial.X 0 := by
      apply e1.injective
      simp [e1, MvPolynomial.finSuccEquiv_apply]
    simp [he1symm]
  let e0a : MvPolynomial (Fin 1) k ≃+* Polynomial (MvPolynomial (Fin 0) k) := by
    simpa using (MvPolynomial.finSuccEquiv k 0).toRingEquiv
  let eempty : MvPolynomial (Fin 0) k ≃+* k :=
    MvPolynomial.isEmptyRingEquiv k (Fin 0)
  let e0 : MvPolynomial (Fin 1) k ≃+* Polynomial k :=
    e0a.trans (Polynomial.mapEquiv eempty)
  let qY0 : MvPolynomial (Fin 2) k →+* Polynomial k :=
    e0.toRingHom.comp q0
  have hkerY0 : RingHom.ker qY0 = Ideal.span {MvPolynomial.X 0} := by
    change RingHom.ker (e0.toRingHom.comp q0) = Ideal.span {MvPolynomial.X 0}
    rw [RingHom.ker_comp_of_injective q0 e0.injective, hker0]
  have hqY0_XY : qY0 (MvPolynomial.X 0 * MvPolynomial.X 1) = 0 := by
    simp [qY0, q0]
  have hle : nodePolynomialIdeal k ≤ RingHom.ker qY0 := by
    rw [nodePolynomialIdeal]
    exact Ideal.span_le.2 (by simpa [RingHom.mem_ker] using hqY0_XY)
  let qY : A →+* Polynomial k :=
    Ideal.Quotient.lift (nodePolynomialIdeal k) qY0 hle
  have hkerY : RingHom.ker qY = nodeXIdeal k := by
    change RingHom.ker (Ideal.Quotient.lift (nodePolynomialIdeal k) qY0 hle) = _
    rw [Ideal.ker_quotient_lift qY0 hle, hkerY0, Ideal.map_span]
    simp [nodeXIdeal]
  have hqYmk (p : MvPolynomial (Fin 2) k) :
      qY (Ideal.Quotient.mk (nodePolynomialIdeal k) p) = qY0 p := by
    change qY0 p = qY0 p
    rfl
  let sY : Polynomial k →+* A :=
    (Ideal.Quotient.mk (nodePolynomialIdeal k)).comp
      (r0.comp e0.symm.toRingHom)
  have hqYsY : qY.comp sY = RingHom.id (Polynomial k) := by
    apply RingHom.ext
    intro p
    change qY (Ideal.Quotient.mk (nodePolynomialIdeal k)
      (r0 (e0.symm p))) = p
    rw [hqYmk]
    change e0 (q0 (r0 (e0.symm p))) = p
    rw [hq0r0_apply, e0.apply_symm_apply]
  let swap : MvPolynomial (Fin 2) k ≃ₐ[k] MvPolynomial (Fin 2) k :=
    MvPolynomial.renameEquiv k (Equiv.swap 0 1)
  let qX0 : MvPolynomial (Fin 2) k →+* Polynomial k :=
    qY0.comp swap.toRingHom
  have hswapker :
      (Ideal.span {MvPolynomial.X 0}).comap swap.toRingHom =
        Ideal.span {MvPolynomial.X 1} := by
    change (Ideal.span {MvPolynomial.X 0}).comap
        (swap : MvPolynomial (Fin 2) k →+* MvPolynomial (Fin 2) k) = _
    rw [show (Ideal.span {MvPolynomial.X 0}).comap
          (swap : MvPolynomial (Fin 2) k →+* MvPolynomial (Fin 2) k) =
          (Ideal.span {MvPolynomial.X 0}).map swap.symm.toRingEquiv from
        (Ideal.map_symm swap.toRingEquiv).symm, Ideal.map_span]
    congr 1
    simp [swap, MvPolynomial.renameEquiv_apply]
  have hkerX0 : RingHom.ker qX0 = Ideal.span {MvPolynomial.X 1} := by
    change RingHom.ker (qY0.comp swap.toRingHom) = _
    rw [← RingHom.comap_ker, hkerY0]
    exact hswapker
  let sX0 : Polynomial k →+* MvPolynomial (Fin 2) k :=
    swap.symm.toRingHom.comp (r0.comp e0.symm.toRingHom)
  have hqX0sX0 : qX0.comp sX0 = RingHom.id (Polynomial k) := by
    apply RingHom.ext
    intro p
    change qY0 (swap (swap.symm (r0 (e0.symm p)))) = p
    rw [swap.apply_symm_apply]
    change e0 (q0 (r0 (e0.symm p))) = p
    rw [hq0r0_apply, e0.apply_symm_apply]
  have hqX0_XY : qX0 (MvPolynomial.X 0 * MvPolynomial.X 1) = 0 := by
    have hx0 : swap (MvPolynomial.X (0 : Fin 2)) = MvPolynomial.X 1 := by
      simp [swap, MvPolynomial.renameEquiv_apply]
    have hx1 : swap (MvPolynomial.X (1 : Fin 2)) = MvPolynomial.X 0 := by
      simp [swap, MvPolynomial.renameEquiv_apply]
    calc
      qX0 (MvPolynomial.X 0 * MvPolynomial.X 1) =
          qY0 (swap (MvPolynomial.X 0 * MvPolynomial.X 1)) := by rfl
      _ = qY0 (MvPolynomial.X 1 * MvPolynomial.X 0) := by
        rw [map_mul, hx0, hx1]
      _ = qY0 (MvPolynomial.X 0 * MvPolynomial.X 1) := by rw [mul_comm]
      _ = 0 := hqY0_XY
  have hleX : nodePolynomialIdeal k ≤ RingHom.ker qX0 := by
    rw [nodePolynomialIdeal]
    exact Ideal.span_le.2 (by simpa [RingHom.mem_ker] using hqX0_XY)
  let qX : A →+* Polynomial k :=
    Ideal.Quotient.lift (nodePolynomialIdeal k) qX0 hleX
  have hkerX : RingHom.ker qX = nodeYIdeal k := by
    change RingHom.ker (Ideal.Quotient.lift (nodePolynomialIdeal k) qX0 hleX) = _
    rw [Ideal.ker_quotient_lift qX0 hleX, hkerX0, Ideal.map_span]
    simp [nodeYIdeal]
  let sX : Polynomial k →+* A :=
    (Ideal.Quotient.mk (nodePolynomialIdeal k)).comp
      (sX0)
  have hqXsX : qX.comp sX = RingHom.id (Polynomial k) := by
    apply RingHom.ext
    intro p
    change qX (Ideal.Quotient.mk (nodePolynomialIdeal k) (sX0 p)) = p
    change qX0 (sX0 p) = p
    exact RingHom.congr_fun hqX0sX0 p
  let x : A := Ideal.Quotient.mk (nodePolynomialIdeal k) (MvPolynomial.X 0)
  let y : A := Ideal.Quotient.mk (nodePolynomialIdeal k) (MvPolynomial.X 1)
  have hxy : x * y = 0 := by
    change Ideal.Quotient.mk (nodePolynomialIdeal k)
      (MvPolynomial.X 0 * MvPolynomial.X 1) = 0
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    exact Ideal.subset_span (by simp)
  have hyx : y * x = 0 := by rw [mul_comm, hxy]
  have hIspan : nodeXIdeal k = Ideal.span {x} := by
    change Ideal.span {Ideal.Quotient.mk (nodePolynomialIdeal k)
      (MvPolynomial.X 0)} = Ideal.span {Ideal.Quotient.mk (nodePolynomialIdeal k)
        (MvPolynomial.X 0)}
    rfl
  have hJspan : nodeYIdeal k = Ideal.span {y} := by
    change Ideal.span {Ideal.Quotient.mk (nodePolynomialIdeal k)
      (MvPolynomial.X 1)} = Ideal.span {Ideal.Quotient.mk (nodePolynomialIdeal k)
        (MvPolynomial.X 1)}
    rfl
  have he0symm_X : e0.symm (Polynomial.X : Polynomial k) =
      MvPolynomial.X 0 := by
    apply e0.injective
    simp [e0, e0a, eempty, MvPolynomial.finSuccEquiv_apply]
  have hsY_X : sY (Polynomial.X : Polynomial k) = y := by
    change (Ideal.Quotient.mk (nodePolynomialIdeal k))
      (r0 (e0.symm Polynomial.X)) = y
    rw [he0symm_X]
    simp [y, r0]
  have hsX_X : sX (Polynomial.X : Polynomial k) = x := by
    change (Ideal.Quotient.mk (nodePolynomialIdeal k))
      (sX0 Polynomial.X) = x
    change (Ideal.Quotient.mk (nodePolynomialIdeal k))
      (swap.symm (r0 (e0.symm Polynomial.X))) = x
    rw [he0symm_X]
    simp [x, r0, swap, MvPolynomial.renameEquiv_apply]
  exact
    { qY := qY
      qX := qX
      sY := sY
      sX := sX
      x := x
      y := y
      hkerY := hkerY
      hqYsY := hqYsY
      hkerX := hkerX
      hqXsX := hqXsX
      hxy := hxy
      hyx := hyx
      hkerY_span := by simpa [x, nodeXIdeal] using hkerY
      hkerX_span := by simpa [y, nodeYIdeal] using hkerX
      hIspan := hIspan
      hJspan := hJspan
      hsY_X := hsY_X
      hsX_X := hsX_X }

private theorem eulerPoincareFunction_node_injective
    (k : Type u) [Field k] [IsAlgClosed k] :
    Function.Injective (nodeEulerParameters (k := k)) := by
  classical
  let A := nodeRing k
  let B := Polynomial k
  let d := nodeMultiplicationData_exists k
  let qY : A →+* B := d.qY
  let qX : A →+* B := d.qX
  let sY : B →+* A := d.sY
  let sX : B →+* A := d.sX
  let x : A := d.x
  let y : A := d.y
  have hkerY : RingHom.ker qY = nodeXIdeal k := by
    change RingHom.ker d.qY = nodeXIdeal k
    exact d.hkerY
  have hqYsY : qY.comp sY = RingHom.id B := by
    change d.qY.comp d.sY = RingHom.id (Polynomial k)
    exact d.hqYsY
  have hkerX : RingHom.ker qX = nodeYIdeal k := by
    change RingHom.ker d.qX = nodeYIdeal k
    exact d.hkerX
  have hqXsX : qX.comp sX = RingHom.id B := by
    change d.qX.comp d.sX = RingHom.id (Polynomial k)
    exact d.hqXsX
  have hxy : x * y = 0 := by
    change d.x * d.y = 0
    exact d.hxy
  have hyx : y * x = 0 := by
    change d.y * d.x = 0
    exact d.hyx
  have hkerY_span : RingHom.ker qY = Ideal.span {x} := by
    change RingHom.ker d.qY = Ideal.span {d.x}
    exact d.hkerY_span
  have hkerX_span : RingHom.ker qX = Ideal.span {y} := by
    change RingHom.ker d.qX = Ideal.span {d.y}
    exact d.hkerX_span
  have hspan_smul :
      ∀ {V : Type u} [AddCommGroup V] [Module A V]
        {r a : A} {z : V}, r ∈ Ideal.span {a} → a • z = 0 → r • z = 0 := by
    intro V _ _ r a z hr hz
    rcases Ideal.mem_span_singleton'.mp hr with ⟨c, hc⟩
    rw [← hc, ← smul_smul, hz]
    change (LinearMap.lsmul A V c) (0 : V) = 0
    exact (LinearMap.lsmul A V c).map_zero
  have hcompat_of_annihilated :
      ∀ {V : Type u} [AddCommGroup V] [Module A V]
        (a : A) (s : B →+* A) (q : A →+* B)
        (hker : RingHom.ker q = Ideal.span {a})
        (hqs : q.comp s = RingHom.id B)
        (b : A) (z : V), a • z = 0 → s (q b) • z = b • z := by
    intro V _ _ a s q hker hqs b z hz
    have hdiff : b - s (q b) ∈ Ideal.span {a} := by
      rw [← hker, RingHom.mem_ker]
      have h := RingHom.congr_fun hqs (q b)
      rw [map_sub]
      have hs : q (s (q b)) = q b := by
        simpa only [RingHom.comp_apply, RingHom.id_apply] using h
      rw [hs]
      simp
    have hz' := hspan_smul hdiff hz
    exact (sub_eq_zero.mp (by simpa only [sub_smul] using hz')).symm
  have hcompatY_of_annihilated :
      ∀ {V : Type u} [AddCommGroup V] [Module A V]
        (a : A) (z : V), x • z = 0 → sY (qY a) • z = a • z := by
    intro V _ _ a z hz
    exact hcompat_of_annihilated (V := V) x sY qY hkerY_span hqYsY a z hz
  have hcompatX_of_annihilated :
      ∀ {V : Type u} [AddCommGroup V] [Module A V]
        (a : A) (z : V), y • z = 0 → sX (qX a) • z = a • z := by
    intro V _ _ a z hz
    exact hcompat_of_annihilated (V := V) y sX qX hkerX_span hqXsX a z hz
  have hrange_annihilated :
      ∀ {V : Type u} [AddCommGroup V] [Module A V]
        (m : V →ₗ[A] V) (hm : ∀ z : V, m z = x • z)
        (z : LinearMap.range m), y • (z : V) = 0 := by
    intro V _ _ m hm z
    obtain ⟨w, hw⟩ := z.property
    rw [← hw, hm]
    calc
      y • (x • w) = (y * x) • w := smul_smul y x w
      _ = 0 := by
        rw [hyx]
        exact zero_smul A w
  have hzero : ∀ (φ : EulerPoincareFunction A),
      φ (FGModuleCat.of A (Fin 0 → A)) = 0 := by
    intro φ
    let Z : Type u := Fin 0 → A
    let : Subsingleton Z := by
      dsimp [Z]
      infer_instance
    let F := forget₂ (FGModuleCat A) (ModuleCat A)
    let S : ShortComplex (FGModuleCat A) :=
      ShortComplex.mk
        (FGModuleCat.ofHom (LinearMap.id : Z →ₗ[A] Z))
        (FGModuleCat.ofHom (0 : Z →ₗ[A] Z)) (by
          apply FGModuleCat.hom_ext
          apply LinearMap.ext
          intro z
          change (0 : Z) = 0
          rfl)
    have hS : S.ShortExact := by
      apply ShortComplex.ShortExact.mk'
      · apply (ShortComplex.exact_map_iff_of_faithful S F).1
        apply (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact (S.map F)).2
        change Function.Exact (LinearMap.id : Z →ₗ[A] Z) (0 : Z →ₗ[A] Z)
        intro z
        constructor
        · intro _
          exact ⟨z, by rfl⟩
        · rintro ⟨z', rfl⟩
          rfl
      · apply F.mono_of_mono_map
        apply (ModuleCat.mono_iff_injective _).2
        intro x y hxy
        exact hxy
      · apply F.epi_of_epi_map
        apply (ModuleCat.epi_iff_surjective _).2
        intro z
        exact ⟨0, by change (0 : Z) = z; exact Subsingleton.elim _ _⟩
    have h := φ.map_shortExact' S hS
    have h' : φ (FGModuleCat.of A Z) =
        φ (FGModuleCat.of A Z) + φ (FGModuleCat.of A Z) := by
      simpa [S] using h
    have hz : φ (FGModuleCat.of A Z) = 0 := by omega
    simpa [Z] using hz
  have hIso : ∀ (φ : EulerPoincareFunction A)
      {V W : Type u} [AddCommGroup V] [Module A V]
      [Module.Finite A V] [AddCommGroup W] [Module A W]
      [Module.Finite A W] (e : V ≃ₗ[A] W),
      φ (FGModuleCat.of A V) = φ (FGModuleCat.of A W) := by
    intro φ V W _ _ _ _ _ _ e
    let Z : Type u := Fin 0 → A
    let : Subsingleton Z := by
      dsimp [Z]
      infer_instance
    let F := forget₂ (FGModuleCat A) (ModuleCat A)
    let S : ShortComplex (FGModuleCat A) :=
      ShortComplex.mk
        (FGModuleCat.ofHom (0 : Z →ₗ[A] V))
        (FGModuleCat.ofHom e.toLinearMap) (by
          apply FGModuleCat.hom_ext
          apply LinearMap.ext
          intro z
          change e.toLinearMap (0 : V) = 0
          simp)
    have hS : S.ShortExact := by
      apply ShortComplex.ShortExact.mk'
      · apply (ShortComplex.exact_map_iff_of_faithful S F).1
        apply (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact (S.map F)).2
        change Function.Exact (0 : Z →ₗ[A] V) e.toLinearMap
        intro w
        constructor
        · intro hw
          change e w = 0 at hw
          have hw0 : w = 0 := e.injective (hw.trans e.map_zero.symm)
          exact ⟨0, by change (0 : V) = w; rw [hw0]⟩
        · rintro ⟨z, hz⟩
          change e w = 0
          rw [← hz]
          simp
      · apply F.mono_of_mono_map
        apply (ModuleCat.mono_iff_injective _).2
        intro x y hxy
        exact @Subsingleton.elim Z _ (x : Z) (y : Z)
      · apply F.epi_of_epi_map
        apply (ModuleCat.epi_iff_surjective _).2
        exact e.surjective
    have h := φ.map_shortExact' S hS
    have h' : φ (FGModuleCat.of A V) =
        φ (FGModuleCat.of A Z) + φ (FGModuleCat.of A W) := by
      simpa [S] using h
    simpa [Z, hzero φ, add_zero] using h'
  have hprod : ∀ (φ : EulerPoincareFunction A)
      {V W : Type u} [AddCommGroup V] [Module A V]
      [Module.Finite A V] [AddCommGroup W] [Module A W]
      [Module.Finite A W],
      φ (FGModuleCat.of A (V × W)) =
        φ (FGModuleCat.of A V) + φ (FGModuleCat.of A W) := by
    intro φ V W _ _ _ _ _ _
    let F := forget₂ (FGModuleCat A) (ModuleCat A)
    let S : ShortComplex (FGModuleCat A) :=
      ShortComplex.mk
        (FGModuleCat.ofHom (LinearMap.inl A V W))
        (FGModuleCat.ofHom (LinearMap.snd A V W)) (by
          apply FGModuleCat.hom_ext
          apply LinearMap.ext
          intro z
          rfl)
    have hS : S.ShortExact := by
      apply ShortComplex.ShortExact.mk'
      · apply (ShortComplex.exact_map_iff_of_faithful S F).1
        apply (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact (S.map F)).2
        change Function.Exact (LinearMap.inl A V W) (LinearMap.snd A V W)
        exact Function.Exact.inl_snd
      · apply F.mono_of_mono_map
        apply (ModuleCat.mono_iff_injective _).2
        exact LinearMap.inl_injective
      · apply F.epi_of_epi_map
        apply (ModuleCat.epi_iff_surjective _).2
        intro z
        exact ⟨(0, z), rfl⟩
    simpa [S] using φ.map_shortExact' S hS
  have hsubzero : ∀ (φ : EulerPoincareFunction A)
      {V : Type u} [AddCommGroup V] [Module A V] [Module.Finite A V]
      [Subsingleton V], φ (FGModuleCat.of A V) = 0 := by
    intro φ V _ _ _ _
    let e : V ≃ₗ[A] (Fin 0 → A) :=
      LinearEquiv.ofBijective 0 (by
        constructor
        · intro x y _
          exact Subsingleton.elim _ _
        · intro y
          exact ⟨0, Subsingleton.elim _ _⟩)
    simpa [hzero φ] using hIso φ e
  intro φ ψ h
  · have hcyclicFor :
        ∀ (θ : EulerPoincareFunction A)
          (q : A →+* B) (hq : Function.Surjective q) (p : B) (hp : p ≠ 0),
          letI : Module A B := Module.compHom B q
          let qLin : A →ₗ[A] B :=
            { toFun := q
              map_add' := by intro a b; simp
              map_smul' := by
                intro a b
                change q (a * b) = q a • q b
                simp [smul_eq_mul] }
          letI : Module.Finite A B := Module.Finite.of_surjective qLin hq
          let L : Submodule B B := B ∙ p
          let Q : Type u := B ⧸ L
          letI : Module A Q := Module.compHom Q q
          let g : B →ₗ[A] Q :=
            { toFun := L.mkQ
              map_add' := by intro z w; rfl
              map_smul' := by
                intro a z
                change L.mkQ (q a * z) = q a • L.mkQ z
                rfl }
          letI : Module.Finite A Q := Module.Finite.of_surjective g L.mkQ_surjective
          θ (FGModuleCat.of A Q) = 0 := by
      intro θ q hq p hp
      let : Module A B := Module.compHom B q
      let qLin : A →ₗ[A] B :=
        { toFun := q
          map_add' := by intro a b; simp
          map_smul' := by
            intro a b
            change q (a * b) = q a • q b
            simp [smul_eq_mul] }
      let : Module.Finite A B := Module.Finite.of_surjective qLin hq
      let L : Submodule B B := B ∙ p
      let Q : Type u := B ⧸ L
      let : Module A Q := Module.compHom Q q
      let f : B →ₗ[A] B :=
        { toFun := fun z => p * z
          map_add' := by intro z w; simp [mul_add]
          map_smul' := by
            intro a z
            change p * (q a * z) = q a • (p * z)
            simp [smul_eq_mul, mul_assoc, mul_comm] }
      let g : B →ₗ[A] Q :=
        { toFun := L.mkQ
          map_add' := by intro z w; rfl
          map_smul' := by
            intro a z
            change L.mkQ (q a * z) = q a • L.mkQ z
            rfl }
      have hcomp : g.comp f = 0 := by
        ext z
        change L.mkQ (p * z) = 0
        apply (Submodule.Quotient.mk_eq_zero L).2
        exact (Submodule.mem_span_singleton).2 ⟨z, by simp [smul_eq_mul, mul_comm]⟩
      have hker : ∀ z, g z = 0 → z ∈ LinearMap.range f := by
        intro z hz
        have hzL : z ∈ L := (Submodule.Quotient.mk_eq_zero L).1 hz
        rcases (Submodule.mem_span_singleton.mp hzL) with ⟨c, hc⟩
        refine ⟨c, ?_⟩
        simpa [f, smul_eq_mul, mul_comm] using hc
      have hfun : Function.Exact f g :=
        LinearMap.exact_of_comp_of_mem_range hcomp hker
      have hf : Function.Injective f := by
        intro z w hzw
        apply mul_left_cancel₀ hp
        simpa [f, smul_eq_mul] using hzw
      have hg : Function.Surjective g := L.mkQ_surjective
      let : Module.Finite A Q := Module.Finite.of_surjective g hg
      let F := forget₂ (FGModuleCat A) (ModuleCat A)
      let S : ShortComplex (FGModuleCat A) :=
        ShortComplex.mk
          (FGModuleCat.ofHom f)
          (FGModuleCat.ofHom g) (by
            apply FGModuleCat.hom_ext
            apply LinearMap.ext
            intro z
            change g (f z) = 0
            exact DFunLike.congr_fun hcomp z)
      have hS : S.ShortExact := by
        apply ShortComplex.ShortExact.mk'
        · apply (ShortComplex.exact_map_iff_of_faithful S F).1
          apply (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact (S.map F)).2
          change Function.Exact f g
          exact hfun
        · apply F.mono_of_mono_map
          apply (ModuleCat.mono_iff_injective _).2
          change Function.Injective f
          exact hf
        · apply F.epi_of_epi_map
          apply (ModuleCat.epi_iff_surjective _).2
          change Function.Surjective g
          exact hg
      have hval := θ.map_shortExact' S hS
      have hval' : θ (FGModuleCat.of A B) =
          θ (FGModuleCat.of A B) + θ (FGModuleCat.of A Q) := by
        simpa [S] using hval
      have hz : θ (FGModuleCat.of A Q) = 0 := by omega
      simpa [Q, L] using hz
    have hDS : ∀ (θ : EulerPoincareFunction A)
        (ι : Type u) [Fintype ι] (Q : ι → Type u)
        [∀ i, AddCommGroup (Q i)] [∀ i, Module A (Q i)]
        [∀ i, Module.Finite A (Q i)]
        [Module.Finite A (DirectSum ι Q)],
        θ (FGModuleCat.of A (DirectSum ι Q)) =
          ∑ i : ι, θ (FGModuleCat.of A (Q i)) := by
      intro θ ι
      refine Fintype.induction_empty_option
        (P := fun ι _ => ∀ (Q : ι → Type u)
          [∀ i, AddCommGroup (Q i)] [∀ i, Module A (Q i)]
          [∀ i, Module.Finite A (Q i)]
          [Module.Finite A (DirectSum ι Q)],
          θ (FGModuleCat.of A (DirectSum ι Q)) =
            ∑ i : ι, θ (FGModuleCat.of A (Q i))) ?_ ?_ ?_ ι
      · intro α β _ e h Q hQadd hQmod hQfinite hQdirect
        let : Fintype α := Fintype.ofEquiv β e.symm
        let : ∀ i, AddCommGroup (Q i) := hQadd
        let : ∀ i, Module A (Q i) := hQmod
        let : ∀ i, Module.Finite A (Q i) := hQfinite
        let : ∀ i, AddCommGroup (Q (e i)) := fun i => hQadd (e i)
        let : ∀ i, Module A (Q (e i)) := fun i => hQmod (e i)
        let : ∀ i, Module.Finite A (Q (e i)) := fun i => hQfinite (e i)
        let : Module A (DirectSum α (fun i => Q (e i))) :=
          @DirectSum.instModule A (inferInstance : Semiring A) α
            (fun i => Q (e i))
            (fun i => @AddCommGroup.toAddCommMonoid _ (hQadd (e i)))
            (fun i => hQmod (e i))
        let : Module.Finite A (DirectSum α (fun i => Q (e i))) :=
          @Module.Finite.instDirectSum A α (inferInstance : Semiring A)
            inferInstance (fun i => Q (e i))
            (fun i => @AddCommGroup.toAddCommMonoid _ (hQadd (e i)))
            (fun i => hQmod (e i)) (fun i => hQfinite (e i))
        have h' := h (fun i => Q (e i))
        have he :
            θ (FGModuleCat.of A (DirectSum β Q)) =
              θ (FGModuleCat.of A (DirectSum α (fun i => Q (e i)))) :=
          hIso θ (DirectSum.lequivCongrLeft A e.symm)
        calc
          θ (FGModuleCat.of A (DirectSum β Q)) =
              θ (FGModuleCat.of A (DirectSum α (fun i => Q (e i)))) := he
          _ = ∑ i : α, θ (FGModuleCat.of A (Q (e i))) := h'
          _ = ∑ i : β, θ (FGModuleCat.of A (Q i)) := by
            exact e.sum_comp (fun i => θ (FGModuleCat.of A (Q i)))
      · intro Q hQadd hQmod hQfinite hQdirect
        have h' := hsubzero θ (V := DirectSum PEmpty Q)
        simpa using h'
      · intro α _ h Q hQadd hQmod hQfinite hQdirect
        let : ∀ i, AddCommGroup (Q i) := hQadd
        let : ∀ i, Module A (Q i) := hQmod
        let : ∀ i, Module.Finite A (Q i) := hQfinite
        let : ∀ i, AddCommGroup (Q (some i)) := fun i => hQadd (some i)
        let : ∀ i, Module A (Q (some i)) := fun i => hQmod (some i)
        let : ∀ i, Module.Finite A (Q (some i)) := fun i => hQfinite (some i)
        let : Module A (DirectSum α (fun i => Q (some i))) :=
          @DirectSum.instModule A (inferInstance : Semiring A) α
            (fun i => Q (some i))
            (fun i => @AddCommGroup.toAddCommMonoid _ (hQadd (some i)))
            (fun i => hQmod (some i))
        let : Module.Finite A (DirectSum α (fun i => Q (some i))) :=
          @Module.Finite.instDirectSum A α (inferInstance : Semiring A)
            inferInstance (fun i => Q (some i))
            (fun i => @AddCommGroup.toAddCommMonoid _ (hQadd (some i)))
            (fun i => hQmod (some i)) (fun i => hQfinite (some i))
        let : AddCommGroup (Q none) := hQadd none
        let : Module A (Q none) := hQmod none
        let : Module.Finite A (Q none) := hQfinite none
        let : Module A (Q none × DirectSum α (fun i => Q (some i))) :=
          @Prod.instModule A (Q none) (DirectSum α (fun i => Q (some i)))
            (inferInstance : Semiring A)
            (@AddCommGroup.toAddCommMonoid _ (hQadd none))
            (@AddCommGroup.toAddCommMonoid _
              (inferInstance : AddCommGroup (DirectSum α (fun i => Q (some i)))))
            (hQmod none)
            (inferInstance : Module A (DirectSum α (fun i => Q (some i))))
        let : Module.Finite A
            (Q none × DirectSum α (fun i => Q (some i))) := inferInstance
        have h' := h (fun i => Q (some i))
        have he :
            θ (FGModuleCat.of A (DirectSum (Option α) Q)) =
              θ (FGModuleCat.of A
                (Q none × DirectSum α (fun i => Q (some i)))) :=
          hIso θ (DirectSum.lequivProdDirectSum A (α := Q))
        calc
          θ (FGModuleCat.of A (DirectSum (Option α) Q)) =
              θ (FGModuleCat.of A
                (Q none × DirectSum α (fun i => Q (some i)))) := he
          _ = θ (FGModuleCat.of A (Q none)) +
              θ (FGModuleCat.of A (DirectSum α (fun i => Q (some i)))) := by
            simpa only using hprod θ (V := Q none)
              (W := DirectSum α (fun i => Q (some i)))
          _ = θ (FGModuleCat.of A (Q none)) +
              ∑ i : α, θ (FGModuleCat.of A (Q (some i))) := by rw [h']
          _ = ∑ i : Option α, θ (FGModuleCat.of A (Q i)) := by
            simp [Fintype.sum_option]
    let : Module A B := Module.compHom B qY
    have hsurjY : Function.Surjective qY := by
      intro b
      refine ⟨sY b, ?_⟩
      simpa only [RingHom.comp_apply, RingHom.id_apply] using
        RingHom.congr_fun hqYsY b
    let qLinY : A →ₗ[A] B :=
      { toFun := qY
        map_add' := by intro a b; simp
        map_smul' := by
          intro a b
          change qY (a * b) = qY a • qY b
          simp [smul_eq_mul] }
    let : Module.Finite A B := Module.Finite.of_surjective qLinY hsurjY
    have hbaseY : ∀ (θ : EulerPoincareFunction A),
        θ (FGModuleCat.of A (nodeXComponent k)) =
          θ (FGModuleCat.of A B) := by
      intro θ
      let fY : A →ₗ[A] B := qLinY
      have hkerfY : LinearMap.ker fY = nodeXIdeal k := by
        ext a
        change qY a = 0 ↔ a ∈ nodeXIdeal k
        rw [← RingHom.mem_ker, hkerY]
      have eY : (A ⧸ nodeXIdeal k) ≃ₗ[A] B := by
        rw [← hkerfY]
        exact fY.quotKerEquivOfSurjective hsurjY
      exact hIso θ eY
    let : Module A B := Module.compHom B qX
    have hsurjX : Function.Surjective qX := by
      intro b
      refine ⟨sX b, ?_⟩
      simpa only [RingHom.comp_apply, RingHom.id_apply] using
        RingHom.congr_fun hqXsX b
    let qLinX : A →ₗ[A] B :=
      { toFun := qX
        map_add' := by intro a b; simp
        map_smul' := by
          intro a b
          change qX (a * b) = qX a • qX b
          simp [smul_eq_mul] }
    let : Module.Finite A B := Module.Finite.of_surjective qLinX hsurjX
    have hbaseX : ∀ (θ : EulerPoincareFunction A),
        θ (FGModuleCat.of A (nodeYComponent k)) =
          θ (FGModuleCat.of A B) := by
      intro θ
      let fX : A →ₗ[A] B := qLinX
      have hkerfX : LinearMap.ker fX = nodeYIdeal k := by
        ext a
        change qX a = 0 ↔ a ∈ nodeYIdeal k
        rw [← RingHom.mem_ker, hkerX]
      have eX : (A ⧸ nodeYIdeal k) ≃ₗ[A] B := by
        rw [← hkerfX]
        exact fX.quotKerEquivOfSurjective hsurjX
      exact hIso θ eX
    have hbranch :
        ∀ (q : A →+* B) (s : B →+* A) (hqs : q.comp s = RingHom.id B),
          letI : Module A B := Module.compHom B q
          ∀ [Module.Finite A B]
          (θ : EulerPoincareFunction A)
          {Q : Type u} [AddCommGroup Q] [Module A Q]
          [Module.Finite A Q] [Module B Q] [Module.Finite B Q]
          (hcompat : ∀ (a : A) (z : Q), q a • z = a • z),
          θ (FGModuleCat.of A Q) =
            θ (FGModuleCat.of A B) * (Module.finrank B Q : ℤ) := by
      intro q s hqs
      let : Module A B := Module.compHom B q
      intro _ θ Q _ _ _ _ _ hcompat
      have hsurj : Function.Surjective q := by
        intro b
        refine ⟨s b, ?_⟩
        simpa only [RingHom.comp_apply, RingHom.id_apply] using
          RingHom.congr_fun hqs b
      have hfiniteQuot : ∀ (p : B),
          let L : Submodule B B := B ∙ p
          let T : Type u := B ⧸ L
          letI : Module A T := Module.compHom T q
          Module.Finite A T := by
        intro p
        let L : Submodule B B := B ∙ p
        let T : Type u := B ⧸ L
        let : Module A T := Module.compHom T q
        let g : B →ₗ[A] T :=
          { toFun := L.mkQ
            map_add' := by intro z w; rfl
            map_smul' := by
              intro a z
              change L.mkQ (q a * z) = q a • L.mkQ z
              rfl }
        exact Module.Finite.of_surjective g L.mkQ_surjective
      obtain ⟨n, ι, fι, p, hp, e, ⟨eQ⟩⟩ :=
        Module.equiv_free_prod_directSum (R := B) (M := Q)
      let : Fintype ι := fι
      let : Module A (Fin n →₀ B) := Module.compHom (Fin n →₀ B) q
      let : ∀ i, Module A (B ⧸ B ∙ p i ^ e i) := fun i =>
        Module.compHom (B ⧸ B ∙ p i ^ e i) q
      let : ∀ i, Module.Finite A (B ⧸ B ∙ p i ^ e i) := fun i =>
        hfiniteQuot (p i ^ e i)
      let : Module A (DirectSum ι (fun i => B ⧸ B ∙ p i ^ e i)) :=
        @DirectSum.instModule A (inferInstance : Semiring A) ι
          (fun i => B ⧸ B ∙ p i ^ e i)
          (fun i => @AddCommGroup.toAddCommMonoid _ (inferInstance : AddCommGroup (B ⧸ B ∙ p i ^ e i)))
          (fun i => inferInstance)
      let : Module.Finite A (DirectSum ι (fun i => B ⧸ B ∙ p i ^ e i)) :=
        @Module.Finite.instDirectSum A ι (inferInstance : Semiring A)
          inferInstance (fun i => B ⧸ B ∙ p i ^ e i)
          (fun i => @AddCommGroup.toAddCommMonoid _
            (inferInstance : AddCommGroup (B ⧸ B ∙ p i ^ e i)))
          (fun i => inferInstance) (fun i => hfiniteQuot (p i ^ e i))
      let : Module A
          ((Fin n →₀ B) × DirectSum ι (fun i => B ⧸ B ∙ p i ^ e i)) :=
        @Prod.instModule A (Fin n →₀ B)
          (DirectSum ι (fun i => B ⧸ B ∙ p i ^ e i))
          (inferInstance : Semiring A)
          (inferInstance : AddCommMonoid (Fin n →₀ B))
          (inferInstance : AddCommMonoid
            (DirectSum ι (fun i => B ⧸ B ∙ p i ^ e i)))
          (inferInstance : Module A (Fin n →₀ B))
          (inferInstance : Module A
            (DirectSum ι (fun i => B ⧸ B ∙ p i ^ e i)))
      have blinearToA : ∀ {V W : Type u} [AddCommGroup V] [Module A V]
          [Module B V] [AddCommGroup W] [Module A W] [Module B W]
          (e : V ≃ₗ[B] W)
          (hV : ∀ (a : A) (v : V), q a • v = a • v)
          (hW : ∀ (a : A) (w : W), q a • w = a • w),
          V ≃ₗ[A] W := by
        intro V W _ _ _ _ _ _ e hV hW
        exact
          { toFun := e
            invFun := e.symm
            left_inv := e.left_inv
            right_inv := e.right_inv
            map_add' := e.map_add
            map_smul' := by
              intro a v
              calc
                e (a • v) = e (q a • v) := congrArg e (hV a v).symm
                _ = q a • e v := e.map_smul (q a) v
                _ = a • e v := hW a (e v) }
      have hPcompat : ∀ (a : A)
          (z : (Fin n →₀ B) × DirectSum ι (fun i => B ⧸ B ∙ p i ^ e i)),
          q a • z = a • z := by
        intro a z
        apply Prod.ext
        · rfl
        · ext i
          rfl
      let eA : Q ≃ₗ[A]
          (Fin n →₀ B) × DirectSum ι (fun i => B ⧸ B ∙ p i ^ e i) :=
        blinearToA eQ hcompat hPcompat
      let : Module.Finite A
          ((Fin n →₀ B) × DirectSum ι (fun i => B ⧸ B ∙ p i ^ e i)) :=
        Module.Finite.of_surjective eA.toLinearMap eA.surjective
      have htorsionDS :
          Module.IsTorsion B (DirectSum ι (fun i => B ⧸ B ∙ p i ^ e i)) := by
        intro z
        let r : B⁰ :=
          ⟨∏ i, p i ^ e i,
            by
              rw [mem_nonZeroDivisors_iff_ne_zero]
              exact Finset.prod_ne_zero_iff.mpr
                (fun i _ => pow_ne_zero _ (hp i).ne_zero)⟩
        refine ⟨r, ?_⟩
        ext i
        have hi : (p i ^ e i : B) • z i = 0 := by
          obtain ⟨b, hb⟩ :=
            Submodule.Quotient.mk_surjective (B ∙ p i ^ e i) (z i)
          rw [← hb]
          apply (Submodule.Quotient.mk_eq_zero (B ∙ p i ^ e i)).2
          exact (Submodule.mem_span_singleton).2
            ⟨b, by simp [smul_eq_mul, mul_comm]⟩
        change (∏ j, p j ^ e j) • z i = 0
        rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ i), mul_smul, hi,
          smul_zero]
      have hfree :
          θ (FGModuleCat.of A (Fin n →₀ B)) =
            (n : ℤ) * θ (FGModuleCat.of A B) := by
        let : Module A (DirectSum (Fin n) (fun _ => B)) :=
          @DirectSum.instModule A (inferInstance : Semiring A) (Fin n)
            (fun _ => B) (fun _ => inferInstance) (fun _ => inferInstance)
        let : Module.Finite A (DirectSum (Fin n) (fun _ => B)) :=
          @Module.Finite.instDirectSum A (Fin n) (inferInstance : Semiring A)
            inferInstance (fun _ => B) (fun _ => inferInstance)
            (fun _ => inferInstance) (fun _ => inferInstance)
        let eFree : (Fin n →₀ B) ≃ₗ[A] DirectSum (Fin n) (fun _ => B) :=
          blinearToA (finsuppLEquivDirectSum B B (Fin n))
            (by intro a z; rfl) (by
              intro a z
              ext i
              rfl)
        let eLift : ULift.{u, 0} (Fin n) ≃ Fin n := Equiv.ulift
        let : Fintype (ULift (Fin n)) :=
          Fintype.ofEquiv (Fin n) eLift.symm
        let : Module A (DirectSum (ULift (Fin n)) (fun _ => B)) :=
          @DirectSum.instModule A (inferInstance : Semiring A)
            (ULift (Fin n)) (fun _ => B) (fun _ => inferInstance)
            (fun _ => inferInstance)
        let : Module.Finite A (DirectSum (ULift (Fin n)) (fun _ => B)) :=
          @Module.Finite.instDirectSum A (ULift (Fin n))
            (inferInstance : Semiring A) inferInstance (fun _ => B)
            (fun _ => inferInstance) (fun _ => inferInstance)
            (fun _ => inferInstance)
        let eLiftDS : DirectSum (ULift (Fin n)) (fun _ => B) ≃ₗ[A]
            DirectSum (Fin n) (fun _ => B) :=
          DirectSum.lequivCongrLeft A eLift
        have hLift := hDS θ (ULift (Fin n)) (fun _ => B)
        calc
          θ (FGModuleCat.of A (Fin n →₀ B)) =
              θ (FGModuleCat.of A (DirectSum (Fin n) (fun _ => B))) :=
            hIso θ eFree
          _ = θ (FGModuleCat.of A (DirectSum (ULift (Fin n)) (fun _ => B))) := by
            exact (hIso θ eLiftDS).symm
          _ = ∑ i : ULift (Fin n), θ (FGModuleCat.of A B) := hLift
          _ = ∑ i : Fin n, θ (FGModuleCat.of A B) := by
            exact eLift.sum_comp (fun _ => θ (FGModuleCat.of A B))
          _ = (n : ℤ) * θ (FGModuleCat.of A B) := by
            rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ,
              Fintype.card_fin]
      have hDSval := hDS θ ι (fun i => B ⧸ B ∙ p i ^ e i)
      have hDSzero :
          ∑ i : ι, θ (FGModuleCat.of A (B ⧸ B ∙ p i ^ e i)) = 0 := by
        apply Finset.sum_eq_zero
        intro i hi
        exact hcyclicFor θ q hsurj (p i ^ e i)
          (pow_ne_zero _ (hp i).ne_zero)
      have hPval :
          θ (FGModuleCat.of A
              ((Fin n →₀ B) × DirectSum ι (fun i => B ⧸ B ∙ p i ^ e i))) =
            (n : ℤ) * θ (FGModuleCat.of A B) := by
        calc
          θ (FGModuleCat.of A
              ((Fin n →₀ B) × DirectSum ι (fun i => B ⧸ B ∙ p i ^ e i))) =
              θ (FGModuleCat.of A (Fin n →₀ B)) +
                θ (FGModuleCat.of A (DirectSum ι
                  (fun i => B ⧸ B ∙ p i ^ e i))) := by
            exact hprod θ
          _ = (n : ℤ) * θ (FGModuleCat.of A B) +
                ∑ i : ι, θ (FGModuleCat.of A (B ⧸ B ∙ p i ^ e i)) := by
            rw [hfree, hDSval]
          _ = (n : ℤ) * θ (FGModuleCat.of A B) := by rw [hDSzero, add_zero]
      have hfinrankP :
          Module.finrank B
              ((Fin n →₀ B) × DirectSum ι (fun i => B ⧸ B ∙ p i ^ e i)) = n := by
        let P := (Fin n →₀ B) × DirectSum ι (fun i => B ⧸ B ∙ p i ^ e i)
        let : AddCommGroup P := inferInstance
        let : Module B P := inferInstance
        let f : P →ₗ[B] (Fin n →₀ B) :=
          LinearMap.fst B (Fin n →₀ B) (DirectSum ι (fun i => B ⧸ B ∙ p i ^ e i))
        have hf : Function.Surjective f := by
          intro z
          exact ⟨(z, 0), rfl⟩
        have hkerT : LinearMap.ker f ≤ Submodule.torsion B P := by
          intro z hz
          rw [Submodule.mem_torsion_iff]
          obtain ⟨b, hb⟩ := htorsionDS (x := z.2)
          refine ⟨b, ?_⟩
          apply Prod.ext
          · have hz1 : z.1 = 0 := by
              change z.1 = 0 at hz
              exact hz
            change (b : B) • z.1 = 0
            simp [hz1]
          · exact hb
        have hquot :
            Module.rank B (P ⧸ LinearMap.ker f) = Module.rank B P :=
          rank_quotient_eq_of_le_torsion (R := B) (M := P) hkerT
        let eproj : (P ⧸ LinearMap.ker f) ≃ₗ[B] (Fin n →₀ B) :=
          f.quotKerEquivOfSurjective hf
        change Module.finrank B P = n
        calc
          Module.finrank B P =
              Module.finrank B (P ⧸ LinearMap.ker f) :=
            (congrArg Cardinal.toNat hquot).symm
          _ = Module.finrank B (Fin n →₀ B) := eproj.finrank_eq
          _ = n := by simp
      have hfinrankQ : Module.finrank B Q = n := by
        rw [eQ.finrank_eq, hfinrankP]
      calc
        θ (FGModuleCat.of A Q) =
            θ (FGModuleCat.of A
              ((Fin n →₀ B) × DirectSum ι (fun i => B ⧸ B ∙ p i ^ e i))) :=
          hIso θ eA
        _ = (n : ℤ) * θ (FGModuleCat.of A B) := hPval
        _ = θ (FGModuleCat.of A B) *
            (Module.finrank B Q : ℤ) := by
          rw [hfinrankQ]
          ring
    have hbranchY :
        ∀ (θ : EulerPoincareFunction A)
          {Q : Type u} [AddCommGroup Q] [Module A Q]
          [Module.Finite A Q] [Module B Q] [Module.Finite B Q]
          (hcompat : ∀ (a : A) (z : Q), qY a • z = a • z),
          θ (FGModuleCat.of A Q) =
            θ (FGModuleCat.of A (nodeXComponent k)) *
              (Module.finrank B Q : ℤ) := by
      intro θ Q _ _ _ _ _ hcompat
      let : Module A B := Module.compHom B qY
      let : Module.Finite A B := Module.Finite.of_surjective qLinY hsurjY
      rw [hbaseY θ]
      exact hbranch qY sY hqYsY θ hcompat
    have hbranchX :
        ∀ (θ : EulerPoincareFunction A)
          {Q : Type u} [AddCommGroup Q] [Module A Q]
          [Module.Finite A Q] [Module B Q] [Module.Finite B Q]
          (hcompat : ∀ (a : A) (z : Q), qX a • z = a • z),
          θ (FGModuleCat.of A Q) =
            θ (FGModuleCat.of A (nodeYComponent k)) *
              (Module.finrank B Q : ℤ) := by
      intro θ Q _ _ _ _ _ hcompat
      let : Module A B := Module.compHom B qX
      let : Module.Finite A B := Module.Finite.of_surjective qLinX hsurjX
      rw [hbaseX θ]
      exact hbranch qX sX hqXsX θ hcompat
    have hformula :
        ∀ (θ : EulerPoincareFunction A)
          {V : Type u} [AddCommGroup V] [Module A V] [Module.Finite A V]
          (m : V →ₗ[A] V)
          (hm : ∀ z : V, m z = x • z),
          letI : Module B (LinearMap.ker m) :=
            Module.compHom (LinearMap.ker m) sY
          letI : Module B (LinearMap.range m) :=
            Module.compHom (LinearMap.range m) sX
          θ (FGModuleCat.of A V) =
          θ (FGModuleCat.of A (nodeXComponent k)) *
                (Module.finrank B (LinearMap.ker m) : ℤ) +
          θ (FGModuleCat.of A (nodeYComponent k)) *
                (Module.finrank B (LinearMap.range m) : ℤ) := by
      intro θ V _ _ _ m hm
      let : Module B (LinearMap.ker m) := Module.compHom (LinearMap.ker m) sY
      let : Module B (LinearMap.range m) := Module.compHom (LinearMap.range m) sX
      exact euler_formula_of_multiplication_sequence
        A B (nodeXComponent k) (nodeYComponent k) V θ qY sY qX sX
        hbranchY hbranchX m
        (by
          intro a z
          have hz0 : x • (z : V) = 0 := by
            have hzK : m (z : V) = 0 := z.property
            rw [hm] at hzK
            exact hzK
          exact hcompatY_of_annihilated (V := V) a (z : V) hz0)
        (by
          intro a z
          have hyz := hrange_annihilated m hm z
          exact hcompatX_of_annihilated (V := V) a (z : V) hyz)
    have hparamX :
        φ (FGModuleCat.of A (nodeXComponent k)) =
          ψ (FGModuleCat.of A (nodeXComponent k)) := by
      simpa [nodeEulerParameters] using congrArg Prod.fst h
    have hparamY :
        φ (FGModuleCat.of A (nodeYComponent k)) =
          ψ (FGModuleCat.of A (nodeYComponent k)) := by
      simpa [nodeEulerParameters] using congrArg Prod.snd h
    have hfun : φ.toFun = ψ.toFun := by
      funext M
      let m : (M : Type u) →ₗ[A] (M : Type u) :=
        { toFun := fun z => x • z
          map_add' := by intro z w; simp
          map_smul' := by
            intro a z
            simp only [smul_smul, RingHom.id_apply, mul_comm] }
      let : Module B (LinearMap.ker m) := Module.compHom (LinearMap.ker m) sY
      let : Module B (LinearMap.range m) := Module.compHom (LinearMap.range m) sX
      have hφM := hformula φ (V := (M : Type u)) m (by intro z; rfl)
      have hψM := hformula ψ (V := (M : Type u)) m (by intro z; rfl)
      calc
        φ M = φ (FGModuleCat.of A (M : Type u)) := by rfl
        _ = φ (FGModuleCat.of A (nodeXComponent k)) *
              (Module.finrank B (LinearMap.ker m) : ℤ) +
            φ (FGModuleCat.of A (nodeYComponent k)) *
              (Module.finrank B (LinearMap.range m) : ℤ) := hφM
        _ = ψ (FGModuleCat.of A (nodeXComponent k)) *
              (Module.finrank B (LinearMap.ker m) : ℤ) +
            ψ (FGModuleCat.of A (nodeYComponent k)) *
              (Module.finrank B (LinearMap.range m) : ℤ) := by
          rw [hparamX, hparamY]
        _ = ψ (FGModuleCat.of A (M : Type u)) := hψM.symm
        _ = ψ M := by rfl
    exact eulerPoincareFunction_ext hfun

private theorem eulerPoincareFunction_node_surjective
    (k : Type u) [Field k] [IsAlgClosed k] :
    Function.Surjective (nodeEulerParameters (k := k)) := by
  classical
  let A := nodeRing k
  let B := Polynomial k
  let d := nodeMultiplicationData_exists k
  let qY : A →+* B := d.qY
  let qX : A →+* B := d.qX
  let sY : B →+* A := d.sY
  let sX : B →+* A := d.sX
  let x : A := d.x
  let y : A := d.y
  have hkerY : RingHom.ker qY = nodeXIdeal k := by
    change RingHom.ker d.qY = nodeXIdeal k
    exact d.hkerY
  have hqYsY : qY.comp sY = RingHom.id B := by
    change d.qY.comp d.sY = RingHom.id (Polynomial k)
    exact d.hqYsY
  have hkerX : RingHom.ker qX = nodeYIdeal k := by
    change RingHom.ker d.qX = nodeYIdeal k
    exact d.hkerX
  have hqXsX : qX.comp sX = RingHom.id B := by
    change d.qX.comp d.sX = RingHom.id (Polynomial k)
    exact d.hqXsX
  have hxy : x * y = 0 := by
    change d.x * d.y = 0
    exact d.hxy
  have hyx : y * x = 0 := by
    change d.y * d.x = 0
    exact d.hyx
  have hIspan : nodeXIdeal k = Ideal.span {x} := by
    change nodeXIdeal k = Ideal.span ({d.x} : Set (nodeRing k))
    exact d.hIspan
  have hJspan : nodeYIdeal k = Ideal.span {y} := by
    change nodeYIdeal k = Ideal.span ({d.y} : Set (nodeRing k))
    exact d.hJspan
  let b : B⁰ := ⟨Polynomial.X, by
    rw [mem_nonZeroDivisors_iff_ne_zero]
    exact Polynomial.X_ne_zero⟩
  have hsYb : sY (b : B) = y := by
    simpa [b] using d.hsY_X
  have hsXb : sX (b : B) = x := by
    simpa [b] using d.hsX_X
  have hfinite :
      ∀ (M : Type u) [AddCommGroup M] [Module A M] [Module.Finite A M]
        (a : A) (s : B →+* A) (q : A →+* B),
        RingHom.ker q = Ideal.span {a} → q.comp s = RingHom.id B →
          let m : M →ₗ[A] M :=
            { toFun := fun z => a • z
              map_add' := by intro z w; simp
              map_smul' := by
                intro c z
                simp only [smul_smul, RingHom.id_apply, mul_comm] }
          let Q : Type u := M ⧸ LinearMap.range m
          letI : Module B Q := Module.compHom Q s
          Module.Finite B Q := by
    intro M _ _ _ a s q hker hqs
    let m : M →ₗ[A] M :=
      { toFun := fun z => a • z
        map_add' := by intro z w; simp
        map_smul' := by
          intro c z
          simp only [smul_smul, RingHom.id_apply, mul_comm] }
    let Q : Type u := M ⧸ LinearMap.range m
    let : Module B Q := Module.compHom Q s
    have hdiff (b : A) : b - s (q b) ∈ Ideal.span {a} := by
      rw [← hker, RingHom.mem_ker]
      have h := RingHom.congr_fun hqs (q b)
      rw [map_sub]
      have hs : q (s (q b)) = q b := by
        simpa only [RingHom.comp_apply, RingHom.id_apply] using h
      rw [hs]
      simp
    have hcompat (b : A) (z : Q) : q b • z = b • z := by
      change s (q b) • z = b • z
      obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp (hdiff b)
      have hz : (b - s (q b)) • z = 0 := by
        obtain ⟨z, rfl⟩ :=
          Submodule.Quotient.mk_surjective (LinearMap.range m) z
        rw [← Submodule.Quotient.mk_smul]
        apply (Submodule.Quotient.mk_eq_zero (LinearMap.range m)).mpr
        rw [← hc]
        exact ⟨c • z, by simp [m, smul_smul, mul_comm]⟩
      exact (sub_eq_zero.mp (by simpa only [sub_smul] using hz)).symm
    simpa [m, Q] using (finite_of_scalar_compat q hcompat)
  intro z
  obtain ⟨φ, hφ⟩ := eulerPoincareFunction_exists_from_multiplication_data
    A B (nodeXIdeal k) (nodeYIdeal k) x y sY sX b qY qX hxy hyx
    hkerY hqYsY hkerX hqXsX hIspan hJspan hsYb hsXb hfinite z
  refine ⟨φ, ?_⟩
  simpa [nodeEulerParameters, nodeXComponent, nodeYComponent, A] using hφ

/-- For an algebraically closed field, the two component values classify all
Euler–Poincaré functions on the nodal ring. -/
theorem eulerPoincareFunction_node_classification
    (k : Type u) [Field k] [IsAlgClosed k] :
    Function.Bijective (nodeEulerParameters (k := k)) :=
  ⟨eulerPoincareFunction_node_injective k,
    eulerPoincareFunction_node_surjective k⟩

/-! ## Exercise 4: kernels of locally finite graded maps -/

/-- The kernel of a degree-preserving map between locally finite graded modules
admits the induced grading and remains locally finite. -/
theorem kernel_of_graded_map_is_locally_finite
    {A M N : Type u} {ι : Type v}
    [CommRing A] [IsNoetherianRing A]
    [AddCommGroup M] [AddCommGroup N]
    [Module A M] [Module A N] [DecidableEq ι]
    (G : GradedModuleData A M ι) (H : GradedModuleData A N ι)
    (hG : G.LocallyFinite) (_hH : H.LocallyFinite)
    (f : GradedLinearMap G H) :
    ∃ K : GradedModuleData A (LinearMap.ker f.toLinearMap) ι,
      (∀ n : ι, K.component n = f.kernelComponent n) ∧ K.LocallyFinite := by
  classical
  let p : Submodule A M := LinearMap.ker f.toLinearMap
  let : DirectSum.Decomposition (fun n => G.component n) := G.decomposition
  let : DirectSum.Decomposition (fun n => H.component n) := H.decomposition
  have hmap_component : ∀ (x : M) (n : ι),
      f.toLinearMap (DirectSum.decompose (fun n => G.component n) x n : M) =
        (DirectSum.decompose (fun n => H.component n)
          (f.toLinearMap x) n : N) := by
    intro x
    refine DirectSum.Decomposition.inductionOn
      (ℳ := fun n => G.component n)
      (motive := fun x => ∀ n : ι,
        f.toLinearMap (DirectSum.decompose (fun n => G.component n) x n : M) =
          (DirectSum.decompose (fun n => H.component n)
            (f.toLinearMap x) n : N)) ?_ ?_ ?_ x
    · intro n
      simp
    · intro i m n
      have hm : (m : M) ∈ G.component i := m.property
      have hfm : f.toLinearMap (m : M) ∈ H.component i :=
        f.map_component' i hm
      by_cases hin : i = n
      · subst n
        rw [DirectSum.decompose_of_mem_same _ hm,
          DirectSum.decompose_of_mem_same _ hfm]
      · rw [DirectSum.decompose_of_mem_ne _ hm hin,
          DirectSum.decompose_of_mem_ne _ hfm hin]
        simp
    · intro x y hx hy n
      have hGadd :
          (DirectSum.decompose (fun n => G.component n) (x + y) n : M) =
            (DirectSum.decompose (fun n => G.component n) x n : M) +
              (DirectSum.decompose (fun n => G.component n) y n : M) := by
        rw [DirectSum.decompose_add]
        simp
      have hHadd :
          (DirectSum.decompose (fun n => H.component n)
            (f.toLinearMap x + f.toLinearMap y) n : N) =
            (DirectSum.decompose (fun n => H.component n) (f.toLinearMap x) n : N) +
              (DirectSum.decompose (fun n => H.component n) (f.toLinearMap y) n : N) := by
        rw [DirectSum.decompose_add]
        simp
      calc
        f.toLinearMap
            (DirectSum.decompose (fun n => G.component n) (x + y) n : M) =
            f.toLinearMap
              ((DirectSum.decompose (fun n => G.component n) x n : M) +
                (DirectSum.decompose (fun n => G.component n) y n : M)) := by
          rw [hGadd]
        _ = f.toLinearMap (DirectSum.decompose (fun n => G.component n) x n : M) +
            f.toLinearMap (DirectSum.decompose (fun n => G.component n) y n : M) :=
          map_add _ _ _
        _ = (DirectSum.decompose (fun n => H.component n) (f.toLinearMap x) n : N) +
            (DirectSum.decompose (fun n => H.component n) (f.toLinearMap y) n : N) := by
          rw [hx n, hy n]
        _ = (DirectSum.decompose (fun n => H.component n)
              (f.toLinearMap x + f.toLinearMap y) n : N) := hHadd.symm
        _ = (DirectSum.decompose (fun n => H.component n)
              (f.toLinearMap (x + y)) n : N) := by rw [f.toLinearMap.map_add]
  have hcomponent : ∀ (x : M), x ∈ p → ∀ n : ι,
      (DirectSum.decompose (fun n => G.component n) x n : M) ∈ p := by
    intro x hx n
    change f.toLinearMap x = 0 at hx
    change f.toLinearMap
      (DirectSum.decompose (fun n => G.component n) x n : M) = 0
    simpa [hx] using hmap_component x n
  let Kc : ι → Submodule A p := fun n => f.kernelComponent n
  let e : Submodule A p ≃o Set.Iic p := p.mapIic
  have hmapK (n : ι) :
      (e (Kc n) : Submodule A M) = G.component n ⊓ p := by
    change ((G.component n).comap p.subtype).map p.subtype = _
    rw [Submodule.map_comap_subtype]
    exact inf_comm _ _
  have hKInd : iSupIndep Kc := by
    have hGInd : iSupIndep (fun n => G.component n) :=
      G.decomposition.isInternal.submodule_iSupIndep
    have hInfInd : iSupIndep (fun n => G.component n ⊓ p) :=
      hGInd.mono (fun n => inf_le_left)
    have he : (e ∘ Kc) =
        (fun n => ⟨G.component n ⊓ p,
          (inf_le_right : G.component n ⊓ p ≤ p)⟩ : ι → Set.Iic p) := by
      funext n
      apply Subtype.ext
      exact hmapK n
    rw [← iSupIndep_map_orderIso_iff e, he]
    exact iSupIndep.of_coe_Iic_comp hInfInd
  have hKTop : iSup Kc = ⊤ := by
    apply top_unique
    intro x _
    have hsum :
        (∑ n ∈ (DirectSum.decompose (fun n => G.component n) (x : M)).support,
          (⟨(DirectSum.decompose (fun n => G.component n) (x : M) n : M),
            hcomponent (x : M) x.property n⟩ : p)) = x := by
      apply Subtype.ext
      change p.subtype
          (∑ n ∈ (DirectSum.decompose (fun n => G.component n) (x : M)).support,
            (⟨(DirectSum.decompose (fun n => G.component n) (x : M) n : M),
              hcomponent (x : M) x.property n⟩ : p)) = (x : M)
      rw [map_sum]
      exact DirectSum.sum_support_decompose (fun n => G.component n) (x : M)
    rw [← hsum]
    exact sum_mem fun n hn =>
      (le_iSup (fun n => Kc n) n) (by
        change (DirectSum.decompose (fun n => G.component n) (x : M) n : M) ∈
          G.component n
        exact (DirectSum.decompose (fun n => G.component n) (x : M) n).property)
  have hK : DirectSum.IsInternal Kc :=
    DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top hKInd hKTop
  let K : GradedModuleData A p ι :=
    { component := Kc
      decomposition := DirectSum.IsInternal.chooseDecomposition Kc hK }
  refine ⟨K, ?_, ?_⟩
  · intro n
    rfl
  · intro n
    let : Module.Finite A (G.component n) := hG n
    let q : Kc n →ₗ[A] G.component n :=
      { toFun := fun x => ⟨(x : p).1, x.2⟩
        map_add' := by intro x y; rfl
        map_smul' := by intro a x; rfl }
    apply Module.Finite.of_injective q
    intro x y hxy
    apply Subtype.ext
    apply Subtype.ext
    simpa [q] using congrArg Subtype.val hxy

/-! ## Exercise 5: a weighted polynomial ring -/

/-- The weights `2` and `3` on the two polynomial variables. -/
def twoThreeWeights : Fin 2 → ℕ := fun i => if i = 0 then 2 else 3

/-- The canonical weighted decomposition of `k[x,y]` with weights `2` and `3`. -/
def weightedPolynomialGradedModule (k : Type u) [Field k] :
    GradedModuleData k (MvPolynomial (Fin 2) k) ℕ :=
  { component := MvPolynomial.weightedHomogeneousSubmodule k twoThreeWeights
    decomposition := MvPolynomial.weightedDecomposition k twoThreeWeights }

/-- The vector-space dimension of a homogeneous component. -/
def fieldDimensionHilbertFunction
    {k M : Type u} {ι : Type v} [Field k]
    [AddCommGroup M] [Module k M] [DecidableEq ι]
    (G : GradedModuleData k M ι) (n : ι) : ℕ :=
  Module.finrank k (G.component n)

def weightedPolynomialHilbertFunction (k : Type u) [Field k] (n : ℕ) : ℕ :=
  fieldDimensionHilbertFunction (weightedPolynomialGradedModule k) n

/-- The number of solutions of `2a + 3b = n`. -/
def weightedTwoThreeFormula (n : ℕ) : ℕ :=
  if n % 6 = 1 then n / 6 else n / 6 + 1

theorem weighted_polynomial_grading_locally_finite (k : Type u) [Field k] :
    (weightedPolynomialGradedModule k).LocallyFinite := by
  exact fun n => Module.Finite.of_fg
    (MvPolynomial.weightedHomogeneousSubmodule_fg k twoThreeWeights
      (by intro x; fin_cases x <;> simp [twoThreeWeights]) n)

/-- The weighted polynomial Hilbert function is the solution-counting formula. -/
theorem weighted_polynomial_hilbert_function (k : Type u) [Field k] (n : ℕ) :
    weightedPolynomialHilbertFunction k n = weightedTwoThreeFormula n := by
  classical
  change Module.finrank k
      (MvPolynomial.weightedHomogeneousSubmodule k twoThreeWeights n) =
    weightedTwoThreeFormula n
  let S : Set (Fin 2 →₀ ℕ) := {d | Finsupp.weight twoThreeWeights d = n}
  have : Finite S :=
    (Finsupp.finite_of_nat_weight_eq twoThreeWeights
      (by intro x; fin_cases x <;> simp [twoThreeWeights]) n).to_subtype
  let := Fintype.ofFinite S
  have hsub :
      MvPolynomial.weightedHomogeneousSubmodule k twoThreeWeights n =
        MvPolynomial.restrictSupport k S := by
    rw [MvPolynomial.weightedHomogeneousSubmodule_eq_finsupp_supported]
    rfl
  have hdim : Module.finrank k
      (MvPolynomial.weightedHomogeneousSubmodule k twoThreeWeights n) =
      Module.finrank k (MvPolynomial.restrictSupport k S) :=
    congrArg (fun T : Submodule k (MvPolynomial (Fin 2) k) => Module.finrank k T) hsub
  let e : (Fin 2 →₀ ℕ) ≃ (ℕ × ℕ) :=
    Finsupp.equivFunOnFinite.trans (finTwoArrowEquiv ℕ)
  let T : Set (ℕ × ℕ) := {p | 2 * p.1 + 3 * p.2 = n}
  have he : ∀ d, d ∈ S ↔ e d ∈ T := by
    intro d
    simp [S, T, e, Finsupp.weight_eq_sum, twoThreeWeights, finTwoArrowEquiv]
    omega
  let eT : S ≃ T := e.subtypeEquiv he
  let : Fintype T := Fintype.ofEquiv S eT
  have hcardST : Fintype.card S = Fintype.card T := Fintype.card_congr eT
  calc
    Module.finrank k
        (MvPolynomial.weightedHomogeneousSubmodule k twoThreeWeights n) =
        Module.finrank k (MvPolynomial.restrictSupport k S) := hdim
    _ = Fintype.card S :=
      Module.finrank_eq_card_basis (MvPolynomial.basisRestrictSupport k S)
    _ = Fintype.card T := hcardST
    _ = weightedTwoThreeFormula n := by
      let L := weightedTwoThreeFormula n
      have hcount : Fintype.card T = L := by
        let eFin : T ≃ Fin L :=
          { toFun := fun x =>
              ⟨x.1.2 / 2, by
                have hx := x.2
                dsimp [T] at hx
                by_cases hs : n % 6 = 1
                · have hL : L = n / 6 := by simp [L, weightedTwoThreeFormula, hs]
                  rw [hL]
                  omega
                · have hL : L = n / 6 + 1 := by simp [L, weightedTwoThreeFormula, hs]
                  rw [hL]
                  omega⟩
            invFun := fun j =>
              ⟨( (n - 3 * (2 * (j : ℕ) + n % 2)) / 2,
                  2 * (j : ℕ) + n % 2), by
                dsimp [T]
                have hp : n % 2 < 2 := Nat.mod_lt _ (by omega)
                by_cases hs : n % 6 = 1
                · have hL : L = n / 6 := by simp [L, weightedTwoThreeFormula, hs]
                  have hj : (j : ℕ) < n / 6 := by simpa [hL] using j.isLt
                  omega
                · have hL : L = n / 6 + 1 := by simp [L, weightedTwoThreeFormula, hs]
                  have hj : (j : ℕ) < n / 6 + 1 := by simpa [hL] using j.isLt
                  omega⟩
            left_inv := by
              intro x
              have hx := x.2
              dsimp [T] at hx
              apply Subtype.ext
              apply Prod.ext
              · have hp : n % 2 < 2 := Nat.mod_lt _ (by omega)
                change (n - 3 * (2 * (x.1.2 / 2) + n % 2)) / 2 = x.1.1
                omega
              · have hp : n % 2 < 2 := Nat.mod_lt _ (by omega)
                change 2 * (x.1.2 / 2) + n % 2 = x.1.2
                omega
            right_inv := by
              intro j
              apply Fin.ext
              have hp : n % 2 < 2 := Nat.mod_lt _ (by omega)
              change (2 * (j : ℕ) + n % 2) / 2 = j
              omega }
        simpa using Fintype.card_congr eFin
      simpa [L] using hcount

/-- The periodic weighted Hilbert function does not eventually agree with a
numerical polynomial. -/
theorem weighted_polynomial_no_hilbert_polynomial (k : Type u) [Field k] :
    ¬ HasHilbertPolynomialOnNat (weightedPolynomialHilbertFunction k) := by
  rintro ⟨P, _hP, hEq⟩
  rcases Filter.eventually_atTop.1 hEq with ⟨N, hN⟩
  let L : Polynomial ℚ := Polynomial.C (1 / 6) * Polynomial.X + Polynomial.C 1
  let f : ℕ → ℚ := fun m => (6 * (m + N) : ℕ)
  have hf : Function.Injective f := by
    intro a b hab
    dsimp [f] at hab
    have hab' : 6 * (a + N) = 6 * (b + N) := by exact_mod_cast hab
    omega
  have hmem : ∀ m : ℕ, P.eval (f m) = L.eval (f m) := by
    intro m
    have hm := hN (6 * (m + N)) (by omega)
    rw [weighted_polynomial_hilbert_function] at hm
    have hlin :
        (weightedTwoThreeFormula (6 * (m + N)) : ℚ) =
          L.eval (f m) := by
      simp [weightedTwoThreeFormula, L, f, Polynomial.eval_add,
        Polynomial.eval_mul]
    exact hm.symm.trans hlin
  have hInf : {x : ℚ | P.eval x = L.eval x}.Infinite := by
    apply Set.infinite_of_injective_forall_mem hf
    intro m
    exact hmem m
  have hP : P = L := Polynomial.eq_of_infinite_eval_eq P L hInf
  have hm := hN (6 * N + 1) (by omega)
  rw [weighted_polynomial_hilbert_function, hP] at hm
  have hmod : (6 * N + 1) % 6 = 1 := by omega
  simp [weightedTwoThreeFormula, hmod] at hm
  have hdiv : (6 * N + 1) / 6 = N := by omega
  rw [hdiv] at hm
  norm_num [L, Polynomial.eval_add, Polynomial.eval_mul] at hm
  linarith

private theorem graded_quotient_data
    {A M N P : Type u} [CommRing A] [AddCommGroup M] [Module A M]
    [AddCommGroup N] [Module A N]
    [SetLike P M] [AddSubmonoidClass P M]
    (G : GradedModuleData A M ℕ)
    [hdec : DirectSum.Decomposition (fun n : ℕ => G.component n)]
    (p : P) (q : M →ₗ[A] N)
    (hq : ∀ x : M, q x = 0 ↔ x ∈ p) (hsurj : Function.Surjective q)
    (hp : DirectSum.SetLike.IsHomogeneous (fun n : ℕ => G.component n) p) :
    ∃ Gq : GradedModuleData A N ℕ,
      ∀ n : ℕ, Gq.component n = (G.component n).map q := by
  classical
  let C : ℕ → Submodule A M := fun n => G.component n
  let Q : ℕ → Submodule A N := fun n => (C n).map q
  let : DirectSum.Decomposition C := hdec
  let r : ∀ n : ℕ, C n →ₗ[A] Q n := fun n =>
    { toFun := fun x => ⟨q x, ⟨x, x.property, rfl⟩⟩
      map_add' := by
        intro x y
        apply Subtype.ext
        exact q.map_add (x : M) (y : M)
      map_smul' := by
        intro a x
        apply Subtype.ext
        exact q.map_smul a (x : M) }
  have hr : ∀ n : ℕ, Function.Surjective (r n) := by
    intro n y
    rcases y.property with ⟨x, hx, hxy⟩
    refine ⟨⟨x, hx⟩, ?_⟩
    apply Subtype.ext
    exact hxy
  let L : DirectSum ℕ (fun n => C n) →ₗ[A] DirectSum ℕ (fun n => Q n) :=
    DirectSum.lmap r
  have hLsurj : Function.Surjective L :=
    (DirectSum.lmap_surjective r).2 hr
  let e : M ≃ₗ[A] DirectSum ℕ (fun n => C n) :=
    DirectSum.decomposeLinearEquiv C
  let d : M →ₗ[A] DirectSum ℕ (fun n => Q n) := L.comp e.toLinearMap
  let coe : DirectSum ℕ (fun n => Q n) →ₗ[A] N :=
    DirectSum.coeLinearMap Q
  have hcoe_d : coe.comp d = q := by
    apply DirectSum.decompose_lhom_ext C
    intro n
    ext x
    simp [coe, d, L, e, r, C]
  have hcoe_surj : Function.Surjective coe := by
    intro y
    rcases hsurj y with ⟨x, hx⟩
    refine ⟨d x, ?_⟩
    simpa [LinearMap.comp_apply] using
      (DFunLike.congr_fun hcoe_d x).trans hx
  have hcoe_inj : Function.Injective coe := by
    intro z z' hzz'
    have hzero : coe (z - z') = 0 := by
      rw [map_sub, hzz', sub_self]
    rcases hLsurj (z - z') with ⟨y, hy⟩
    let x : M := e.symm y
    have hqx : q x = 0 := by
      rw [← DFunLike.congr_fun hcoe_d x]
      change coe (L (e x)) = 0
      rw [show e x = y by simp [x], hy, hzero]
    have hpx : x ∈ p := (hq x).mp hqx
    have hdx : d x = 0 := by
      apply DirectSum.ext
      intro n
      apply Subtype.ext
      change q (e x n : M) = 0
      apply (hq _).mpr
      change (DirectSum.decompose C x n : M) ∈ p
      exact hp n hpx
    have hLy : L y = 0 := by
      simpa [d, x] using hdx
    have hdiff : z - z' = 0 := by
      rw [← hy, hLy]
    exact sub_eq_zero.mp hdiff
  let eQ : DirectSum ℕ (fun n => Q n) ≃ₗ[A] N := LinearEquiv.ofBijective coe
    ⟨hcoe_inj, hcoe_surj⟩
  have hleft : coe.comp eQ.symm.toLinearMap = LinearMap.id := by
    apply LinearMap.ext
    intro y
    change eQ (eQ.symm y) = y
    exact eQ.apply_symm_apply y
  have hright : eQ.symm.toLinearMap.comp coe = LinearMap.id := by
    apply LinearMap.ext
    intro z
    change eQ.symm (coe z) = z
    exact eQ.symm_apply_apply z
  let dec : DirectSum.Decomposition Q :=
    DirectSum.Decomposition.ofLinearMap Q eQ.symm.toLinearMap hleft hright
  let Gq : GradedModuleData A N ℕ :=
    { component := Q
      decomposition := dec }
  refine ⟨Gq, ?_⟩
  intro n
  rfl

/-! ## Exercise 6: a weighted quotient -/

/-- The homogeneous ideal `(x², xy)` in the weighted polynomial ring. -/
def truncatedPolynomialIdeal (k : Type u) [Field k] :
    Ideal (MvPolynomial (Fin 2) k) :=
  Ideal.span {MvPolynomial.X 0 ^ 2, MvPolynomial.X 0 * MvPolynomial.X 1}

/-- The quotient `k[x,y]/(x²,xy)` with `deg x = 2` and `deg y = 3`. -/
abbrev truncatedPolynomialRing (k : Type u) [Field k] : Type u :=
  MvPolynomial (Fin 2) k ⧸ truncatedPolynomialIdeal k

/-- The computed Hilbert function of the weighted quotient. -/
def truncatedPolynomialHilbertFunction (n : ℕ) : ℕ :=
  if n = 0 ∨ n = 2 ∨ (0 < n ∧ 3 ∣ n) then 1 else 0

/-- The quotient has the grading induced from the weighted homogeneous pieces,
and its Hilbert function is the displayed formula. -/
theorem truncated_polynomial_graded_quotient_exists (k : Type u) [Field k] :
    ∃ G : GradedModuleData k (truncatedPolynomialRing k) ℕ,
      G.LocallyFinite ∧
        (∀ n : ℕ,
          G.component n =
            (MvPolynomial.weightedHomogeneousSubmodule k twoThreeWeights n).map
              (Ideal.Quotient.mkₐ k (truncatedPolynomialIdeal k)).toLinearMap) ∧
        ∀ n : ℕ,
          fieldDimensionHilbertFunction G n = truncatedPolynomialHilbertFunction n := by
  classical
  let : GradedAlgebra
      (MvPolynomial.weightedHomogeneousSubmodule k twoThreeWeights) :=
    MvPolynomial.weightedGradedAlgebra k twoThreeWeights
  have hI : (truncatedPolynomialIdeal k).IsHomogeneous
      (MvPolynomial.weightedHomogeneousSubmodule k twoThreeWeights) := by
    apply Ideal.homogeneous_span
    intro x hx
    rcases hx with rfl | rfl
    · refine ⟨4, ?_⟩
      simpa [twoThreeWeights] using
        (MvPolynomial.IsWeightedHomogeneous.pow
          (MvPolynomial.isWeightedHomogeneous_X (R := k) twoThreeWeights 0) 2)
    · refine ⟨5, ?_⟩
      simpa [twoThreeWeights] using
        (MvPolynomial.IsWeightedHomogeneous.mul
          (MvPolynomial.isWeightedHomogeneous_X (R := k) twoThreeWeights 0)
          (MvPolynomial.isWeightedHomogeneous_X (R := k) twoThreeWeights 1))
  let q : MvPolynomial (Fin 2) k →ₗ[k] truncatedPolynomialRing k :=
    (Ideal.Quotient.mkₐ k (truncatedPolynomialIdeal k)).toLinearMap
  have hq : ∀ p : MvPolynomial (Fin 2) k,
      q p = 0 ↔ p ∈ truncatedPolynomialIdeal k := by
    intro p
    exact Ideal.Quotient.eq_zero_iff_mem
  have hqsurj : Function.Surjective q := by
    exact Ideal.Quotient.mkₐ_surjective k (truncatedPolynomialIdeal k)
  let : DirectSum.Decomposition
      (fun n : ℕ => (weightedPolynomialGradedModule k).component n) :=
    (weightedPolynomialGradedModule k).decomposition
  rcases graded_quotient_data (weightedPolynomialGradedModule k)
      (truncatedPolynomialIdeal k) q hq hqsurj hI with ⟨G, hG⟩
  have hfinite : ∀ n : ℕ, Module.Finite k (G.component n) := by
    intro n
    let : Module.Finite k
        (MvPolynomial.weightedHomogeneousSubmodule k twoThreeWeights n) :=
      weighted_polynomial_grading_locally_finite k n
    rw [hG n]
    exact Module.Finite.map
      (MvPolynomial.weightedHomogeneousSubmodule k twoThreeWeights n) q
  let s : Set (Fin 2 →₀ ℕ) :=
    {Finsupp.single 0 2, Finsupp.single 0 1 + Finsupp.single 1 1}
  have hIeq : truncatedPolynomialIdeal k =
      Ideal.span ((fun d => MvPolynomial.monomial d (1 : k)) '' s) := by
    have hsingle : (Finsupp.single 0 1 : Fin 2 →₀ ℕ) + Finsupp.single 0 1 =
        Finsupp.single 0 2 := by
      ext i
      fin_cases i <;> simp
    have himage :
        (fun d : Fin 2 →₀ ℕ => MvPolynomial.monomial d (1 : k)) '' s =
          {MvPolynomial.X 0 ^ 2, MvPolynomial.X 0 * MvPolynomial.X 1} := by
      ext z
      constructor
      · rintro ⟨d, hd, rfl⟩
        simp only [s, Set.mem_insert_iff, Set.mem_singleton_iff] at hd
        rcases hd with rfl | rfl
        · left
          simp [MvPolynomial.X, pow_two, hsingle]
        · right
          simp [MvPolynomial.X]
      · intro hz
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
        rcases hz with hz | hz
        · refine ⟨Finsupp.single 0 2, by simp [s], ?_⟩
          simpa [MvPolynomial.X, pow_two, hsingle] using hz.symm
        · refine ⟨Finsupp.single 0 1 + Finsupp.single 1 1, by simp [s], ?_⟩
          simpa [MvPolynomial.X] using hz.symm
    ext p
    rw [truncatedPolynomialIdeal, himage]
  have hgen : ∀ {n : ℕ} {d : Fin 2 →₀ ℕ},
      2 * d 0 + 3 * d 1 = n →
        ¬(n = 0 ∨ n = 2 ∨ (0 < n ∧ 3 ∣ n)) →
        ∃ si ∈ s, si ≤ d := by
    intro n d hn hbad
    by_cases h20 : 2 ≤ d 0
    · refine ⟨Finsupp.single 0 2, by simp [s], ?_⟩
      intro i
      fin_cases i <;> simp; omega
    by_cases h11 : 1 ≤ d 1
    · refine ⟨Finsupp.single 0 1 + Finsupp.single 1 1, by simp [s], ?_⟩
      intro i
      fin_cases i <;> simp
      all_goals omega
    have hd0 : d 0 = 0 ∨ d 0 = 1 := by omega
    rcases hd0 with hd0 | hd0
    · have hn' : n = 3 * d 1 := by omega
      by_cases hd1 : d 1 = 0
      · exfalso
        apply hbad
        omega
      · exfalso
        apply hbad
        refine Or.inr (Or.inr ⟨?_, ?_⟩)
        · omega
        · exact ⟨d 1, by omega⟩
    · have hd1 : d 1 = 0 := by omega
      exfalso
      apply hbad
      omega
  have hmem_bad : ∀ {n : ℕ} {p : MvPolynomial (Fin 2) k},
      p ∈ MvPolynomial.weightedHomogeneousSubmodule k twoThreeWeights n →
        ¬(n = 0 ∨ n = 2 ∨ (0 < n ∧ 3 ∣ n)) →
        p ∈ truncatedPolynomialIdeal k := by
    intro n p hp hbad
    rw [hIeq]
    apply MvPolynomial.mem_ideal_span_monomial_image.mpr
    intro d hd
    have hweight := hp (MvPolynomial.mem_support_iff.mp hd)
    have hweight' : 2 * d 0 + 3 * d 1 = n := by
      simpa [Finsupp.weight_eq_sum, twoThreeWeights, Nat.mul_comm] using hweight
    exact hgen hweight' hbad
  have hnotgen0 : ¬ ∃ si ∈ s, si ≤ (0 : Fin 2 →₀ ℕ) := by
    rintro ⟨si, hsi, hle⟩
    simp [s] at hsi
    rcases hsi with rfl | rfl <;>
      have := hle 0 <;> simp at this
  have hnotgen2 : ¬ ∃ si ∈ s, si ≤ Finsupp.single 0 1 := by
    rintro ⟨si, hsi, hle⟩
    simp [s] at hsi
    rcases hsi with rfl | rfl
    · have := hle 0
      simp at this
    · have := hle 1
      simp at this
  have hnotgenc (c : ℕ) :
      ¬ ∃ si ∈ s, si ≤ Finsupp.single 1 c := by
    rintro ⟨si, hsi, hle⟩
    simp [s] at hsi
    rcases hsi with rfl | rfl
    · have := hle 0
      simp at this
    · have := hle 0
      simp at this
  have hmonoI : ∀ {d : Fin 2 →₀ ℕ} {r : k},
      (∃ si ∈ s, si ≤ d) →
        MvPolynomial.monomial d r ∈ truncatedPolynomialIdeal k := by
    intro d r hgen'
    rw [hIeq]
    apply MvPolynomial.mem_ideal_span_monomial_image.mpr
    intro di hdi
    have hdi'' : d = di ∧ r ≠ 0 := by
      simpa [MvPolynomial.coeff_monomial] using
        (MvPolynomial.mem_support_iff.mp hdi)
    have hdi' : d = di := hdi''.1
    subst di
    exact hgen'
  have hclass0 : ∀ {d : Fin 2 →₀ ℕ},
      2 * d 0 + 3 * d 1 = 0 → d = 0 := by
    intro d hd
    apply Finsupp.ext
    intro i
    fin_cases i <;> simp at hd ⊢ <;> omega
  have hclass2 : ∀ {d : Fin 2 →₀ ℕ},
      2 * d 0 + 3 * d 1 = 2 → d = Finsupp.single 0 1 := by
    intro d hd
    apply Finsupp.ext
    intro i
    fin_cases i <;> simp at hd ⊢ <;> omega
  have hclassc : ∀ {c : ℕ} {d : Fin 2 →₀ ℕ},
      2 * d 0 + 3 * d 1 = 3 * c →
        d = Finsupp.single 1 c ∨ ∃ si ∈ s, si ≤ d := by
    intro c d hd
    by_cases h0 : d 0 = 0
    · left
      apply Finsupp.ext
      intro i
      fin_cases i <;> simp [h0] at hd ⊢; omega
    · right
      by_cases h20 : 2 ≤ d 0
      · refine ⟨Finsupp.single 0 2, ?_, ?_⟩
        · simp [s]
        · intro i
          fin_cases i <;> simp; omega
      · have hone : d 0 = 1 := by omega
        exfalso
        omega
  have hqmonomial : ∀ (d : Fin 2 →₀ ℕ) (r : k),
      q (MvPolynomial.monomial d r) =
        r • q (MvPolynomial.monomial d (1 : k)) := by
    intro d r
    have hmon :
        MvPolynomial.monomial d r =
          r • MvPolynomial.monomial d (1 : k) := by
      rw [← MvPolynomial.C_mul', MvPolynomial.C_mul_monomial, mul_one]
    calc
      q (MvPolynomial.monomial d r) =
          q (r • MvPolynomial.monomial d (1 : k)) := congrArg q hmon
      _ = r • q (MvPolynomial.monomial d (1 : k)) := q.map_smul r _
  have hmap0 :
      (MvPolynomial.weightedHomogeneousSubmodule k twoThreeWeights 0).map
          q =
        k ∙ q
          (MvPolynomial.monomial 0 (1 : k)) := by
    apply le_antisymm
    · rintro y ⟨p, hp, rfl⟩
      rw [p.as_sum, map_sum]
      apply Submodule.sum_mem
      intro d hd
      have hweight := hp (MvPolynomial.mem_support_iff.mp hd)
      have hweight' : 2 * d 0 + 3 * d 1 = 0 := by
        simpa [Finsupp.weight_eq_sum, twoThreeWeights, Nat.mul_comm] using hweight
      have hdeq := hclass0 hweight'
      rw [hdeq, hqmonomial 0 (MvPolynomial.coeff 0 p)]
      exact Submodule.smul_mem
        (k ∙ q (MvPolynomial.monomial 0 (1 : k)))
        _ (Submodule.mem_span_singleton_self _)
    · intro y hy
      rw [Submodule.mem_span_singleton] at hy
      rcases hy with ⟨a, rfl⟩
      apply (Submodule.mem_map).2
      refine ⟨a • MvPolynomial.monomial 0 (1 : k), ?_, ?_⟩
      · apply (MvPolynomial.weightedHomogeneousSubmodule k twoThreeWeights 0).smul_mem
        exact MvPolynomial.isWeightedHomogeneous_one k twoThreeWeights
      · exact q.map_smul a _
  have hmap2 :
      (MvPolynomial.weightedHomogeneousSubmodule k twoThreeWeights 2).map
          q =
        k ∙ q
          (MvPolynomial.monomial (Finsupp.single 0 1) (1 : k)) := by
    apply le_antisymm
    · rintro y ⟨p, hp, rfl⟩
      rw [p.as_sum, map_sum]
      apply Submodule.sum_mem
      intro d hd
      have hweight := hp (MvPolynomial.mem_support_iff.mp hd)
      have hweight' : 2 * d 0 + 3 * d 1 = 2 := by
        simpa [Finsupp.weight_eq_sum, twoThreeWeights, Nat.mul_comm] using hweight
      have hdeq := hclass2 hweight'
      rw [hdeq,
        hqmonomial (Finsupp.single 0 1)
          (MvPolynomial.coeff (Finsupp.single 0 1) p)]
      exact Submodule.smul_mem
        (k ∙ q (MvPolynomial.monomial (Finsupp.single 0 1) (1 : k)))
        _ (Submodule.mem_span_singleton_self _)
    · intro y hy
      rw [Submodule.mem_span_singleton] at hy
      rcases hy with ⟨a, rfl⟩
      apply (Submodule.mem_map).2
      refine ⟨a • MvPolynomial.monomial (Finsupp.single 0 1) (1 : k), ?_, ?_⟩
      · apply (MvPolynomial.weightedHomogeneousSubmodule k twoThreeWeights 2).smul_mem
        exact MvPolynomial.isWeightedHomogeneous_monomial (R := k)
          twoThreeWeights _ _ (by
          simp [Finsupp.weight_eq_sum, twoThreeWeights])
      · exact q.map_smul a _
  have hmapc (c : ℕ) :
      (MvPolynomial.weightedHomogeneousSubmodule k twoThreeWeights (3 * c)).map
          q =
        k ∙ q
          (MvPolynomial.monomial (Finsupp.single 1 c) (1 : k)) := by
    apply le_antisymm
    · rintro y ⟨p, hp, rfl⟩
      rw [p.as_sum, map_sum]
      apply Submodule.sum_mem
      intro d hd
      have hweight := hp (MvPolynomial.mem_support_iff.mp hd)
      have hweight' : 2 * d 0 + 3 * d 1 = 3 * c := by
        simpa [Finsupp.weight_eq_sum, twoThreeWeights, Nat.mul_comm] using hweight
      rcases hclassc hweight' with rfl | ⟨si, hsi, hle⟩
      · rw [hqmonomial (Finsupp.single 1 c)
          (MvPolynomial.coeff (Finsupp.single 1 c) p)]
        exact Submodule.smul_mem
          (k ∙ q (MvPolynomial.monomial (Finsupp.single 1 c) (1 : k)))
          _ (Submodule.mem_span_singleton_self _)
      · have hi := hmonoI (r := MvPolynomial.coeff d p) ⟨si, hsi, hle⟩
        rw [(hq _).2 hi]
        exact Submodule.zero_mem _
    · intro y hy
      rw [Submodule.mem_span_singleton] at hy
      rcases hy with ⟨a, rfl⟩
      apply (Submodule.mem_map).2
      refine ⟨a • MvPolynomial.monomial (Finsupp.single 1 c) (1 : k), ?_, ?_⟩
      · apply (MvPolynomial.weightedHomogeneousSubmodule k twoThreeWeights (3 * c)).smul_mem
        exact MvPolynomial.isWeightedHomogeneous_monomial (R := k)
          twoThreeWeights _ _ (by
          simp [Finsupp.weight_eq_sum, twoThreeWeights, Nat.mul_comm])
      · exact q.map_smul a _
  refine ⟨G, hfinite, ?_, ?_⟩
  · intro n
    rw [hG n]
    rfl
  · have hq0_ne : q (MvPolynomial.monomial 0 (1 : k)) ≠ 0 := by
      intro hz
      have hpI : MvPolynomial.monomial 0 (1 : k) ∈ truncatedPolynomialIdeal k :=
        (hq _).mp hz
      rw [hIeq] at hpI
      have hsupp : (0 : Fin 2 →₀ ℕ) ∈
          (MvPolynomial.monomial 0 (1 : k)).support := by
        simp
      exact hnotgen0
        ((MvPolynomial.mem_ideal_span_monomial_image.mp hpI) 0 hsupp)
    have hq2_ne :
        q (MvPolynomial.monomial (Finsupp.single 0 1) (1 : k)) ≠ 0 := by
      intro hz
      have hpI :
          MvPolynomial.monomial (Finsupp.single 0 1) (1 : k) ∈
            truncatedPolynomialIdeal k := (hq _).mp hz
      rw [hIeq] at hpI
      have hsupp : (Finsupp.single 0 1 : Fin 2 →₀ ℕ) ∈
          (MvPolynomial.monomial (Finsupp.single 0 1) (1 : k)).support := by
        simp
      exact hnotgen2
        ((MvPolynomial.mem_ideal_span_monomial_image.mp hpI)
          (Finsupp.single 0 1) hsupp)
    have hqc_ne (c : ℕ) :
        q (MvPolynomial.monomial (Finsupp.single 1 c) (1 : k)) ≠ 0 := by
      intro hz
      have hpI :
          MvPolynomial.monomial (Finsupp.single 1 c) (1 : k) ∈
            truncatedPolynomialIdeal k := (hq _).mp hz
      rw [hIeq] at hpI
      have hsupp : (Finsupp.single 1 c : Fin 2 →₀ ℕ) ∈
          (MvPolynomial.monomial (Finsupp.single 1 c) (1 : k)).support := by
        simp
      exact hnotgenc c
        ((MvPolynomial.mem_ideal_span_monomial_image.mp hpI)
          (Finsupp.single 1 c) hsupp)
    have hbad_component : ∀ n : ℕ,
        ¬(n = 0 ∨ n = 2 ∨ (0 < n ∧ 3 ∣ n)) → G.component n = ⊥ := by
      intro n hn
      rw [hG n]
      apply le_antisymm
      · rintro y ⟨p, hp, rfl⟩
        have hpI := hmem_bad hp hn
        have hpzero : q p = 0 := (hq p).2 hpI
        change q p = 0
        exact hpzero
      · exact bot_le
    have hdim0 : Module.finrank k (G.component 0) = 1 := by
      rw [hG 0]
      change Module.finrank k
        (Submodule.map q
          (MvPolynomial.weightedHomogeneousSubmodule k twoThreeWeights 0)) = 1
      rw [hmap0]
      exact finrank_span_singleton hq0_ne
    have hdim2 : Module.finrank k (G.component 2) = 1 := by
      rw [hG 2]
      change Module.finrank k
        (Submodule.map q
          (MvPolynomial.weightedHomogeneousSubmodule k twoThreeWeights 2)) = 1
      rw [hmap2]
      exact finrank_span_singleton hq2_ne
    have hdimc (c : ℕ) :
        Module.finrank k (G.component (3 * c)) = 1 := by
      rw [hG (3 * c)]
      change Module.finrank k
        (Submodule.map q
          (MvPolynomial.weightedHomogeneousSubmodule k twoThreeWeights (3 * c))) = 1
      rw [hmapc c]
      exact finrank_span_singleton (hqc_ne c)
    intro n
    change Module.finrank k (G.component n) =
      if n = 0 ∨ n = 2 ∨ (0 < n ∧ 3 ∣ n) then 1 else 0
    by_cases hn0 : n = 0
    · subst n
      simpa using hdim0
    by_cases hn2 : n = 2
    · subst n
      simpa using hdim2
    by_cases hdiv : 0 < n ∧ 3 ∣ n
    · rcases hdiv.2 with ⟨c, rfl⟩
      simpa [hdiv, hn0, hn2] using hdimc c
    · let : Module.Finite k (G.component n) := hfinite n
      have hbad : ¬(n = 0 ∨ n = 2 ∨ (0 < n ∧ 3 ∣ n)) := by
        intro h
        rcases h with h | h | h
        · exact hn0 h
        · exact hn2 h
        · exact hdiv h
      have hzero : Module.finrank k (G.component n) = 0 :=
        (Submodule.finrank_eq_zero).2 (hbad_component n hbad)
      simpa [hn0, hn2, hdiv] using hzero

theorem truncated_polynomial_no_hilbert_polynomial :
    ¬ HasHilbertPolynomialOnNat truncatedPolynomialHilbertFunction := by
  rintro ⟨P, _hP, hEq⟩
  rcases Filter.eventually_atTop.1 hEq with ⟨N, hN⟩
  let f : ℕ → ℚ := fun m => (6 * (m + N) + 1 : ℕ)
  have hf : Function.Injective f := by
    intro a b hab
    dsimp [f] at hab
    have hab' : 6 * (a + N) + 1 = 6 * (b + N) + 1 := by
      exact_mod_cast hab
    omega
  have hzero : ∀ m : ℕ, P.eval (f m) = 0 := by
    intro m
    have hm : N ≤ 6 * (m + N) + 1 := by omega
    have hm' := hN (6 * (m + N) + 1) hm
    have hval : truncatedPolynomialHilbertFunction (6 * (m + N) + 1) = 0 := by
      simp [truncatedPolynomialHilbertFunction]
      omega
    rw [hval] at hm'
    simpa [f] using hm'.symm
  have hInf : {x : ℚ | P.eval x = 0}.Infinite := by
    apply Set.infinite_of_injective_forall_mem hf
    intro m
    exact hzero m
  have hPzero : P = 0 := by
    apply Polynomial.eq_of_infinite_eval_eq P 0
    simpa using hInf
  have hm := hN (6 * N + 3) (by omega)
  rw [hPzero] at hm
  have hval : truncatedPolynomialHilbertFunction (6 * N + 3) = 1 := by
    simp [truncatedPolynomialHilbertFunction]
    omega
  rw [hval] at hm
  simp at hm

/-! ## Exercise 7: a degree-`d` plane hypersurface -/

/-- The homogeneous equation defining the degree-`d` hypersurface. -/
def hypersurfacePolynomial (k : Type u) [Field k] (d : ℕ) :
    MvPolynomial (Fin 3) k :=
  MvPolynomial.X 0 ^ d + MvPolynomial.X 1 ^ d + MvPolynomial.X 2 ^ d

/-- The homogeneous coordinate ring of the degree-`d` hypersurface. -/
abbrev hypersurfaceRing (k : Type u) [Field k] (d : ℕ) : Type u :=
  MvPolynomial (Fin 3) k ⧸ Ideal.span {hypersurfacePolynomial k d}

/-- The degree-`n` Hilbert-function formula for the hypersurface quotient. -/
def hypersurfaceHilbertFunction (d n : ℕ) : ℕ :=
  Nat.choose (n + 2) 2 - if d ≤ n then Nat.choose (n - d + 2) 2 else 0

/-- The eventual Hilbert polynomial of a plane degree-`d` hypersurface. -/
def hypersurfaceHilbertPolynomial (d : ℕ) : Polynomial ℚ :=
  Polynomial.C (d : ℚ) * Polynomial.X +
    Polynomial.C ((d : ℚ) * (3 - (d : ℚ)) / 2)

/-- The hypersurface quotient has the grading induced from the homogeneous
pieces and the displayed Hilbert-function formula. -/
theorem hypersurface_graded_quotient_exists (k : Type u) [Field k]
    (d : ℕ) (hd : 0 < d) :
    ∃ G : GradedModuleData k (hypersurfaceRing k d) ℕ,
      G.LocallyFinite ∧
        (∀ n : ℕ,
          G.component n =
            (MvPolynomial.homogeneousSubmodule (Fin 3) k n).map
              (Ideal.Quotient.mkₐ k (Ideal.span {hypersurfacePolynomial k d})).toLinearMap) ∧
        ∀ n : ℕ,
          fieldDimensionHilbertFunction G n = hypersurfaceHilbertFunction d n := by
  classical
  let f : MvPolynomial (Fin 3) k := hypersurfacePolynomial k d
  let : GradedAlgebra
      (MvPolynomial.homogeneousSubmodule (Fin 3) k) :=
    MvPolynomial.gradedAlgebra
  have hf : MvPolynomial.IsHomogeneous f d := by
    dsimp [f, hypersurfacePolynomial]
    apply MvPolynomial.IsHomogeneous.add
    · apply MvPolynomial.IsHomogeneous.add
      · simpa using (MvPolynomial.isHomogeneous_X_pow (R := k) 0 d)
      · simpa using (MvPolynomial.isHomogeneous_X_pow (R := k) 1 d)
    · simpa using (MvPolynomial.isHomogeneous_X_pow (R := k) 2 d)
  have hf0 : f ≠ 0 := by
    intro h
    have hc := congrArg (MvPolynomial.coeff (Finsupp.single 0 d)) h
    simp only [f, hypersurfacePolynomial, MvPolynomial.coeff_add,
      MvPolynomial.coeff_X_pow, MvPolynomial.coeff_zero] at hc
    have h10 : (Finsupp.single 1 d : Fin 3 →₀ ℕ) ≠ Finsupp.single 0 d := by
      intro h'
      have h'0 := congrArg (fun e => e 0) h'
      have h'1 := congrArg (fun e => e 1) h'
      simp [hd.ne'] at h'0 h'1
    have h20 : (Finsupp.single 2 d : Fin 3 →₀ ℕ) ≠ Finsupp.single 0 d := by
      intro h'
      have h'0 := congrArg (fun e => e 0) h'
      have h'2 := congrArg (fun e => e 2) h'
      simp [hd.ne'] at h'0 h'2
    have hc' : (1 : k) = 0 := by
      simp [h10, h20] at hc
    exact (one_ne_zero : (1 : k) ≠ 0) hc'
  let H : GradedModuleData k (MvPolynomial (Fin 3) k) ℕ :=
    { component := MvPolynomial.homogeneousSubmodule (Fin 3) k
      decomposition := MvPolynomial.decomposition }
  have hdimH : ∀ m : ℕ,
      Module.finrank k (H.component m) = Nat.choose (m + 2) 2 := by
    intro m
    let S : Set (Fin 3 →₀ ℕ) := {d | d.degree = m}
    let T : Finset (Fin 3 →₀ ℕ) :=
      (Finset.univ : Finset (Fin 3)).finsuppAntidiag m
    have hST : ∀ z, z ∈ (T : Set (Fin 3 →₀ ℕ)) ↔ z ∈ S := by
      intro z
      simp only [T, Finset.mem_coe, S, Finset.mem_finsuppAntidiag']
      simp only [Finsupp.sum]
      constructor
      · rintro ⟨h, _⟩
        simpa [Finsupp.degree_apply] using h
      · intro h
        exact ⟨by simpa [Finsupp.degree_apply] using h, by simp⟩
    have hSet : (T : Set (Fin 3 →₀ ℕ)) = S := by
      ext z
      exact hST z
    have : Finite S := by
      rw [← hSet]
      exact Set.toFinite _
    let := Fintype.ofFinite S
    have hsub : H.component m = MvPolynomial.restrictSupport k S := by
      rw [show H.component m = MvPolynomial.homogeneousSubmodule (Fin 3) k m by rfl]
      rw [MvPolynomial.homogeneousSubmodule_eq_finsupp_supported]
      rfl
    have hcard : Fintype.card S = T.card := by
      let e : S ≃ T :=
        { toFun := fun z => ⟨z.1, (hST z.1).2 z.2⟩
          invFun := fun z => ⟨z.1, (hST z.1).1 z.2⟩
          left_inv := by intro z; rfl
          right_inv := by intro z; rfl }
      simpa using Fintype.card_congr e
    have hTcard : T.card = Nat.choose (m + 2) 2 := by
      have hc := Finset.card_finsuppAntidiag_nat_eq_choose
        (s := (Finset.univ : Finset (Fin 3))) m
      have hcard : (Finset.univ : Finset (Fin 3)).card = 3 := by simp
      rw [hcard] at hc
      rw [show 3 + m - 1 = m + 2 by omega] at hc
      rw [Nat.choose_symm_add] at hc
      exact hc
    calc
      Module.finrank k (H.component m) =
          Module.finrank k (MvPolynomial.restrictSupport k S) := by
            rw [hsub]
      _ = Fintype.card S :=
        Module.finrank_eq_card_basis (MvPolynomial.basisRestrictSupport k S)
      _ = T.card := hcard
      _ = Nat.choose (m + 2) 2 := hTcard
  have hcomp_mul : ∀ (m : ℕ) (g : MvPolynomial (Fin 3) k),
      MvPolynomial.homogeneousComponent m (g * f) =
        if d ≤ m then
          f * MvPolynomial.homogeneousComponent (m - d) g
        else 0 := by
    intro m g
    have hterm (i : ℕ) :
        MvPolynomial.homogeneousComponent m
            (MvPolynomial.homogeneousComponent i g * f) =
          if m = i + d then
            MvPolynomial.homogeneousComponent i g * f else 0 := by
      exact MvPolynomial.homogeneousComponent_of_mem
        ((MvPolynomial.homogeneousComponent_isHomogeneous i g).mul hf)
    calc
      MvPolynomial.homogeneousComponent m (g * f) =
          MvPolynomial.homogeneousComponent m
            ((∑ i ∈ Finset.range (g.totalDegree + 1),
              MvPolynomial.homogeneousComponent i g) * f) := by
                rw [MvPolynomial.sum_homogeneousComponent]
      _ = ∑ i ∈ Finset.range (g.totalDegree + 1),
            (if m = i + d then
              MvPolynomial.homogeneousComponent i g * f else 0) := by
        rw [Finset.sum_mul, map_sum]
        simp_rw [hterm]
      _ = if d ≤ m then
            f * MvPolynomial.homogeneousComponent (m - d) g else 0 := by
        by_cases hdm : d ≤ m
        · let j := m - d
          by_cases hj : j ∈ Finset.range (g.totalDegree + 1)
          · rw [Finset.sum_eq_single j]
            · have hmj : m = j + d := by
                dsimp [j]
                omega
              rw [if_pos hmj]
              simp [hmj, mul_comm]
            · intro i hi hne
              rw [if_neg]
              intro heq
              apply hne
              dsimp [j]
              omega
            · intro hj'
              exact (hj' hj).elim
          · have hjgt : g.totalDegree < j := by
              simpa [Finset.mem_range] using hj
            have hz : MvPolynomial.homogeneousComponent j g = 0 :=
              MvPolynomial.homogeneousComponent_eq_zero j g hjgt
            rw [if_pos hdm, hz, mul_zero]
            apply Finset.sum_eq_zero
            intro i hi
            rw [if_neg]
            intro heq
            apply hj
            rw [Finset.mem_range]
            have hi' : i ≤ g.totalDegree := by
              simpa [Finset.mem_range] using hi
            dsimp [j]
            omega
        · rw [if_neg hdm]
          apply Finset.sum_eq_zero
          intro i hi
          rw [if_neg]
          omega
  have hmul_inj (m : ℕ) :
      Function.Injective
        ((LinearMap.mulLeft k f).domRestrict
          (H.component m)) := by
    intro x y hxy
    apply Subtype.ext
    change f * (x : MvPolynomial (Fin 3) k) =
        f * (y : MvPolynomial (Fin 3) k) at hxy
    exact mul_left_cancel₀ hf0 hxy
  have hI : (Ideal.span {f}).IsHomogeneous
      (MvPolynomial.homogeneousSubmodule (Fin 3) k) := by
    apply Ideal.homogeneous_span
    intro x hx
    rcases hx with rfl
    exact ⟨d, hf⟩
  have hfiniteH : H.LocallyFinite := by
    intro n
    exact Module.Finite.of_fg (MvPolynomial.homogeneousSubmodule_fg (Fin 3) k n)
  let q : MvPolynomial (Fin 3) k →ₗ[k] hypersurfaceRing k d :=
    (Ideal.Quotient.mkₐ k (Ideal.span {f})).toLinearMap
  have hq : ∀ p : MvPolynomial (Fin 3) k, q p = 0 ↔ p ∈ Ideal.span {f} := by
    intro p
    exact Ideal.Quotient.eq_zero_iff_mem
  have hqsurj : Function.Surjective q := by
    exact Ideal.Quotient.mkₐ_surjective k (Ideal.span {f})
  have hkerq : LinearMap.ker q = (Ideal.span {f}).restrictScalars k := by
    ext p
    change q p = 0 ↔ p ∈ Ideal.span {f}
    exact hq p
  let : DirectSum.Decomposition (fun n : ℕ => H.component n) := H.decomposition
  rcases graded_quotient_data H (Ideal.span {f}) q hq hqsurj hI with ⟨G, hG⟩
  have hintersection (n : ℕ) (hdn : d ≤ n) :
      LinearMap.range
          ((LinearMap.mulLeft k f).domRestrict (H.component (n - d))) =
        H.component n ⊓ (Ideal.span {f}).restrictScalars k := by
    let mulf : H.component (n - d) →ₗ[k] MvPolynomial (Fin 3) k :=
      (LinearMap.mulLeft k f).domRestrict (H.component (n - d))
    change LinearMap.range mulf = H.component n ⊓ (Ideal.span {f}).restrictScalars k
    apply le_antisymm
    · rintro p ⟨g, rfl⟩
      constructor
      · change f * (g : MvPolynomial (Fin 3) k) ∈ H.component n
        change MvPolynomial.IsHomogeneous
          (f * (g : MvPolynomial (Fin 3) k)) n
        have hg : MvPolynomial.IsHomogeneous
            (g : MvPolynomial (Fin 3) k) (n - d) := g.property
        convert hf.mul hg using 1; omega
      · exact Ideal.mem_span_singleton'.mpr ⟨(g : MvPolynomial (Fin 3) k), by
          change (g : MvPolynomial (Fin 3) k) * f =
            f * (g : MvPolynomial (Fin 3) k)
          ac_rfl⟩
    · rintro p ⟨hp, hpI⟩
      rcases Ideal.mem_span_singleton'.mp hpI with ⟨g, hg⟩
      let g' : H.component (n - d) :=
        ⟨MvPolynomial.homogeneousComponent (n - d) g,
          MvPolynomial.homogeneousComponent_mem _ _⟩
      refine ⟨g', ?_⟩
      change f * MvPolynomial.homogeneousComponent (n - d) g = p
      calc
        f * MvPolynomial.homogeneousComponent (n - d) g =
            MvPolynomial.homogeneousComponent n (g * f) := by
              rw [hcomp_mul n g, if_pos hdn]
        _ = MvPolynomial.homogeneousComponent n p := by rw [hg]
        _ = p := MvPolynomial.homogeneousComponent_eq_self hp
  have hintersection_zero (n : ℕ) (hn : ¬ d ≤ n) :
      H.component n ⊓ (Ideal.span {f}).restrictScalars k =
        (⊥ : Submodule k (MvPolynomial (Fin 3) k)) := by
    apply bot_unique
    rintro p ⟨hp, hpI⟩
    rcases Ideal.mem_span_singleton'.mp hpI with ⟨g, hg⟩
    have hp0 : p = 0 := by
      calc
        p = MvPolynomial.homogeneousComponent n p :=
          (MvPolynomial.homogeneousComponent_eq_self hp).symm
        _ = MvPolynomial.homogeneousComponent n (g * f) := by rw [hg]
        _ = 0 := by rw [hcomp_mul n g, if_neg hn]
    exact hp0 ▸ Submodule.zero_mem _
  have hdim_component (n : ℕ) :
      Module.finrank k (G.component n) =
        if d ≤ n then
          Module.finrank k (H.component n) -
            Module.finrank k (H.component (n - d))
        else Module.finrank k (H.component n) := by
    let : Module.Finite k (H.component n) := hfiniteH n
    let qn : H.component n →ₗ[k] hypersurfaceRing k d :=
      q.domRestrict (H.component n)
    let K : Submodule k (MvPolynomial (Fin 3) k) :=
      H.component n ⊓ (Ideal.span {f}).restrictScalars k
    have hrange : LinearMap.range qn = G.component n := by
      rw [hG n]
      exact LinearMap.range_domRestrict _ _
    have hkerqn : LinearMap.ker qn =
        ((Ideal.span {f}).restrictScalars k).comap (H.component n).subtype := by
      dsimp [qn]
      rw [LinearMap.ker_domRestrict, hkerq]
    have hkerdimn :
        Module.finrank k (LinearMap.ker qn) =
          Module.finrank k K := by
      calc
        Module.finrank k (LinearMap.ker qn) =
            Module.finrank k
              ((LinearMap.ker qn).map (H.component n).subtype) := by
                symm
                rw [Submodule.finrank_map_subtype_eq]
        _ = Module.finrank k K := by
          rw [hkerqn, Submodule.map_comap_subtype]
    have hrank := qn.finrank_range_add_finrank_ker
    rw [hrange] at hrank
    by_cases hdn : d ≤ n
    · have hkerdim_mul :
          Module.finrank k (LinearMap.ker qn) =
            Module.finrank k (H.component (n - d)) := by
        calc
          Module.finrank k (LinearMap.ker qn) =
              Module.finrank k K := hkerdimn
          _ = Module.finrank k
                (LinearMap.range
                  ((LinearMap.mulLeft k f).domRestrict (H.component (n - d)))) := by
            simpa [K] using
              congrArg (fun L : Submodule k (MvPolynomial (Fin 3) k) =>
                Module.finrank k L) (hintersection n hdn).symm
          _ = Module.finrank k (H.component (n - d)) :=
            LinearMap.finrank_range_of_inj (hmul_inj (n - d))
      rw [hkerdim_mul] at hrank
      simp only [if_pos hdn]
      omega
    · have hkerdim_zero : Module.finrank k (LinearMap.ker qn) = 0 := by
        calc
          Module.finrank k (LinearMap.ker qn) =
              Module.finrank k K := hkerdimn
          _ = Module.finrank k (⊥ : Submodule k (MvPolynomial (Fin 3) k)) := by
            simpa [K] using
              congrArg (fun L : Submodule k (MvPolynomial (Fin 3) k) =>
                Module.finrank k L) (hintersection_zero n hdn)
          _ = 0 := by simp
      rw [hkerdim_zero] at hrank
      simp only [if_neg hdn]
      omega
  refine ⟨G, ?_, ?_, ?_⟩
  · intro n
    let : Module.Finite k (H.component n) := hfiniteH n
    rw [hG n]
    exact Module.Finite.map (H.component n) q
  · intro n
    simpa [f] using hG n
  · intro n
    change Module.finrank k (G.component n) = hypersurfaceHilbertFunction d n
    by_cases hdn : d ≤ n
    · rw [hdim_component n, if_pos hdn, hdimH n, hdimH (n - d)]
      simp [hypersurfaceHilbertFunction, hdn]
    · rw [hdim_component n, if_neg hdn, hdimH n]
      simp [hypersurfaceHilbertFunction, hdn]

/-- For positive `d`, the hypersurface Hilbert function eventually agrees with
the stated numerical polynomial. -/
theorem hypersurface_hilbert_polynomial (d : ℕ) (hd : 0 < d) :
    IsNumericalPolynomial (hypersurfaceHilbertPolynomial d) ∧
      ∀ᶠ n : ℕ in Filter.atTop,
        (hypersurfaceHilbertFunction d n : ℚ) =
          (hypersurfaceHilbertPolynomial d).eval (n : ℚ) := by
  constructor
  · intro z
    refine ⟨(d : ℤ) * z + ((d : ℤ) * (3 - (d : ℤ)) / 2), ?_⟩
    simp [hypersurfaceHilbertPolynomial, Polynomial.eval_add, Polynomial.eval_mul]
    have heven : Even ((d : ℤ) * (3 - (d : ℤ))) := by
      rcases Nat.even_or_odd d with h | h
      · obtain ⟨c, hc⟩ := h
        refine ⟨(c : ℤ) * (3 - (d : ℤ)), ?_⟩
        rw [hc]
        push_cast
        ring
      · obtain ⟨c, hc⟩ := h
        refine ⟨(d : ℤ) * (1 - (c : ℤ)), ?_⟩
        rw [hc]
        push_cast
        ring
    rw [Int.cast_div_charZero heven.two_dvd]
    push_cast
    ring
  · filter_upwards [Filter.eventually_ge_atTop d] with n hn
    simp only [hypersurfaceHilbertFunction, hypersurfaceHilbertPolynomial,
      Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
    rw [if_pos hn]
    have hchoose : (n - d + 2).choose 2 ≤ (n + 2).choose 2 :=
      Nat.choose_le_choose 2 (by omega)
    rw [Nat.cast_sub hchoose]
    rw [Nat.choose_two_right, Nat.choose_two_right]
    have hdiv₁ : 2 ∣ (n + 2) * (n + 2 - 1) := by
      simpa [Nat.mul_comm] using Nat.two_dvd_mul_add_one (n + 1)
    have hdiv₂ : 2 ∣ (n - d + 2) * (n - d + 2 - 1) := by
      simpa [Nat.mul_comm] using Nat.two_dvd_mul_add_one (n - d + 1)
    rw [Nat.cast_div_charZero hdiv₁, Nat.cast_div_charZero hdiv₂]
    push_cast
    rw [Nat.cast_sub hn]
    ring

end Formalization.Books.Exercises.Unit26
