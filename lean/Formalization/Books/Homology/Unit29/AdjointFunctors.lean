import Formalization.Books.Homology.Unit27.Injectives
import Formalization.Books.Categories.Unit23.ExactFunctors
import Formalization.Books.Categories.Unit24.AdjointFunctors
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact
import Mathlib.Algebra.Category.ModuleCat.EnoughInjectives
import Mathlib.CategoryTheory.Adjunction.PartialAdjoint
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import Mathlib.CategoryTheory.Preadditive.Basic
import Mathlib.CategoryTheory.Preadditive.Injective.Preserves
import Mathlib.Data.List.TFAE
import Mathlib.RingTheory.RingHom.Flat
import Mathlib.RingTheory.SimpleModule.InjectiveProjective
import Mathlib.RingTheory.SimpleModule.WedderburnArtin
import Mathlib.RingTheory.SimpleRing.Basic
import Mathlib.Algebra.Field.ZMod

/-!
# Homological Algebra, Chapter 29: Injectives and adjoint functors

This file records the source's adjoint criteria for injectives, the change of
rings example, transfer of enough and functorial injective embeddings, and the
criterion for constructing a left adjoint from a quotient-generating family.
Mathlib's canonical injective, exactness, adjunction, module-category, and
representability interfaces are used throughout.
-/

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Functor
open Formalization.Books.Categories.Unit23
open Formalization.Books.Homology.Unit27
open scoped ZeroObject

universe v₁ u₁ v₂ u₂

namespace Formalization.Books.Homology.Unit29

/-! ## Injectives and adjoint functors -/

/- The source's conditions (a), (b), and (c) are respectively Mathlib's
   preservation of monomorphisms, exactness from Categories Chapter 23, and
   preservation of injective objects.  The existing
   `Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms`
   and `Functor.preservesMonomorphisms_of_adjunction_of_preservesInjectiveObjects`
   are the direct proof interfaces for the two adjoint implications. -/
theorem adjoint_preserve_injectives
    {A : Type u₁} [Category.{v₁} A] [Abelian A]
    {B : Type u₂} [Category.{v₂} B] [Abelian B]
    (u : A ⥤ B) (v : B ⥤ A) [u.Additive] [v.Additive]
    (hAdj : v ⊣ u) :
    (PreservesMonomorphisms v ↔ IsExact v) ∧
      (IsExact v → Functor.PreservesInjectiveObjects u) ∧
      (EnoughInjectives A →
        List.TFAE [PreservesMonomorphisms v, IsExact v,
          Functor.PreservesInjectiveObjects u]) := by
  have hCol : PreservesFiniteColimits v := by
    constructor
    intro J _ _
    exact hAdj.leftAdjoint_preservesColimits.preservesColimitsOfShape
  have hMonoOfExact : IsExact v → PreservesMonomorphisms v := by
    intro h
    exact @preservesMonomorphisms_of_preservesLimitsOfShape _ _ _ _ v
      (h.1.preservesFiniteLimits WalkingCospan)
  have hExactOfMono : PreservesMonomorphisms v → IsExact v := by
    intro h
    refine ⟨?_, hCol⟩
    apply (Functor.preservesFiniteLimits_tfae v).out 0 3 |>.1
    intro S hS
    have hMap : ∀ (S : ShortComplex B), S.ShortExact →
        (S.map v).Exact ∧ Epi (v.map S.g) :=
      ((Functor.preservesFiniteColimits_tfae v).out 3 0).1 hCol
    have hS' := hMap S hS
    have hMonoS : Mono S.f := hS.mono_f
    exact ⟨hS'.1,
      @PreservesMonomorphisms.preserves B _ A _ v h _ _ S.f hMonoS⟩
  have hExactInjective : IsExact v → Functor.PreservesInjectiveObjects u := by
    intro h
    refine ⟨?_⟩
    intro I hI
    exact @Adjunction.map_injective B _ A _ v u hAdj (hMonoOfExact h) I hI
  refine ⟨⟨hExactOfMono, hMonoOfExact⟩, hExactInjective, ?_⟩
  intro hEnough
  have hEnough' : EnoughInjectives A := hEnough
  apply List.tfae_of_forall (IsExact v)
  intro p hp
  rcases List.mem_cons.mp hp with hp | hp
  · subst p
    exact ⟨hExactOfMono, hMonoOfExact⟩
  rcases List.mem_cons.mp hp with hp | hp
  · subst p
    exact Iff.rfl
  have hp := List.mem_singleton.mp hp
  subst p
  constructor
  · exact fun h =>
      hExactOfMono
        (@Functor.preservesMonomorphisms_of_adjunction_of_preservesInjectiveObjects
          B _ A _ hEnough' v u hAdj h)
  · exact hExactInjective

/-! ### Change of rings -/

/- For a map of commutative rings, the source's restriction-of-scalars functor
   is the right adjoint of extension of scalars.  The exactness assertions are
   stated using the chapter's `IsExact` and `IsRightExact` interfaces. -/
theorem change_of_rings_adjunction
    {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) :
    Nonempty (ModuleCat.extendScalars f ⊣ ModuleCat.restrictScalars f) ∧
      IsExact (ModuleCat.restrictScalars f) ∧
        IsRightExact (ModuleCat.extendScalars f) := by
  constructor
  · exact ⟨ModuleCat.extendRestrictScalarsAdj f⟩
  · constructor
    · constructor
      · change PreservesFiniteLimits (ModuleCat.restrictScalars f)
        exact inferInstance
      · change PreservesFiniteColimits (ModuleCat.restrictScalars f)
        exact inferInstance
    · let _ : Algebra R S := f.toAlgebra
      let _ : (ModuleCat.extendScalars f).Additive := by
        constructor
        intro X Y g h
        apply ModuleCat.ExtendScalars.hom_ext
        intro x
        dsimp [ModuleCat.extendScalars, ModuleCat.ExtendScalars.map']
        rw [LinearMap.baseChange_add]
        rfl
      apply (Functor.preservesFiniteColimits_iff_forall_exact_map_and_epi
        (ModuleCat.extendScalars f)).2
      intro C hC
      have hExact : Function.Exact C.f.hom C.g.hom :=
        (CategoryTheory.ShortComplex.ShortExact.moduleCat_exact_iff_function_exact C).1 hC.exact
      have hTensor : Function.Exact
          (C.f.hom.baseChange S) (C.g.hom.baseChange S) :=
        lTensor_exact S hExact hC.moduleCat_surjective_g
      have hMap : (C.map (ModuleCat.extendScalars f)).Exact := by
        apply (CategoryTheory.ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).2
        change Function.Exact (C.f.hom.baseChange S) (C.g.hom.baseChange S)
        exact hTensor
      refine ⟨hMap, ?_⟩
      apply (ModuleCat.epi_iff_surjective _).2
      change Function.Surjective (C.g.hom.baseChange S)
      exact LinearMap.baseChange_surjective S hC.moduleCat_surjective_g

/- The source's final change-of-rings conclusion is the canonical flatness
   criterion for the restriction functor on module categories. -/
theorem change_of_rings_preserves_injectives_iff_flat
    {R : Type u₁} {S : Type u₂} [CommRing R] [CommRing S] (f : R →+* S) :
    Functor.PreservesInjectiveObjects (ModuleCat.restrictScalars.{max u₁ u₂} f) ↔
      RingHom.Flat f := by
  let _ : Algebra R S := f.toAlgebra
  let F := ModuleCat.extendScalars.{u₁, u₂, max u₁ u₂} f
  let G := ModuleCat.restrictScalars.{max u₁ u₂} f
  have hAdj : F ⊣ G := ModuleCat.extendRestrictScalarsAdj.{u₁, u₁, u₂} f
  constructor
  · intro hG
    let : Functor.PreservesInjectiveObjects G := hG
    have hMonoF : PreservesMonomorphisms F :=
      Functor.preservesMonomorphisms_of_adjunction_of_preservesInjectiveObjects hAdj
    have hMonoF' : ∀ {X Y : ModuleCat.{max u₁ u₂} R} (g : X ⟶ Y),
        Mono g → Mono (F.map g) := by
      intro X Y g hg
      let : Mono g := hg
      exact hMonoF.preserves g
    refine Module.Flat.iff_lTensor_preserves_injective_linearMap.mpr ?_
    intro N N' _ _ _ _ g hg
    let g' : ModuleCat.of R N ⟶ ModuleCat.of R N' := ModuleCat.ofHom g
    have hg' : Mono g' := (ModuleCat.mono_iff_injective g').2 hg
    have hFg : Mono (F.map g') := hMonoF' g' hg'
    have hFg' : Function.Injective (F.map g') := (ModuleCat.mono_iff_injective _).1 hFg
    change Function.Injective (g.baseChange S) at hFg'
    rw [LinearMap.baseChange_eq_ltensor] at hFg'
    exact hFg'
  · intro hf
    let : Module.Flat R S := hf
    have hMonoF : PreservesMonomorphisms F := by
      constructor
      intro X Y g hg
      rw [ModuleCat.mono_iff_injective] at hg ⊢
      change Function.Injective (g.hom.baseChange S)
      rw [LinearMap.baseChange_eq_ltensor]
      exact Module.Flat.lTensor_preserves_injective_linearMap g.hom hg
    let : PreservesMonomorphisms F := hMonoF
    exact Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms hAdj

/- The source's example is stated with an explicit primality hypothesis, since
   `ZMod p` is the field occurring in the example only for prime `p`. -/
theorem zmod_prime_change_of_rings_counterexample
    (p : ℕ) (hp : Nat.Prime p) :
    Injective (ModuleCat.of (ZMod p) (ZMod p)) ∧
      ¬ Injective
        ((ModuleCat.restrictScalars (Int.castRingHom (ZMod p))).obj
          (ModuleCat.of (ZMod p) (ZMod p))) ∧
      ¬ Functor.PreservesInjectiveObjects
        (ModuleCat.restrictScalars (Int.castRingHom (ZMod p))) := by
  let : Fact (Nat.Prime p) := ⟨hp⟩
  let : IsArtinianRing (ZMod p) := isArtinian_of_finite
  have hfield : Module.Injective (ZMod p) (ZMod p) := by
    apply Module.injective_of_isSemisimpleRing
  have hinj : Injective (ModuleCat.of (ZMod p) (ZMod p)) :=
    (Module.injective_iff_injective_object (ZMod p) (ZMod p)).mp hfield
  have hnotMod : ¬ Module.Injective ℤ (ZMod p) := by
    intro hZ'
    let q : ℤ →ₗ[ℤ] ℤ := LinearMap.lsmul ℤ ℤ (p : ℤ)
    have hq : Function.Injective q := by
      intro x y hxy
      apply (mul_left_cancel₀ (show (p : ℤ) ≠ 0 by exact_mod_cast hp.ne_zero))
      simpa [q] using hxy
    let g : ℤ →ₗ[ℤ] ZMod p := LinearMap.toSpanSingleton ℤ _ 1
    obtain ⟨l, hl⟩ := hZ'.out q hq g
    have hl₁ := hl 1
    have hl₁' : l (p : ℤ) = (1 : ZMod p) := by
      simpa [q, g]
        using hl₁
    have hlzero : l (p : ℤ) = 0 := by
      calc
        l (p : ℤ) = (p : ZMod p) • l 1 := by
          simpa using (l.map_smul (p : ℤ) (1 : ℤ))
        _ = 0 := by rw [ZMod.natCast_self, zero_smul]
    have h01 : (0 : ZMod p) = 1 := hlzero.symm.trans hl₁'
    exact zero_ne_one h01
  have hnot : ¬ Injective
      ((ModuleCat.restrictScalars (Int.castRingHom (ZMod p))).obj
        (ModuleCat.of (ZMod p) (ZMod p))) := by
    intro hZ
    let M := (ModuleCat.restrictScalars (Int.castRingHom (ZMod p))).obj
      (ModuleCat.of (ZMod p) (ZMod p))
    have hZ' : Module.Injective ℤ M :=
      (Module.injective_iff_injective_object ℤ M).mpr hZ
    let q : ℤ →ₗ[ℤ] ℤ := LinearMap.lsmul ℤ ℤ (p : ℤ)
    have hq : Function.Injective q := by
      intro x y hxy
      apply (mul_left_cancel₀ (show (p : ℤ) ≠ 0 by exact_mod_cast hp.ne_zero))
      simpa [q] using hxy
    let oneM : M := show ZMod p from 1
    let g : ℤ →ₗ[ℤ] M := LinearMap.toSpanSingleton ℤ M oneM
    obtain ⟨l, hl⟩ := hZ'.out q hq g
    have hq1 : q 1 = (p : ℤ) := by simp [q]
    have hg1 : g 1 = oneM := by
      exact LinearMap.toSpanSingleton_apply_one ℤ M oneM
    have hl₁ := hl 1
    rw [hq1, hg1] at hl₁
    have hlzero : l (p : ℤ) = 0 := by
      calc
        l (p : ℤ) = l (p • (1 : ℤ)) := by simp
        _ = p • l 1 := by exact map_nsmul l p 1
        _ = 0 := by
          exact (show p • (l 1 : ZMod p) = 0 by
            rw [← Nat.cast_smul_eq_nsmul (R := ZMod p), ZMod.natCast_self, zero_smul])
    have hbad := hlzero.symm.trans hl₁
    have hdown : (0 : ZMod p) = 1 :=
      congrArg (fun x : M => (x : ZMod p)) hbad
    exact zero_ne_one hdown
  refine ⟨hinj, hnot, ?_⟩
  intro hpres
  let I : ModuleCat.{u_1} (ZMod p) :=
    ModuleCat.of (ZMod p) (ULift.{u_1} (ZMod p))
  have hI : Injective I := by
    apply (Module.injective_iff_injective_object (ZMod p) (ULift.{u_1} (ZMod p))).mp
    exact Module.ulift_injective_of_injective (R := ZMod p) (M := ZMod p)
      (Module.injective_of_isSemisimpleRing (ZMod p) (ZMod p))
  have hInot : ¬ Injective
      ((ModuleCat.restrictScalars (Int.castRingHom (ZMod p))).obj I) := by
    intro hU
    have hU' : Module.Injective ℤ
        ((ModuleCat.restrictScalars (Int.castRingHom (ZMod p))).obj I) :=
      (Module.injective_iff_injective_object ℤ _).mpr hU
    let q : ULift.{u_1} ℤ →ₗ[ℤ] ULift.{u_1} ℤ :=
      LinearMap.lsmul ℤ (ULift.{u_1} ℤ) (p : ℤ)
    have hq : Function.Injective q := by
      intro x y hxy
      apply ULift.ext
      apply (mul_left_cancel₀ (show (p : ℤ) ≠ 0 by exact_mod_cast hp.ne_zero))
      simpa [q] using congrArg ULift.down hxy
    let U := (ModuleCat.restrictScalars (Int.castRingHom (ZMod p))).obj I
    let oneU : U := ULift.up (1 : ZMod p)
    let g₀ : ℤ →ₗ[ℤ] U := LinearMap.toSpanSingleton ℤ U oneU
    let g : ULift.{u_1} ℤ →ₗ[ℤ] U := g₀.comp ULift.moduleEquiv.toLinearMap
    obtain ⟨l, hl⟩ := hU'.out q hq g
    have hl₁ := hl ⟨1⟩
    have hq1 : q ⟨1⟩ = (⟨p⟩ : ULift.{u_1} ℤ) := by
      apply ULift.ext
      simp [q]
    have hg1 : g ⟨1⟩ = oneU := by
      simpa [g, g₀, oneU] using
        (LinearMap.toSpanSingleton_apply_one ℤ U oneU)
    rw [hq1, hg1] at hl₁
    have hlzero : l ⟨p⟩ = 0 := by
      calc
        l ⟨p⟩ = l (p • (⟨1⟩ : ULift.{u_1} ℤ)) := by
          congr 1
          apply ULift.ext
          simp
        _ = p • l ⟨1⟩ := by exact map_nsmul l p ⟨1⟩
        _ = 0 := by
          exact (show p • (l ⟨1⟩ : ULift.{u_1} (ZMod p)) = 0 by
            rw [← Nat.cast_smul_eq_nsmul (R := ZMod p), ZMod.natCast_self, zero_smul])
    have hbad := hlzero.symm.trans hl₁
    have hdown : (0 : ZMod p) = 1 :=
      congrArg (fun x : U => ULift.down x) hbad
    exact zero_ne_one hdown
  exact hInot (hpres.injective_obj hI)

/-! ### Enough injectives and faithfulness -/

theorem adjoint_enough_injectives
    {A : Type u₁} [Category.{v₁} A] [Abelian A]
    {B : Type u₂} [Category.{v₂} B] [Abelian B]
    (u : A ⥤ B) (v : B ⥤ A) [u.Additive] [v.Additive]
    (hAdj : v ⊣ u) (hMono : PreservesMonomorphisms v)
    (hEnough : EnoughInjectives A)
    (hReflectsZero : ∀ B₀ : B, IsZero (v.obj B₀) → IsZero B₀) :
    EnoughInjectives B := by
  refine ⟨fun B₀ => ?_⟩
  obtain ⟨p⟩ := hEnough.presentation (v.obj B₀)
  let g : B₀ ⟶ u.obj p.J := (hAdj.homEquiv B₀ p.J) p.f
  have hcomp : v.map (kernel.ι g) ≫ p.f = 0 := by
    apply (hAdj.homEquiv (kernel g) p.J).injective
    rw [hAdj.homEquiv_naturality_left]
    simp only [hAdj.homEquiv_unit, Functor.map_zero, comp_zero]
    change kernel.ι g ≫ g = 0
    exact kernel.condition g
  have hzero : v.map (kernel.ι g) = 0 := by
    apply (cancel_mono p.f).1
    simpa using hcomp
  have hvmono : Mono (v.map (kernel.ι g)) :=
    @PreservesMonomorphisms.preserves B _ A _ v hMono _ _ (kernel.ι g) inferInstance
  have hkernel : IsZero (v.obj (kernel g)) := by
    rw [IsZero.iff_id_eq_zero]
    apply (@cancel_mono _ _ _ _ _ (v.map (kernel.ι g)) hvmono).1
    simp [hzero]
  have hkernel' : IsZero (kernel g) := hReflectsZero _ hkernel
  exact ⟨{
    J := u.obj p.J
    injective := hAdj.map_injective p.J p.injective
    f := g
    mono := Preadditive.mono_of_isZero_kernel g hkernel'
  }⟩

/- In the presence of the adjunction and preservation of monomorphisms, the
   source's objectwise condition (4) is exactly faithfulness of `v`. -/
theorem adjoint_faithful_iff_reflects_zero
    {A : Type u₁} [Category.{v₁} A] [Abelian A]
    {B : Type u₂} [Category.{v₂} B] [Abelian B]
    (u : A ⥤ B) (v : B ⥤ A) [u.Additive] [v.Additive]
    (hAdj : v ⊣ u) (hMono : PreservesMonomorphisms v) :
    Functor.Faithful v ↔
      ∀ B₀ : B, IsZero (v.obj B₀) → IsZero B₀ := by
  constructor
  · intro hFaithful B₀ hB₀
    rw [IsZero.iff_id_eq_zero]
    apply hFaithful.map_injective
    calc
      v.map (𝟙 B₀) = 𝟙 (v.obj B₀) := v.map_id _
      _ = 0 := hB₀.eq_of_src _ _
      _ = v.map (0 : B₀ ⟶ B₀) := (v.map_zero B₀ B₀).symm
  · intro hReflectsZero
    have : PreservesMonomorphisms v := hMono
    have : PreservesEpimorphisms v :=
      Functor.preservesEpimorphisms_of_adjunction hAdj
    constructor
    intro X Y f g hfg
    have hsub : v.map (f - g) = 0 := by
      rw [Functor.map_sub, hfg, sub_self]
    have hsub' : f - g = 0 := by
      let q := f - g
      have hq : v.map q = 0 := hsub
      have himage : v.map (Abelian.image.ι q) = 0 := by
        apply zero_of_epi_comp (v.map (Abelian.factorThruImage q))
        rw [← v.map_comp, Abelian.image.fac, hq]
      have hzero : IsZero (v.obj (Abelian.image q)) :=
        IsZero.of_mono_eq_zero _ himage
      have hzero' : IsZero (Abelian.image q) := hReflectsZero _ hzero
      have himage' : Abelian.image.ι q = 0 := hzero'.eq_of_src _ _
      have himage'' : Abelian.image.ι (f - g) = 0 := by simpa [q] using himage'
      calc
        f - g = Abelian.factorThruImage (f - g) ≫ Abelian.image.ι (f - g) :=
          (Abelian.image.fac (f - g)).symm
        _ = 0 := by rw [himage'', comp_zero]
    exact sub_eq_zero.mp hsub'

/- The zero-functor example from the source makes the need for the objectwise
   zero-reflection hypothesis explicit.  The two constant functors at the
   zero objects are the canonical zero functors in an abelian category. -/
theorem zero_functors_counterexample
    {A : Type u₁} [Category.{v₁} A] [Abelian A]
    {B : Type u₂} [Category.{v₂} B] [Abelian B]
    (hB : ∃ X : B, ¬ IsZero X) :
    let u₀ : A ⥤ B := (Functor.const A).obj (0 : B)
    let v₀ : B ⥤ A := (Functor.const B).obj (0 : A)
    Nonempty (v₀ ⊣ u₀) ∧
      PreservesMonomorphisms v₀ ∧
        IsExact v₀ ∧
            ¬ Functor.Faithful v₀ ∧
              ¬ (∀ X : B, IsZero (v₀.obj X) → IsZero X) := by
  let u₀ : A ⥤ B := (Functor.const A).obj (0 : B)
  let v₀ : B ⥤ A := (Functor.const B).obj (0 : A)
  change Nonempty (v₀ ⊣ u₀) ∧
    PreservesMonomorphisms v₀ ∧
      IsExact v₀ ∧
        ¬ Functor.Faithful v₀ ∧
          ¬ (∀ X : B, IsZero (v₀.obj X) → IsZero X)
  have hAdj : Nonempty (v₀ ⊣ u₀) := by
    refine ⟨Adjunction.mkOfHomEquiv ?_⟩
    refine {
      homEquiv := fun X Y => ?_
      homEquiv_naturality_left_symm := ?_
      homEquiv_naturality_right := ?_ }
    · letI : Unique (v₀.obj X ⟶ Y) :=
        ⟨⟨0⟩, fun f => (isZero_zero A).eq_of_src _ _⟩
      letI : Unique (X ⟶ u₀.obj Y) :=
        ⟨⟨0⟩, fun f => (isZero_zero B).eq_of_tgt _ _⟩
      exact Equiv.ofUnique _ _
    · intro X' X Y f g
      exact (isZero_zero A).eq_of_src _ _
    · intro X Y Y' f g
      exact (isZero_zero B).eq_of_tgt _ _
  have hMono : PreservesMonomorphisms v₀ := by
    constructor
    intro X Y f hf
    dsimp [v₀]
    infer_instance
  have hZero : IsZero v₀ := Functor.isZero _ (fun X => isZero_zero _)
  have hExact : IsExact v₀ := by
    change PreservesFiniteLimits v₀ ∧ PreservesFiniteColimits v₀
    constructor
    · constructor
      intro J _ _
      exact v₀.preservesLimitsOfShape_of_isZero hZero J
    · constructor
      intro J _ _
      exact v₀.preservesColimitsOfShape_of_isZero hZero J
  have hNotFaithful : ¬ Functor.Faithful v₀ := by
    intro hFaithful
    obtain ⟨X, hX⟩ := hB
    have hEq : v₀.map (𝟙 X) = v₀.map (0 : X ⟶ X) := by
      rfl
    have hId : (𝟙 X) = 0 := hFaithful.map_injective hEq
    exact hX ((IsZero.iff_id_eq_zero X).2 hId)
  have hNotReflects :
      ¬ (∀ X : B, IsZero (v₀.obj X) → IsZero X) := by
    intro hReflects
    obtain ⟨X, hX⟩ := hB
    apply hX
    apply hReflects X
    simpa [v₀] using (isZero_zero A)
  exact ⟨hAdj, hMono, hExact, hNotFaithful, hNotReflects⟩

/-! ### Functorial injective embeddings -/

theorem adjoint_functorial_injective_embeddings
    {A : Type u₁} [Category.{v₁} A] [Abelian A]
    {B : Type u₂} [Category.{v₂} B] [Abelian B]
    (u : A ⥤ B) (v : B ⥤ A) [u.Additive] [v.Additive]
    (hAdj : v ⊣ u) (hMono : PreservesMonomorphisms v)
    (hEnough : EnoughInjectives A)
    (hReflectsZero : ∀ B₀ : B, IsZero (v.obj B₀) → IsZero B₀)
    (hFunctorial : HasFunctorialInjectiveEmbeddings (C := A)) :
    HasFunctorialInjectiveEmbeddings (C := B) := by
  /-
  Prior attempt: the checked functor construction is retained, but its
  naturality and arrow-category coercions do not compile with the current API.
  haveI : PreservesMonomorphisms v := hMono
  haveI : Functor.Faithful v :=
    (adjoint_faithful_iff_reflects_zero u v hAdj hMono).2 hReflectsZero
  haveI : PreservesMonomorphisms u :=
    Functor.preservesMonomorphisms_of_adjunction hAdj
  obtain ⟨J, hJleft, hJmono, hJinjective⟩ := hFunctorial
  let e : (J ⋙ Arrow.leftFunc) ≅ 𝟭 A := eqToIso hJleft
  let J' : B ⥤ Arrow B := {
    obj X := Arrow.mk
      (hAdj.unit.app X ≫
        u.map (e.inv.app (v.obj X) ≫ (J.obj (v.obj X)).hom))
    map {X Y} f := Arrow.homMk f
      (u.map (J.map (v.map f)).right) (by
        have hinside :
            v.map f ≫ (e.inv.app (v.obj Y) ≫ (J.obj (v.obj Y)).hom) =
              (e.inv.app (v.obj X) ≫ (J.obj (v.obj X)).hom) ≫
                (J.map (v.map f)).right := by
          rw [← Category.assoc, e.inv.naturality]
          simp only [Functor.comp_map, Functor.id_map, Category.assoc]
          rw [(J.map (v.map f)).w]
        simp only [Category.assoc]
        rw [hAdj.unit.naturality, ← u.map_comp, ← u.map_comp, hinside])
    map_id X := by
      apply Arrow.hom_ext <;> simp
    map_comp f g := by
      apply Arrow.hom_ext <;> simp
  }
  have hJ'left : J' ⋙ Arrow.leftFunc = 𝟭 B := by
    apply Functor.ext <;> simp [J']
  have hJ'mono : ∀ X : B, Mono (J'.obj X).hom := by
    intro X
    dsimp [J']
    letI : Mono (J.obj (v.obj X)).hom := hJmono _
    infer_instance
  have hJ'injective : ∀ X : B, Injective (J'.obj X).right := by
    intro X
    dsimp [J']
    exact Functor.injective_obj_of_injective u (hJinjective (v.obj X))
  exact ⟨J', hJ'left, hJ'mono, hJ'injective⟩
  -/
  sorry

/-! ### A partially defined left adjoint -/

/- `CorepresentableBy` is the precise functorial form of the source's
   equality
   `Hom_A(Q, A) = Hom_B(P, u(A))`.  Its `homEquiv (𝟙 Q)` is the source's
   universal map `P → u(Q)`, and `CorepresentableBy.homEquiv_eq` supplies the
   displayed characterization of all represented morphisms.  The remaining
   maps on the quotient-generating family and the exact sequence
   `P₂ → P₁ → B → 0` are construction details of the standard proof, so no
   parallel functor or presentation API is introduced here. -/
theorem left_adjoint_of_quotient_generators
    {A : Type u₁} [Category.{v₁} A] [Abelian A]
    {B : Type u₂} [Category.{v₂} B] [Abelian B]
    (u : A ⥤ B) (Pset : Set B)
    (hQuotient : ∀ B₀ : B,
      ∃ P : B, P ∈ Pset ∧ ∃ f : P ⟶ B₀, Epi f)
    (hRepresentable : ∀ P : B, P ∈ Pset →
      ∃ Q : A,
        Nonempty ((u ⋙ coyoneda.obj (Opposite.op P)).CorepresentableBy Q)) :
    ∃ v : B ⥤ A, Nonempty (v ⊣ u) := by
  sorry

end Formalization.Books.Homology.Unit29
