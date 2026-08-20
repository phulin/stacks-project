import Formalization.Books.Dualizing.Unit02.Essential
import Mathlib.Algebra.Category.ModuleCat.Biproducts
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.Algebra.Category.ModuleCat.EnoughInjectives
import Mathlib.Algebra.DirectSum.Module
import Mathlib.Algebra.Module.Injective
import Mathlib.RingTheory.Ideal.Maximal
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.LocalRing.Basic
import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
import Mathlib.RingTheory.Noetherian.Defs

/-!
# Dualizing Complexes, Chapter 5: Injective hulls

This file records the definitions, examples, and theorem interfaces in the
chapter.  Proofs are intentionally deferred to the proving stage.
-/

namespace Formalization.Books.Dualizing.Unit05

open CategoryTheory
open CategoryTheory.Limits
open DirectSum
open Formalization.Books.Dualizing.Unit02
open Set

universe u v w

noncomputable section

/-! ## Injective hulls -/

/- The canonical `CategoryTheory.Injective` predicate is used for injective
objects, and `EssentialExtension` is the essential-monomorphism predicate
introduced in Chapter 2. -/

/-- An essential extension whose target is an injective module. -/
def InjectiveHull {R : Type u} [Ring R] {M E : ModuleCat.{v} R}
    (f : M ⟶ E) : Prop :=
  EssentialExtension f ∧ CategoryTheory.Injective E

/-- Every module has an injective hull. -/
theorem exists_injective_hull {R : Type u} [Ring R] [Small.{v} R]
    (M : ModuleCat.{v} R) :
    ∃ (E : ModuleCat.{v} R) (f : M ⟶ E), InjectiveHull f := by
  let p : InjectivePresentation M :=
    (EnoughInjectives.presentation M).some
  let : CategoryTheory.Injective p.J := p.injective
  let I : Type v := (p.J : Type v)
  let : Module.Injective R I :=
    Module.injective_module_of_injective_object R (p.J : Type v)
  let j : (M : Type v) →ₗ[R] I := p.f.hom
  have hj : Function.Injective j :=
    (ModuleCat.mono_iff_injective p.f).mp p.mono
  let J : Submodule R I := LinearMap.range j
  let Good : Submodule R I → Prop := fun E =>
    J ≤ E ∧ ∀ T : Submodule R I, T ≤ E → T ≠ ⊥ → J ⊓ T ≠ ⊥
  have hJGood : Good J := by
    refine ⟨le_rfl, ?_⟩
    intro T hTJ hTne
    rw [inf_eq_right.mpr hTJ]
    exact hTne
  have range_essential :
      ∀ (A B : ModuleCat.{v} R) (u : A ⟶ B), EssentialExtension u →
        EssentialSubmodule (LinearMap.range u.hom) := by
    intro A B u hu
    let : Mono u := hu.1
    let : Mono (ModuleCat.ofHom (LinearMap.range u.hom).subtype) :=
      ConcreteCategory.mono_of_injective _ Subtype.val_injective
    let S : Submodule R (B : Type v) := LinearMap.range u.hom
    let e : (A : Type v) ≃ₗ[R] S :=
      LinearEquiv.ofBijective u.hom.rangeRestrict
        ⟨(LinearMap.injective_rangeRestrict_iff u.hom).2
            (by
              intro x y hxy
              apply (ModuleCat.mono_iff_injective u).mp hu.1
              simpa using hxy),
          u.hom.surjective_rangeRestrict⟩
    have heq : e.toModuleIso.hom ≫ ModuleCat.ofHom S.subtype = u := by
      apply ModuleCat.hom_ext
      rfl
    have hmk :
        Subobject.mk u = Subobject.mk (ModuleCat.ofHom S.subtype) :=
      Subobject.mk_eq_mk_of_comm u (ModuleCat.ofHom S.subtype) e.toModuleIso heq
    apply (essentialSubmodule_iff_essentialExtension S).2
    unfold EssentialExtension
    have hSmono : Mono (ModuleCat.ofHom S.subtype) :=
      ConcreteCategory.mono_of_injective _ Subtype.val_injective
    refine ⟨hSmono, ?_⟩
    intro P hP
    rw [← hmk]
    exact hu.2 P hP
  have hupper :
      ∀ c ⊆ {E : Submodule R I | Good E},
        IsChain (· ≤ ·) c →
        ∀ y ∈ c, ∃ ub ∈ {E : Submodule R I | Good E},
          ∀ z ∈ c, z ≤ ub := by
    intro c hc hchain y hy
    let U : Submodule R I := sSup c
    have hcne : c.Nonempty := ⟨y, hy⟩
    refine ⟨U, ?_, ?_⟩
    · refine ⟨?_, ?_⟩
      · exact (hc hy).1.trans (le_sSup hy)
      · intro T hTU hTne
        obtain ⟨x, hxT, hx0⟩ := T.ne_bot_iff.mp hTne
        have hxU : x ∈ U := hTU hxT
        obtain ⟨E, hEc, hxE⟩ :=
          (Submodule.mem_sSup_of_directed hcne hchain.directedOn).mp hxU
        have hTE : T ⊓ E ≠ ⊥ := by
          intro hbot
          apply hx0
          have hxinf : x ∈ T ⊓ E := ⟨hxT, hxE⟩
          rw [hbot] at hxinf
          exact (Submodule.mem_bot R).mp hxinf
        obtain ⟨z, hz, hz0⟩ :=
          (J ⊓ (T ⊓ E)).ne_bot_iff.mp
            ((hc hEc).2 (T ⊓ E) inf_le_right hTE)
        refine (J ⊓ T).ne_bot_iff.mpr ⟨z, ?_, hz0⟩
        exact ⟨hz.1, hz.2.1⟩
    · intro z hz
      exact le_sSup hz
  obtain ⟨E, hJE, hEmax⟩ :=
    zorn_le_nonempty₀ {E : Submodule R I | Good E} hupper J hJGood
  have hEGood : Good E := hEmax.1
  have htriv :
      ∀ (E' : Submodule R I) (hEE' : E ≤ E'),
        EssentialExtension (ModuleCat.ofHom (E.inclusion hEE')) → E = E' := by
    intro E' hEE' hEss
    have hEssRange :
        EssentialSubmodule (LinearMap.range (E.inclusion hEE')) :=
      range_essential (ModuleCat.of R E) (ModuleCat.of R E')
        (ModuleCat.ofHom (E.inclusion hEE')) hEss
    have hGoodE' : Good E' := by
      refine ⟨hEGood.1.trans hEE', ?_⟩
      intro T hTE' hTne
      obtain ⟨x, hxT, hx0⟩ := T.ne_bot_iff.mp hTne
      let x' : E' := ⟨x, hTE' hxT⟩
      have hx'0 : x' ≠ 0 := by
        intro hx'
        apply hx0
        exact congrArg Subtype.val hx'
      obtain ⟨r, hrange, hr0⟩ :=
        (essentialSubmodule_iff_smul _).1 hEssRange x' hx'0
      rcases hrange with ⟨e, he⟩
      have he0 : (e : I) ≠ 0 := by
        intro he0
        apply hr0
        rw [← he]
        apply Subtype.ext
        simp [he0]
      let U : Submodule R I := Submodule.span R ({(e : I)} : Set I)
      have hUE : U ≤ E := by
        rw [Submodule.span_le]
        intro z hz
        rcases Set.mem_singleton_iff.mp hz with rfl
        exact e.property
      have hUne : U ≠ ⊥ := by
        rw [Submodule.ne_bot_iff]
        exact ⟨(e : I), Submodule.mem_span_singleton_self (e : I), he0⟩
      obtain ⟨z, hz, hz0⟩ :=
        (J ⊓ U).ne_bot_iff.mp (hEGood.2 U hUE hUne)
      have hzU : z ∈ U := hz.2
      rw [Submodule.mem_span_singleton] at hzU
      rcases hzU with ⟨s, hs⟩
      have he' : (e : I) = r • (x : I) := by
        exact congrArg (fun q : E' => (q : I)) he
      have hsr : (s * r) • (x : I) = z := by
        calc
          (s * r) • (x : I) = s • (r • (x : I)) := by rw [mul_smul]
          _ = s • (e : I) := by rw [← he']
          _ = z := hs
      refine (J ⊓ T).ne_bot_iff.mpr ⟨(s * r) • (x : I), ?_, ?_⟩
      · exact ⟨(hsr.symm ▸ hz).1, T.smul_mem (s * r) hxT⟩
      · rw [hsr]
        exact hz0
    exact hEmax.eq_of_le hGoodE' hEE'
  have hE_module : Module.Injective R E := by
    refine ⟨?_⟩
    intro X Y _ _ _ _ i hi g
    have : Fact (Function.Injective i) := ⟨hi⟩
    let a := Module.Baer.extensionOfMax i g
    let ga : a.domain →ₗ[R] E :=
      { toFun := fun x => a.toLinearPMap x
        map_add' := by
          intro x y
          rw [← LinearPMap.map_add]
        map_smul' := by
          intro r x
          rw [← LinearPMap.map_smul]
          rfl }
    obtain ⟨ψ, hψ⟩ :=
      (inferInstance : Module.Injective R I).out a.domain.subtype
        Subtype.val_injective (E.subtype.comp ga)
    by_cases hψE : ∀ y, ψ y ∈ E
    · let h : Y →ₗ[R] E := ψ.codRestrict E hψE
      refine ⟨h, ?_⟩
      intro x
      apply Subtype.ext
      change ψ (i x) = E.subtype (g x)
      have hψx :
          ψ (i x) = E.subtype (ga ⟨i x, a.le ⟨x, rfl⟩⟩) := by
        simpa using hψ ⟨i x, a.le ⟨x, rfl⟩⟩
      rw [hψx]
      simpa [ga] using congrArg E.subtype (a.is_extension x).symm
    · let H : Submodule R I := E ⊔ LinearMap.range ψ
      have hHE : E ≤ H := le_sup_left
      have hneq : E ≠ H := by
        intro hEH
        obtain ⟨y, hy⟩ := not_forall.mp hψE
        apply hy
        rw [hEH]
        exact Submodule.mem_sup_right (ψ.mem_range_self y)
      let jH : E →ₗ[R] H := E.inclusion hHE
      let S : Submodule R H := LinearMap.range jH
      have hjH : Function.Injective jH := Submodule.inclusion_injective hHE
      let e : E ≃ₗ[R] S :=
        LinearEquiv.ofBijective jH.rangeRestrict
          ⟨(LinearMap.injective_rangeRestrict_iff jH).2 hjH,
            jH.surjective_rangeRestrict⟩
      have : Mono (ModuleCat.ofHom (E.inclusion hHE)) :=
        ConcreteCategory.mono_of_injective _ (Submodule.inclusion_injective hHE)
      have : Mono (ModuleCat.ofHom jH) :=
        ConcreteCategory.mono_of_injective _ hjH
      have : Mono (ModuleCat.ofHom S.subtype) :=
        ConcreteCategory.mono_of_injective _ Subtype.val_injective
      have heq :
          e.toModuleIso.hom ≫ ModuleCat.ofHom S.subtype =
            ModuleCat.ofHom jH := by
        apply ModuleCat.hom_ext
        rfl
      have hmk :
          Subobject.mk (ModuleCat.ofHom jH) =
            Subobject.mk (ModuleCat.ofHom S.subtype) :=
        Subobject.mk_eq_mk_of_comm (ModuleCat.ofHom jH)
          (ModuleCat.ofHom S.subtype) e.toModuleIso heq
      have hnotS : ¬ EssentialSubmodule S := by
        intro hS
        apply hneq
        apply htriv H hHE
        have hcatS := (essentialSubmodule_iff_essentialExtension S).1 hS
        unfold EssentialExtension at hcatS ⊢
        rcases hcatS with ⟨hmono, hess⟩
        have := hmono
        refine ⟨inferInstance, ?_⟩
        intro P hP
        rw [hmk]
        exact hess P hP
      have hKexists : ∃ K : Submodule R H, K ≠ ⊥ ∧ S ⊓ K = ⊥ := by
        by_contra hK
        apply hnotS
        intro K hKne hzero
        apply hK
        exact ⟨K, hKne, hzero⟩
      obtain ⟨K, hKne, hSK⟩ := hKexists
      let T : Submodule R H := S ⊔ K
      let ST : Submodule R T := Submodule.comap T.subtype S
      let KT : Submodule R T := Submodule.comap T.subtype K
      have hSTKT : ST ⊓ KT = ⊥ := by
        apply le_antisymm
        · intro z hz
          rw [Submodule.mem_inf] at hz
          have hzSK : (z : H) ∈ S ⊓ K := ⟨hz.1, hz.2⟩
          have hz0 : (z : H) = 0 := by
            apply (Submodule.mem_bot R).mp
            rw [← hSK]
            exact hzSK
          apply (Submodule.mem_bot R).mpr
          exact Subtype.ext hz0
        · exact bot_le
      have hSTKT_top : ST ⊔ KT = ⊤ := by
        apply top_unique
        intro z hz
        rcases Submodule.mem_sup.mp z.property with ⟨s, hs, k, hk, hsk⟩
        have hsT : (⟨s, Submodule.mem_sup_left hs⟩ : T) ∈ ST := hs
        have hkT : (⟨k, Submodule.mem_sup_right hk⟩ : T) ∈ KT := hk
        have hsum :
            (⟨s, Submodule.mem_sup_left hs⟩ : T) +
                ⟨k, Submodule.mem_sup_right hk⟩ = z := by
          apply Subtype.ext
          exact hsk
        rw [← hsum]
        exact Submodule.add_mem_sup hsT hkT
      let hcomp : IsCompl ST KT :=
        ⟨disjoint_iff.mpr hSTKT, codisjoint_iff.mpr hSTKT_top⟩
      let jT : E →ₗ[R] T :=
        jH.codRestrict T (fun e => Submodule.mem_sup_left (jH.mem_range_self e))
      let jTS : E →ₗ[R] ST :=
        jT.codRestrict ST (fun e => jH.mem_range_self e)
      have hjTS : Function.Injective jTS := by
        intro x y hxy
        apply hjH
        exact congrArg (fun z : ST => (z : H)) hxy
      have hjTS_surj : Function.Surjective jTS := by
        intro z
        rcases z.property with hzS
        rcases hzS with ⟨e, he⟩
        refine ⟨e, ?_⟩
        apply Subtype.ext
        apply Subtype.ext
        exact he
      let eT : E ≃ₗ[R] ST := LinearEquiv.ofBijective jTS ⟨hjTS, hjTS_surj⟩
      let p : T →ₗ[R] ST := ST.projectionOnto KT hcomp
      let q : T →ₗ[R] E := eT.symm.toLinearMap.comp p
      have hqj : ∀ e, q (jT e) = e := by
        intro e0
        have he0 : jT e0 ∈ ST := jH.mem_range_self e0
        calc
          q (jT e0) = eT.symm (p (jT e0)) := rfl
          _ = eT.symm (jTS e0) := by
            rw [Submodule.projectionOnto_apply_of_mem_left hcomp he0]
            rfl
          _ = e0 := eT.symm_apply_apply e0
      let ψH : Y →ₗ[R] H :=
        ψ.codRestrict H (fun y => Submodule.mem_sup_right (ψ.mem_range_self y))
      let Mnew : Submodule R Y := Submodule.comap ψH T
      let ψT : Mnew →ₗ[R] T :=
        (ψH.comp Mnew.subtype).codRestrict T (fun y => y.property)
      let gnew : Mnew →ₗ[R] E := q.comp ψT
      have haM : a.domain ≤ Mnew := by
        intro y hy
        change ψH y ∈ T
        have hψy := hψ ⟨y, hy⟩
        have hψy' : ψH y = jH (ga ⟨y, hy⟩) := by
          apply Subtype.ext
          change ψ y = E.subtype (ga ⟨y, hy⟩)
          simpa [LinearMap.comp_apply] using hψy
        rw [hψy']
        exact Submodule.mem_sup_left (jH.mem_range_self _)
      have hga_new : ∀ y : a.domain,
          gnew ⟨y, haM y.property⟩ = ga y := by
        intro y
        have hψy : ψT ⟨y, haM y.property⟩ = jT (ga y) := by
          apply Subtype.ext
          apply Subtype.ext
          change ψ (y : Y) = E.subtype (ga y)
          simpa [LinearMap.comp_apply] using hψ y
        calc
          gnew ⟨y, haM y.property⟩ = q (ψT ⟨y, haM y.property⟩) := rfl
          _ = q (jT (ga y)) := by rw [hψy]
          _ = ga y := hqj _
      let anew : Module.Baer.ExtensionOf i g :=
        { domain := Mnew
          toFun := gnew
          le := by
            intro y hy
            rcases hy with ⟨x, rfl⟩
            exact haM (a.le ⟨x, rfl⟩)
          is_extension := by
            intro x
            have hix : i x ∈ a.domain := a.le ⟨x, rfl⟩
            change g x = gnew
              ⟨i x, haM hix⟩
            calc
              g x = ga ⟨i x, hix⟩ := by simpa [ga] using a.is_extension x
              _ = gnew ⟨i x, haM hix⟩ := (hga_new ⟨i x, hix⟩).symm }
      have ha_le : a ≤ anew := by
        refine ⟨haM, ?_⟩
        intro x y hxy
        have hxy' : y = ⟨x, haM x.property⟩ := by
          apply Subtype.ext
          exact hxy.symm
        subst y
        exact (hga_new x).symm
      have hmax : anew = a := by
        simpa [a] using Module.Baer.extensionOfMax_is_max i g anew ha_le
      have hdom : Mnew = a.domain :=
        congrArg (fun z : Module.Baer.ExtensionOf i g => z.domain) hmax
      obtain ⟨k, hkK, hk0⟩ := K.ne_bot_iff.mp hKne
      have hkH : (k : I) ∈ E ⊔ LinearMap.range ψ := k.property
      rcases Submodule.mem_sup.mp hkH with ⟨eI, heI, zI, hzI, hk_eq⟩
      rcases hzI with ⟨y, hyψ⟩
      let e0 : E := ⟨eI, heI⟩
      have hψTmem : ψH y ∈ T := by
        have heq : ψH y = k - jH e0 := by
          apply Subtype.ext
          change ψ y = (k : I) - eI
          rw [hyψ]
          apply (eq_sub_iff_add_eq).2
          simpa [add_comm] using hk_eq
        rw [heq]
        apply T.sub_mem
        · exact Submodule.mem_sup_right hkK
        · exact Submodule.mem_sup_left (jH.mem_range_self e0)
      have hyM : y ∈ Mnew := hψTmem
      have hyD : y ∈ a.domain := hdom ▸ hyM
      have hψyE : ψ y ∈ E := by
        have h := hψ ⟨y, hyD⟩
        have h' : ψ y = E.subtype (ga ⟨y, hyD⟩) := by
          simpa [LinearMap.comp_apply] using h
        rw [h']
        exact (ga ⟨y, hyD⟩).property
      have hkE : (k : I) ∈ E := by
        rw [← hk_eq, ← hyψ]
        exact E.add_mem heI hψyE
      have hkS : k ∈ S := by
        refine ⟨⟨k, hkE⟩, ?_⟩
        rfl
      have hk0' : k = 0 := by
        apply (Submodule.mem_bot R).mp
        rw [← hSK]
        exact ⟨hkS, hkK⟩
      exact (hk0 hk0').elim
  have hEcat : CategoryTheory.Injective (ModuleCat.of R E) := by
    constructor
    intro X Y g f hf
    have hf_inj : Function.Injective f.hom :=
      (ModuleCat.mono_iff_injective f).mp hf
    obtain ⟨h, hh⟩ := hE_module.out f.hom hf_inj g.hom
    refine ⟨ModuleCat.ofHom h, ?_⟩
    apply ModuleCat.hom_ext
    ext x
    simpa using hh x
  let fE : (M : Type v) →ₗ[R] E :=
    j.codRestrict E (fun m => hEGood.1 (show j m ∈ J from ⟨m, rfl⟩))
  let f : M ⟶ ModuleCat.of R E := ModuleCat.ofHom fE
  have hRangef : EssentialSubmodule (LinearMap.range fE) := by
    apply (essentialSubmodule_iff_smul _).2
    intro x hx0
    let U : Submodule R I := Submodule.span R ({(x : I)} : Set I)
    have hUE : U ≤ E := by
      rw [Submodule.span_le]
      intro z hz
      rcases Set.mem_singleton_iff.mp hz with rfl
      exact x.property
    have hUne : U ≠ ⊥ := by
      rw [Submodule.ne_bot_iff]
      have hxI0 : (x : I) ≠ 0 := by
        intro hxI
        apply hx0
        exact Subtype.ext hxI
      exact ⟨(x : I), Submodule.mem_span_singleton_self (x : I), hxI0⟩
    obtain ⟨z, hz, hz0⟩ :=
      (J ⊓ U).ne_bot_iff.mp (hEGood.2 U hUE hUne)
    rcases hz.1 with ⟨m, hm⟩
    have hzU : z ∈ U := hz.2
    rw [Submodule.mem_span_singleton] at hzU
    rcases hzU with ⟨r, hr⟩
    refine ⟨r, ?_, ?_⟩
    · refine ⟨m, ?_⟩
      apply Subtype.ext
      calc
        (fE m : I) = j m := rfl
        _ = z := hm
        _ = r • (x : I) := hr.symm
    · intro hzero
      apply hz0
      rw [← hr]
      exact congrArg Subtype.val hzero
  have hfmono : Mono f := by
    apply (ModuleCat.mono_iff_injective f).mpr
    intro x y hxy
    apply hj
    exact congrArg Subtype.val hxy
  have hEssf : EssentialExtension f := by
    let : Mono f := hfmono
    let : Mono (ModuleCat.ofHom (LinearMap.range fE).subtype) :=
      ConcreteCategory.mono_of_injective _ Subtype.val_injective
    let e : (M : Type v) ≃ₗ[R] LinearMap.range fE :=
      LinearEquiv.ofBijective fE.rangeRestrict
        ⟨(LinearMap.injective_rangeRestrict_iff fE).2 (by
            intro x y hxy
            apply hj
            exact congrArg Subtype.val hxy),
          fE.surjective_rangeRestrict⟩
    have heq :
        e.toModuleIso.hom ≫ ModuleCat.ofHom (LinearMap.range fE).subtype = f := by
      apply ModuleCat.hom_ext
      rfl
    have hmk :
        Subobject.mk f =
          Subobject.mk (ModuleCat.ofHom (LinearMap.range fE).subtype) :=
      Subobject.mk_eq_mk_of_comm f (ModuleCat.ofHom (LinearMap.range fE).subtype)
        e.toModuleIso heq
    have hsub :=
      (essentialSubmodule_iff_essentialExtension (LinearMap.range fE)).1 hRangef
    unfold EssentialExtension at hsub ⊢
    refine ⟨hfmono, ?_⟩
    intro P hP
    rw [hmk]
    exact hsub.2 P hP
  exact ⟨ModuleCat.of R E, f, ⟨hEssf, hEcat⟩⟩

/-! The extension and uniqueness assertions are separated so that the map
chosen by extension remains available to the subsequent assertions. -/

/-- A map between the modules extends across their injective hulls. -/
theorem injective_hull_extend
    {R : Type u} [Ring R] {M N E E' : ModuleCat.{v} R}
    {f : M ⟶ E} {g : N ⟶ E'}
    (hf : InjectiveHull f) (hg : InjectiveHull g) (φ : M ⟶ N) :
    ∃ ψ : E ⟶ E', f ≫ ψ = φ ≫ g := by
  let : Mono f := hf.1.1
  let : CategoryTheory.Injective E' := hg.2
  exact Injective.factors (φ ≫ g) f

/-- The extension of a monomorphism is a monomorphism. -/
theorem injective_hull_extend_mono
    {R : Type u} [Ring R] {M N E E' : ModuleCat.{v} R}
    {f : M ⟶ E} {g : N ⟶ E'}
    (hf : InjectiveHull f) (hg : InjectiveHull g)
    (φ : M ⟶ N) (hφ : Mono φ) (ψ : E ⟶ E')
    (hψ : f ≫ ψ = φ ≫ g) : Mono ψ := by
  rcases hf with ⟨⟨hfmono, hfess⟩, _⟩
  rcases hg with ⟨⟨hgmono, _⟩, _⟩
  let S : Submodule R (E : Type v) := LinearMap.range f.hom
  let e : (M : Type v) ≃ₗ[R] S :=
    LinearEquiv.ofBijective f.hom.rangeRestrict
      ⟨(LinearMap.injective_rangeRestrict_iff f.hom).2
          (by
            intro x y hxy
            apply (ModuleCat.mono_iff_injective f).mp hfmono
            simpa using hxy),
        f.hom.surjective_rangeRestrict⟩
  have heq : e.toModuleIso.hom ≫ ModuleCat.ofHom S.subtype = f := by
    apply ModuleCat.hom_ext
    rfl
  have hmk :
      Subobject.mk f = Subobject.mk (ModuleCat.ofHom S.subtype) :=
    Subobject.mk_eq_mk_of_comm f (ModuleCat.ofHom S.subtype) e.toModuleIso heq
  have hEssS : EssentialSubmodule S := by
    apply (essentialSubmodule_iff_essentialExtension S).2
    unfold EssentialExtension
    have hSmono : Mono (ModuleCat.ofHom S.subtype) :=
      ConcreteCategory.mono_of_injective _ Subtype.val_injective
    refine ⟨hSmono, ?_⟩
    intro P hP
    rw [← hmk]
    exact hfess P hP
  apply (ModuleCat.mono_iff_injective ψ).mpr
  intro x y hxy
  have hzψ : ψ.hom (x - y) = 0 := by
    rw [map_sub, hxy, sub_self]
  by_contra hxy0
  have hdiff0 : x - y ≠ 0 := sub_ne_zero.mpr hxy0
  obtain ⟨r, hrS, hr0⟩ :=
    (essentialSubmodule_iff_smul S).1 hEssS (x - y) hdiff0
  rcases hrS with ⟨m, hm⟩
  have hfmzero : ψ.hom (f.hom m) = 0 := by
    rw [hm, map_smul, hzψ, smul_zero]
  have hφmzero : φ.hom m = 0 := by
    apply (ModuleCat.mono_iff_injective g).mp hgmono
    have hzero : (φ ≫ g).hom m = 0 := by
      calc
        (φ ≫ g).hom m = (f ≫ ψ).hom m := by rw [hψ.symm]
        _ = ψ.hom (f.hom m) := rfl
        _ = 0 := hfmzero
    simpa using hzero
  have hmzero : m = 0 := by
    apply (ModuleCat.mono_iff_injective φ).mp hφ
    simpa using hφmzero
  apply hr0
  rw [← hm, hmzero, map_zero]

/-- An extension of an essential monomorphism is an isomorphism. -/
theorem injective_hull_extend_isIso_of_essential
    {R : Type u} [Ring R] {M N E E' : ModuleCat.{v} R}
    {f : M ⟶ E} {g : N ⟶ E'}
    (hf : InjectiveHull f) (hg : InjectiveHull g)
    (φ : M ⟶ N) (hφ : EssentialExtension φ) (ψ : E ⟶ E')
    (hψ : f ≫ ψ = φ ≫ g) : IsIso ψ := by
  have range_essential :
      ∀ (A B : ModuleCat.{v} R) (u : A ⟶ B), EssentialExtension u →
        EssentialSubmodule (LinearMap.range u.hom) :=
    fun A B u hu => by
    let : Mono u := hu.1
    let : Mono (ModuleCat.ofHom (LinearMap.range u.hom).subtype) :=
      ConcreteCategory.mono_of_injective _ Subtype.val_injective
    let S : Submodule R (B : Type v) := LinearMap.range u.hom
    let e : (A : Type v) ≃ₗ[R] S :=
      LinearEquiv.ofBijective u.hom.rangeRestrict
        ⟨(LinearMap.injective_rangeRestrict_iff u.hom).2
            (by
              intro x y hxy
              apply (ModuleCat.mono_iff_injective u).mp hu.1
              simpa using hxy),
          u.hom.surjective_rangeRestrict⟩
    have heq : e.toModuleIso.hom ≫ ModuleCat.ofHom S.subtype = u := by
      apply ModuleCat.hom_ext
      rfl
    have hmk :
        Subobject.mk u = Subobject.mk (ModuleCat.ofHom S.subtype) :=
      Subobject.mk_eq_mk_of_comm u (ModuleCat.ofHom S.subtype) e.toModuleIso heq
    apply (essentialSubmodule_iff_essentialExtension S).2
    unfold EssentialExtension
    have hSmono : Mono (ModuleCat.ofHom S.subtype) :=
      ConcreteCategory.mono_of_injective _ Subtype.val_injective
    refine ⟨hSmono, ?_⟩
    intro P hP
    rw [← hmk]
    exact hu.2 P hP
  have hφmono : Mono φ := hφ.1
  have hψmono :=
    injective_hull_extend_mono hf hg φ hφmono ψ hψ
  have hG : EssentialSubmodule (LinearMap.range g.hom) :=
    range_essential N E' g hg.1
  have hF : EssentialSubmodule (LinearMap.range φ.hom) :=
    range_essential M N φ hφ
  have hRangePsi : EssentialSubmodule (LinearMap.range ψ.hom) := by
    apply (essentialSubmodule_iff_smul _).2
    intro y hy
    obtain ⟨a, haG, haG0⟩ :=
      (essentialSubmodule_iff_smul (LinearMap.range g.hom)).1 hG y hy
    rcases haG with ⟨n, hn⟩
    have hn0 : n ≠ 0 := by
      intro hn0
      apply haG0
      rw [← hn, hn0, map_zero]
    obtain ⟨b, hbF, hbF0⟩ :=
      (essentialSubmodule_iff_smul (LinearMap.range φ.hom)).1 hF n hn0
    rcases hbF with ⟨m, hm⟩
    have hmem : (b * a) • y ∈ LinearMap.range ψ.hom := by
      refine ⟨f.hom m, ?_⟩
      calc
        ψ.hom (f.hom m) = g.hom (φ.hom m) := by
          have h := congrArg (fun q : M ⟶ E' => q.hom m) hψ
          simpa using h
        _ = g.hom (b • n) := by rw [hm]
        _ = b • g.hom n := by rw [map_smul]
        _ = b • (a • y) := by rw [hn]
        _ = (b * a) • y := by rw [mul_smul]
    have hnonzero : (b * a) • y ≠ 0 := by
      intro hzero
      have hbn : g.hom (b • n) ≠ 0 := by
        intro hbnzero
        apply hbF0
        apply (ModuleCat.mono_iff_injective g).mp hg.1.1
        simpa using hbnzero
      apply hbn
      calc
        g.hom (b • n) = b • g.hom n := by rw [map_smul]
        _ = b • (a • y) := by rw [hn]
        _ = (b * a) • y := by rw [mul_smul]
        _ = 0 := hzero
    exact not_subset.mp fun a_1 => hnonzero (a_1 hmem)
  let : Mono ψ := hψmono
  let : CategoryTheory.Injective E := hf.2
  let ρ : E' ⟶ E := Injective.factorThru (𝟙 E) ψ
  have hρ : ψ ≫ ρ = 𝟙 E := by
    change ψ ≫ Injective.factorThru (𝟙 E) ψ = 𝟙 E
    exact Injective.comp_factorThru (𝟙 E) ψ
  have hker : LinearMap.ker ρ.hom = ⊥ := by
    apply (LinearMap.ker ρ.hom).eq_bot_iff.mpr
    intro y hy
    by_contra hy0
    obtain ⟨r, hrange, hr0⟩ :=
      (essentialSubmodule_iff_smul (LinearMap.range ψ.hom)).1 hRangePsi y hy0
    rcases hrange with ⟨x, hx⟩
    have hrho : ρ.hom (r • y) = 0 := by
      rw [map_smul, LinearMap.mem_ker.mp hy, smul_zero]
    have hx0 : x = 0 := by
      have hcomp : ρ.hom (ψ.hom x) = x := by
        have h := congrArg (fun q : E ⟶ E => q.hom x) hρ
        simpa using h
      rw [hx, hrho] at hcomp
      exact hcomp.symm
    apply hr0
    rw [← hx, hx0, map_zero]
  have hsurj : Function.Surjective ψ.hom := by
    intro y
    have hz : y - ψ.hom (ρ.hom y) ∈ LinearMap.ker ρ.hom := by
      rw [LinearMap.mem_ker]
      have hcomp : ρ.hom (ψ.hom (ρ.hom y)) = ρ.hom y := by
        have h := congrArg (fun q : E ⟶ E => q.hom (ρ.hom y)) hρ
        simpa using h
      rw [map_sub, hcomp, sub_self]
    have hz0 : y - ψ.hom (ρ.hom y) = 0 := by
      have : y - ψ.hom (ρ.hom y) ∈ (⊥ : Submodule R (E' : Type v)) := hker ▸ hz
      simpa using this
    exact ⟨ρ.hom y, (sub_eq_zero.mp hz0).symm⟩
  let e : (E : Type v) ≃ₗ[R] (E' : Type v) :=
    LinearEquiv.ofBijective ψ.hom
      ⟨by simpa using (ModuleCat.mono_iff_injective ψ).mp hψmono, hsurj⟩
  have heq : e.toModuleIso.hom = ψ := by
    apply ModuleCat.hom_ext
    rfl
  rw [← heq]
  infer_instance

/-- If the map on modules is an isomorphism, so is its extension. -/
theorem injective_hull_extend_isIso_of_isIso
    {R : Type u} [Ring R] {M N E E' : ModuleCat.{v} R}
    {f : M ⟶ E} {g : N ⟶ E'}
    (hf : InjectiveHull f) (hg : InjectiveHull g)
    (φ : M ⟶ N) [IsIso φ] (ψ : E ⟶ E')
    (hψ : f ≫ ψ = φ ≫ g) : IsIso ψ := by
  have hφess : EssentialExtension φ := by
    unfold EssentialExtension
    refine ⟨inferInstance, ?_⟩
    intro P hP
    simpa [(Subobject.isIso_iff_mk_eq_top φ).mp inferInstance] using hP
  exact injective_hull_extend_isIso_of_essential hf hg φ hφess ψ hψ

/-- An injective module containing the source splits off the hull. -/
theorem injective_hull_split
    {R : Type u} [Ring R] {M E I : ModuleCat.{v} R}
      {f : M ⟶ E} {h : M ⟶ I}
    (hf : InjectiveHull f) (hh : Mono h)
    (hI : CategoryTheory.Injective I) :
    ∃ (I' : ModuleCat.{v} R) (e : I ≅ E ⊞ I'),
      h ≫ e.hom ≫ biprod.fst = f := by
  have hid : InjectiveHull (𝟙 I) := by
    refine ⟨?_, hI⟩
    unfold EssentialExtension
    refine ⟨inferInstance, ?_⟩
    intro P hP
    simpa [(Subobject.isIso_iff_mk_eq_top (𝟙 I)).mp inferInstance] using hP
  obtain ⟨α, hα⟩ := injective_hull_extend hf hid h
  have hαmono : Mono α := injective_hull_extend_mono hf hid h hh α hα
  let ρ : I ⟶ E :=
    @Injective.factorThru (ModuleCat.{v} R) _ E E I hf.2 (𝟙 E) α hαmono
  have hρα : α ≫ ρ = 𝟙 E := by
    change α ≫
        @Injective.factorThru (ModuleCat.{v} R) _ E E I hf.2 (𝟙 E) α hαmono = 𝟙 E
    exact @Injective.comp_factorThru (ModuleCat.{v} R) _ E E I hf.2 (𝟙 E) α hαmono
  have h_eq : h = f ≫ α := by
    simpa using hα.symm
  let S : ShortComplex (ModuleCat.{v} R) :=
    ShortComplex.mk α (cokernel.π α) (by simp)
  have hS : S.Exact := by
    dsimp [S]
    exact ShortComplex.exact_cokernel α
  let s : S.Splitting :=
    ShortComplex.Splitting.ofExactOfRetraction S hS ρ hρα (by infer_instance)
  refine ⟨cokernel α, s.isoBinaryBiproduct, ?_⟩
  change h ≫ biprod.lift ρ (cokernel.π α) ≫ biprod.fst = f
  rw [biprod.lift_fst, h_eq, Category.assoc, hρα, Category.comp_id]

/-- Injective hulls of a fixed module are isomorphic. -/
theorem injective_hull_unique_up_to_iso
    {R : Type u} [Ring R] {M E E' : ModuleCat.{v} R}
    {f : M ⟶ E} {g : M ⟶ E'}
    (hf : InjectiveHull f) (hg : InjectiveHull g) :
    Nonempty (E ≅ E') := by
  obtain ⟨ψ, hψ⟩ := injective_hull_extend hf hg (𝟙 M)
  let : IsIso ψ :=
    injective_hull_extend_isIso_of_isIso hf hg (𝟙 M) ψ hψ
  exact ⟨asIso ψ⟩

/-! The domain example uses the standard fraction-field embedding. -/

/-- The canonical module map from a domain to its fraction field. -/
def fractionFieldModuleMap
    {R K : Type u} [CommRing R] [Field K] [Algebra R K]
    [IsFractionRing R K] :
    ModuleCat.of R R ⟶ ModuleCat.of R K :=
  ModuleCat.ofHom (Algebra.linearMap R K)

/-- For a domain, its inclusion in the fraction field is an injective hull. -/
theorem fractionField_is_injective_hull
    {R K : Type u} [CommRing R] [IsDomain R] [Field K] [Algebra R K]
    [IsFractionRing R K] :
    InjectiveHull (fractionFieldModuleMap (R := R) (K := K)) := by
  have hKinj : Module.Injective R K := by
    apply Module.Baer.injective
    intro I g
    by_cases hI : I = ⊥
    · refine ⟨0, ?_⟩
      intro r hr
      have hr0 : r = 0 := by simpa [hI] using hr
      subst r
      symm
      change g ⟨0, hr⟩ = (0 : K)
      exact g.map_zero
    · obtain ⟨a, haI, ha0⟩ := I.ne_bot_iff.mp hI
      have haK : algebraMap R K a ≠ 0 := by
        intro haK
        apply ha0
        exact (IsFractionRing.injective R K) (by simpa using haK)
      let x : K := g ⟨a, haI⟩ / algebraMap R K a
      refine ⟨LinearMap.toSpanSingleton R K x, ?_⟩
      intro r hr
      have hgr : algebraMap R K a * g ⟨r, hr⟩ =
          algebraMap R K r * g ⟨a, haI⟩ := by
        calc
          algebraMap R K a * g ⟨r, hr⟩ =
              g (a • (⟨r, hr⟩ : I)) := by
                rw [map_smul, Algebra.smul_def]
          _ = g (r • (⟨a, haI⟩ : I)) := by
                congr 1
                ext
                simp [mul_comm]
          _ = algebraMap R K r * g ⟨a, haI⟩ := by
                rw [map_smul, Algebra.smul_def]
      apply (mul_left_cancel₀ haK)
      change algebraMap R K a * (r • x) =
        algebraMap R K a * g ⟨r, hr⟩
      rw [Algebra.smul_def]
      dsimp [x]
      calc
        algebraMap R K a *
              (algebraMap R K r * (g ⟨a, haI⟩ / algebraMap R K a)) =
            algebraMap R K r *
              (algebraMap R K a * (g ⟨a, haI⟩ / algebraMap R K a)) := by
                ac_rfl
        _ = algebraMap R K r * g ⟨a, haI⟩ := by
                rw [mul_div_cancel₀ _ haK]
        _ = algebraMap R K a * g ⟨r, hr⟩ := hgr.symm
  let S : Submodule R K := LinearMap.range (Algebra.linearMap R K)
  have hS : EssentialSubmodule S := by
    apply (essentialSubmodule_iff_smul S).2
    intro y hy
    obtain ⟨a, b, hb, hyab⟩ := IsFractionRing.div_surjective R y
    have hbK : algebraMap R K b ≠ 0 := by
      intro hbK
      apply (mem_nonZeroDivisors_iff_ne_zero.mp hb)
      exact (IsFractionRing.injective R K) (by simpa using hbK)
    refine ⟨b, ?_, ?_⟩
    · refine ⟨a, ?_⟩
      change algebraMap R K a = b • y
      rw [← hyab, Algebra.smul_def, mul_div_cancel₀ _ hbK]
    · rw [Algebra.smul_def, ← hyab, mul_div_cancel₀ _ hbK]
      intro haK
      apply hy
      rw [← hyab, haK, zero_div]
  have hmono : Mono (fractionFieldModuleMap (R := R) (K := K)) := by
    apply (ModuleCat.mono_iff_injective _).mpr
    change Function.Injective (Algebra.linearMap R K)
    exact IsFractionRing.injective R K
  let : Mono (fractionFieldModuleMap (R := R) (K := K)) := hmono
  let : Mono (ModuleCat.ofHom S.subtype) :=
    ConcreteCategory.mono_of_injective _ Subtype.val_injective
  let e : R ≃ₗ[R] S :=
    LinearEquiv.ofBijective (Algebra.linearMap R K).rangeRestrict
      ⟨(LinearMap.injective_rangeRestrict_iff (Algebra.linearMap R K)).2
          (IsFractionRing.injective R K),
        (Algebra.linearMap R K).surjective_rangeRestrict⟩
  have heq : e.toModuleIso.hom ≫ ModuleCat.ofHom S.subtype =
      fractionFieldModuleMap (R := R) (K := K) := by
    apply ModuleCat.hom_ext
    rfl
  have hmk :
      Subobject.mk (fractionFieldModuleMap (R := R) (K := K)) =
        Subobject.mk (ModuleCat.ofHom S.subtype) :=
    Subobject.mk_eq_mk_of_comm (fractionFieldModuleMap (R := R) (K := K))
      (ModuleCat.ofHom S.subtype) e.toModuleIso heq
  have hEss : EssentialExtension (fractionFieldModuleMap (R := R) (K := K)) := by
    unfold EssentialExtension
    have hsub := (essentialSubmodule_iff_essentialExtension S).1 hS
    unfold EssentialExtension at hsub
    refine ⟨hmono, ?_⟩
    exact fun P hP => by
      rw [hmk]
      exact hsub.2 P hP
  let : Module.Injective R K := hKinj
  exact ⟨hEss, Module.injective_object_of_injective_module R K⟩

/-! ## Indecomposable injectives -/
private theorem exists_injective_hull_in_injective
    {R : Type u} [Ring R] (I₀ : ModuleCat.{v} R)
    (hI : CategoryTheory.Injective I₀)
    (M : ModuleCat.{v} R) (j₀ : M ⟶ I₀) (hj₀ : Mono j₀) :
    ∃ (E : ModuleCat.{v} R) (f : M ⟶ E), InjectiveHull f := by
  let : CategoryTheory.Injective I₀ := hI
  let I : Type v := (I₀ : Type v)
  let : Module.Injective R I :=
    Module.injective_module_of_injective_object R (I₀ : Type v)
  let j : (M : Type v) →ₗ[R] I := j₀.hom
  have hj : Function.Injective j :=
    (ModuleCat.mono_iff_injective j₀).mp hj₀
  let J : Submodule R I := LinearMap.range j
  let Good : Submodule R I → Prop := fun E =>
    J ≤ E ∧ ∀ T : Submodule R I, T ≤ E → T ≠ ⊥ → J ⊓ T ≠ ⊥
  have hJGood : Good J := by
    refine ⟨le_rfl, ?_⟩
    intro T hTJ hTne
    rw [inf_eq_right.mpr hTJ]
    exact hTne
  have range_essential :
      ∀ (A B : ModuleCat.{v} R) (u : A ⟶ B), EssentialExtension u →
        EssentialSubmodule (LinearMap.range u.hom) := by
    intro A B u hu
    let : Mono u := hu.1
    let : Mono (ModuleCat.ofHom (LinearMap.range u.hom).subtype) :=
      ConcreteCategory.mono_of_injective _ Subtype.val_injective
    let S : Submodule R (B : Type v) := LinearMap.range u.hom
    let e : (A : Type v) ≃ₗ[R] S :=
      LinearEquiv.ofBijective u.hom.rangeRestrict
        ⟨(LinearMap.injective_rangeRestrict_iff u.hom).2
            (by
              intro x y hxy
              apply (ModuleCat.mono_iff_injective u).mp hu.1
              simpa using hxy),
          u.hom.surjective_rangeRestrict⟩
    have heq : e.toModuleIso.hom ≫ ModuleCat.ofHom S.subtype = u := by
      apply ModuleCat.hom_ext
      rfl
    have hmk :
        Subobject.mk u = Subobject.mk (ModuleCat.ofHom S.subtype) :=
      Subobject.mk_eq_mk_of_comm u (ModuleCat.ofHom S.subtype) e.toModuleIso heq
    apply (essentialSubmodule_iff_essentialExtension S).2
    unfold EssentialExtension
    have hSmono : Mono (ModuleCat.ofHom S.subtype) :=
      ConcreteCategory.mono_of_injective _ Subtype.val_injective
    refine ⟨hSmono, ?_⟩
    intro P hP
    rw [← hmk]
    exact hu.2 P hP
  have hupper :
      ∀ c ⊆ {E : Submodule R I | Good E},
        IsChain (· ≤ ·) c →
        ∀ y ∈ c, ∃ ub ∈ {E : Submodule R I | Good E},
          ∀ z ∈ c, z ≤ ub := by
    intro c hc hchain y hy
    let U : Submodule R I := sSup c
    have hcne : c.Nonempty := ⟨y, hy⟩
    refine ⟨U, ?_, ?_⟩
    · refine ⟨?_, ?_⟩
      · exact (hc hy).1.trans (le_sSup hy)
      · intro T hTU hTne
        obtain ⟨x, hxT, hx0⟩ := T.ne_bot_iff.mp hTne
        have hxU : x ∈ U := hTU hxT
        obtain ⟨E, hEc, hxE⟩ :=
          (Submodule.mem_sSup_of_directed hcne hchain.directedOn).mp hxU
        have hTE : T ⊓ E ≠ ⊥ := by
          intro hbot
          apply hx0
          have hxinf : x ∈ T ⊓ E := ⟨hxT, hxE⟩
          rw [hbot] at hxinf
          exact (Submodule.mem_bot R).mp hxinf
        obtain ⟨z, hz, hz0⟩ :=
          (J ⊓ (T ⊓ E)).ne_bot_iff.mp
            ((hc hEc).2 (T ⊓ E) inf_le_right hTE)
        refine (J ⊓ T).ne_bot_iff.mpr ⟨z, ?_, hz0⟩
        exact ⟨hz.1, hz.2.1⟩
    · intro z hz
      exact le_sSup hz
  obtain ⟨E, hJE, hEmax⟩ :=
    zorn_le_nonempty₀ {E : Submodule R I | Good E} hupper J hJGood
  have hEGood : Good E := hEmax.1
  have htriv :
      ∀ (E' : Submodule R I) (hEE' : E ≤ E'),
        EssentialExtension (ModuleCat.ofHom (E.inclusion hEE')) → E = E' := by
    intro E' hEE' hEss
    have hEssRange :
        EssentialSubmodule (LinearMap.range (E.inclusion hEE')) :=
      range_essential (ModuleCat.of R E) (ModuleCat.of R E')
        (ModuleCat.ofHom (E.inclusion hEE')) hEss
    have hGoodE' : Good E' := by
      refine ⟨hEGood.1.trans hEE', ?_⟩
      intro T hTE' hTne
      obtain ⟨x, hxT, hx0⟩ := T.ne_bot_iff.mp hTne
      let x' : E' := ⟨x, hTE' hxT⟩
      have hx'0 : x' ≠ 0 := by
        intro hx'
        apply hx0
        exact congrArg Subtype.val hx'
      obtain ⟨r, hrange, hr0⟩ :=
        (essentialSubmodule_iff_smul _).1 hEssRange x' hx'0
      rcases hrange with ⟨e, he⟩
      have he0 : (e : I) ≠ 0 := by
        intro he0
        apply hr0
        rw [← he]
        apply Subtype.ext
        simp [he0]
      let U : Submodule R I := Submodule.span R ({(e : I)} : Set I)
      have hUE : U ≤ E := by
        rw [Submodule.span_le]
        intro z hz
        rcases Set.mem_singleton_iff.mp hz with rfl
        exact e.property
      have hUne : U ≠ ⊥ := by
        rw [Submodule.ne_bot_iff]
        exact ⟨(e : I), Submodule.mem_span_singleton_self (e : I), he0⟩
      obtain ⟨z, hz, hz0⟩ :=
        (J ⊓ U).ne_bot_iff.mp (hEGood.2 U hUE hUne)
      have hzU : z ∈ U := hz.2
      rw [Submodule.mem_span_singleton] at hzU
      rcases hzU with ⟨s, hs⟩
      have he' : (e : I) = r • (x : I) := by
        exact congrArg (fun q : E' => (q : I)) he
      have hsr : (s * r) • (x : I) = z := by
        calc
          (s * r) • (x : I) = s • (r • (x : I)) := by rw [mul_smul]
          _ = s • (e : I) := by rw [← he']
          _ = z := hs
      refine (J ⊓ T).ne_bot_iff.mpr ⟨(s * r) • (x : I), ?_, ?_⟩
      · exact ⟨(hsr.symm ▸ hz).1, T.smul_mem (s * r) hxT⟩
      · rw [hsr]
        exact hz0
    exact hEmax.eq_of_le hGoodE' hEE'
  have hE_module : Module.Injective R E := by
    refine ⟨?_⟩
    intro X Y _ _ _ _ i hi g
    have : Fact (Function.Injective i) := ⟨hi⟩
    let a := Module.Baer.extensionOfMax i g
    let ga : a.domain →ₗ[R] E :=
      { toFun := fun x => a.toLinearPMap x
        map_add' := by
          intro x y
          rw [← LinearPMap.map_add]
        map_smul' := by
          intro r x
          rw [← LinearPMap.map_smul]
          rfl }
    obtain ⟨ψ, hψ⟩ :=
      (inferInstance : Module.Injective R I).out a.domain.subtype
        Subtype.val_injective (E.subtype.comp ga)
    by_cases hψE : ∀ y, ψ y ∈ E
    · let h : Y →ₗ[R] E := ψ.codRestrict E hψE
      refine ⟨h, ?_⟩
      intro x
      apply Subtype.ext
      change ψ (i x) = E.subtype (g x)
      have hψx :
          ψ (i x) = E.subtype (ga ⟨i x, a.le ⟨x, rfl⟩⟩) := by
        simpa using hψ ⟨i x, a.le ⟨x, rfl⟩⟩
      rw [hψx]
      simpa [ga] using congrArg E.subtype (a.is_extension x).symm
    · let H : Submodule R I := E ⊔ LinearMap.range ψ
      have hHE : E ≤ H := le_sup_left
      have hneq : E ≠ H := by
        intro hEH
        obtain ⟨y, hy⟩ := not_forall.mp hψE
        apply hy
        rw [hEH]
        exact Submodule.mem_sup_right (ψ.mem_range_self y)
      let jH : E →ₗ[R] H := E.inclusion hHE
      let S : Submodule R H := LinearMap.range jH
      have hjH : Function.Injective jH := Submodule.inclusion_injective hHE
      let e : E ≃ₗ[R] S :=
        LinearEquiv.ofBijective jH.rangeRestrict
          ⟨(LinearMap.injective_rangeRestrict_iff jH).2 hjH,
            jH.surjective_rangeRestrict⟩
      have : Mono (ModuleCat.ofHom (E.inclusion hHE)) :=
        ConcreteCategory.mono_of_injective _ (Submodule.inclusion_injective hHE)
      have : Mono (ModuleCat.ofHom jH) :=
        ConcreteCategory.mono_of_injective _ hjH
      have : Mono (ModuleCat.ofHom S.subtype) :=
        ConcreteCategory.mono_of_injective _ Subtype.val_injective
      have heq :
          e.toModuleIso.hom ≫ ModuleCat.ofHom S.subtype =
            ModuleCat.ofHom jH := by
        apply ModuleCat.hom_ext
        rfl
      have hmk :
          Subobject.mk (ModuleCat.ofHom jH) =
            Subobject.mk (ModuleCat.ofHom S.subtype) :=
        Subobject.mk_eq_mk_of_comm (ModuleCat.ofHom jH)
          (ModuleCat.ofHom S.subtype) e.toModuleIso heq
      have hnotS : ¬ EssentialSubmodule S := by
        intro hS
        apply hneq
        apply htriv H hHE
        have hcatS := (essentialSubmodule_iff_essentialExtension S).1 hS
        unfold EssentialExtension at hcatS ⊢
        rcases hcatS with ⟨hmono, hess⟩
        have := hmono
        refine ⟨inferInstance, ?_⟩
        intro P hP
        rw [hmk]
        exact hess P hP
      have hKexists : ∃ K : Submodule R H, K ≠ ⊥ ∧ S ⊓ K = ⊥ := by
        by_contra hK
        apply hnotS
        intro K hKne hzero
        apply hK
        exact ⟨K, hKne, hzero⟩
      obtain ⟨K, hKne, hSK⟩ := hKexists
      let T : Submodule R H := S ⊔ K
      let ST : Submodule R T := Submodule.comap T.subtype S
      let KT : Submodule R T := Submodule.comap T.subtype K
      have hSTKT : ST ⊓ KT = ⊥ := by
        apply le_antisymm
        · intro z hz
          rw [Submodule.mem_inf] at hz
          have hzSK : (z : H) ∈ S ⊓ K := ⟨hz.1, hz.2⟩
          have hz0 : (z : H) = 0 := by
            apply (Submodule.mem_bot R).mp
            rw [← hSK]
            exact hzSK
          apply (Submodule.mem_bot R).mpr
          exact Subtype.ext hz0
        · exact bot_le
      have hSTKT_top : ST ⊔ KT = ⊤ := by
        apply top_unique
        intro z hz
        rcases Submodule.mem_sup.mp z.property with ⟨s, hs, k, hk, hsk⟩
        have hsT : (⟨s, Submodule.mem_sup_left hs⟩ : T) ∈ ST := hs
        have hkT : (⟨k, Submodule.mem_sup_right hk⟩ : T) ∈ KT := hk
        have hsum :
            (⟨s, Submodule.mem_sup_left hs⟩ : T) +
                ⟨k, Submodule.mem_sup_right hk⟩ = z := by
          apply Subtype.ext
          exact hsk
        rw [← hsum]
        exact Submodule.add_mem_sup hsT hkT
      let hcomp : IsCompl ST KT :=
        ⟨disjoint_iff.mpr hSTKT, codisjoint_iff.mpr hSTKT_top⟩
      let jT : E →ₗ[R] T :=
        jH.codRestrict T (fun e => Submodule.mem_sup_left (jH.mem_range_self e))
      let jTS : E →ₗ[R] ST :=
        jT.codRestrict ST (fun e => jH.mem_range_self e)
      have hjTS : Function.Injective jTS := by
        intro x y hxy
        apply hjH
        exact congrArg (fun z : ST => (z : H)) hxy
      have hjTS_surj : Function.Surjective jTS := by
        intro z
        rcases z.property with hzS
        rcases hzS with ⟨e, he⟩
        refine ⟨e, ?_⟩
        apply Subtype.ext
        apply Subtype.ext
        exact he
      let eT : E ≃ₗ[R] ST := LinearEquiv.ofBijective jTS ⟨hjTS, hjTS_surj⟩
      let p : T →ₗ[R] ST := ST.projectionOnto KT hcomp
      let q : T →ₗ[R] E := eT.symm.toLinearMap.comp p
      have hqj : ∀ e, q (jT e) = e := by
        intro e0
        have he0 : jT e0 ∈ ST := jH.mem_range_self e0
        calc
          q (jT e0) = eT.symm (p (jT e0)) := rfl
          _ = eT.symm (jTS e0) := by
            rw [Submodule.projectionOnto_apply_of_mem_left hcomp he0]
            rfl
          _ = e0 := eT.symm_apply_apply e0
      let ψH : Y →ₗ[R] H :=
        ψ.codRestrict H (fun y => Submodule.mem_sup_right (ψ.mem_range_self y))
      let Mnew : Submodule R Y := Submodule.comap ψH T
      let ψT : Mnew →ₗ[R] T :=
        (ψH.comp Mnew.subtype).codRestrict T (fun y => y.property)
      let gnew : Mnew →ₗ[R] E := q.comp ψT
      have haM : a.domain ≤ Mnew := by
        intro y hy
        change ψH y ∈ T
        have hψy := hψ ⟨y, hy⟩
        have hψy' : ψH y = jH (ga ⟨y, hy⟩) := by
          apply Subtype.ext
          change ψ y = E.subtype (ga ⟨y, hy⟩)
          simpa [LinearMap.comp_apply] using hψy
        rw [hψy']
        exact Submodule.mem_sup_left (jH.mem_range_self _)
      have hga_new : ∀ y : a.domain,
          gnew ⟨y, haM y.property⟩ = ga y := by
        intro y
        have hψy : ψT ⟨y, haM y.property⟩ = jT (ga y) := by
          apply Subtype.ext
          apply Subtype.ext
          change ψ (y : Y) = E.subtype (ga y)
          simpa [LinearMap.comp_apply] using hψ y
        calc
          gnew ⟨y, haM y.property⟩ = q (ψT ⟨y, haM y.property⟩) := rfl
          _ = q (jT (ga y)) := by rw [hψy]
          _ = ga y := hqj _
      let anew : Module.Baer.ExtensionOf i g :=
        { domain := Mnew
          toFun := gnew
          le := by
            intro y hy
            rcases hy with ⟨x, rfl⟩
            exact haM (a.le ⟨x, rfl⟩)
          is_extension := by
            intro x
            have hix : i x ∈ a.domain := a.le ⟨x, rfl⟩
            change g x = gnew
              ⟨i x, haM hix⟩
            calc
              g x = ga ⟨i x, hix⟩ := by simpa [ga] using a.is_extension x
              _ = gnew ⟨i x, haM hix⟩ := (hga_new ⟨i x, hix⟩).symm }
      have ha_le : a ≤ anew := by
        refine ⟨haM, ?_⟩
        intro x y hxy
        have hxy' : y = ⟨x, haM x.property⟩ := by
          apply Subtype.ext
          exact hxy.symm
        subst y
        exact (hga_new x).symm
      have hmax : anew = a := by
        simpa [a] using Module.Baer.extensionOfMax_is_max i g anew ha_le
      have hdom : Mnew = a.domain :=
        congrArg (fun z : Module.Baer.ExtensionOf i g => z.domain) hmax
      obtain ⟨k, hkK, hk0⟩ := K.ne_bot_iff.mp hKne
      have hkH : (k : I) ∈ E ⊔ LinearMap.range ψ := k.property
      rcases Submodule.mem_sup.mp hkH with ⟨eI, heI, zI, hzI, hk_eq⟩
      rcases hzI with ⟨y, hyψ⟩
      let e0 : E := ⟨eI, heI⟩
      have hψTmem : ψH y ∈ T := by
        have heq : ψH y = k - jH e0 := by
          apply Subtype.ext
          change ψ y = (k : I) - eI
          rw [hyψ]
          apply (eq_sub_iff_add_eq).2
          simpa [add_comm] using hk_eq
        rw [heq]
        apply T.sub_mem
        · exact Submodule.mem_sup_right hkK
        · exact Submodule.mem_sup_left (jH.mem_range_self e0)
      have hyM : y ∈ Mnew := hψTmem
      have hyD : y ∈ a.domain := hdom ▸ hyM
      have hψyE : ψ y ∈ E := by
        have h := hψ ⟨y, hyD⟩
        have h' : ψ y = E.subtype (ga ⟨y, hyD⟩) := by
          simpa [LinearMap.comp_apply] using h
        rw [h']
        exact (ga ⟨y, hyD⟩).property
      have hkE : (k : I) ∈ E := by
        rw [← hk_eq, ← hyψ]
        exact E.add_mem heI hψyE
      have hkS : k ∈ S := by
        refine ⟨⟨k, hkE⟩, ?_⟩
        rfl
      have hk0' : k = 0 := by
        apply (Submodule.mem_bot R).mp
        rw [← hSK]
        exact ⟨hkS, hkK⟩
      exact (hk0 hk0').elim
  have hEcat : CategoryTheory.Injective (ModuleCat.of R E) := by
    constructor
    intro X Y g f hf
    have hf_inj : Function.Injective f.hom :=
      (ModuleCat.mono_iff_injective f).mp hf
    obtain ⟨h, hh⟩ := hE_module.out f.hom hf_inj g.hom
    refine ⟨ModuleCat.ofHom h, ?_⟩
    apply ModuleCat.hom_ext
    ext x
    simpa using hh x
  let fE : (M : Type v) →ₗ[R] E :=
    j.codRestrict E (fun m => hEGood.1 (show j m ∈ J from ⟨m, rfl⟩))
  let f : M ⟶ ModuleCat.of R E := ModuleCat.ofHom fE
  have hRangef : EssentialSubmodule (LinearMap.range fE) := by
    apply (essentialSubmodule_iff_smul _).2
    intro x hx0
    let U : Submodule R I := Submodule.span R ({(x : I)} : Set I)
    have hUE : U ≤ E := by
      rw [Submodule.span_le]
      intro z hz
      rcases Set.mem_singleton_iff.mp hz with rfl
      exact x.property
    have hUne : U ≠ ⊥ := by
      rw [Submodule.ne_bot_iff]
      have hxI0 : (x : I) ≠ 0 := by
        intro hxI
        apply hx0
        exact Subtype.ext hxI
      exact ⟨(x : I), Submodule.mem_span_singleton_self (x : I), hxI0⟩
    obtain ⟨z, hz, hz0⟩ :=
      (J ⊓ U).ne_bot_iff.mp (hEGood.2 U hUE hUne)
    rcases hz.1 with ⟨m, hm⟩
    have hzU : z ∈ U := hz.2
    rw [Submodule.mem_span_singleton] at hzU
    rcases hzU with ⟨r, hr⟩
    refine ⟨r, ?_, ?_⟩
    · refine ⟨m, ?_⟩
      apply Subtype.ext
      calc
        (fE m : I) = j m := rfl
        _ = z := hm
        _ = r • (x : I) := hr.symm
    · intro hzero
      apply hz0
      rw [← hr]
      exact congrArg Subtype.val hzero
  have hfmono : Mono f := by
    apply (ModuleCat.mono_iff_injective f).mpr
    intro x y hxy
    apply hj
    exact congrArg Subtype.val hxy
  have hEssf : EssentialExtension f := by
    let : Mono f := hfmono
    let : Mono (ModuleCat.ofHom (LinearMap.range fE).subtype) :=
      ConcreteCategory.mono_of_injective _ Subtype.val_injective
    let e : (M : Type v) ≃ₗ[R] LinearMap.range fE :=
      LinearEquiv.ofBijective fE.rangeRestrict
        ⟨(LinearMap.injective_rangeRestrict_iff fE).2 (by
            intro x y hxy
            apply hj
            exact congrArg Subtype.val hxy),
          fE.surjective_rangeRestrict⟩
    have heq :
        e.toModuleIso.hom ≫ ModuleCat.ofHom (LinearMap.range fE).subtype = f := by
      apply ModuleCat.hom_ext
      rfl
    have hmk :
        Subobject.mk f =
          Subobject.mk (ModuleCat.ofHom (LinearMap.range fE).subtype) :=
      Subobject.mk_eq_mk_of_comm f (ModuleCat.ofHom (LinearMap.range fE).subtype)
        e.toModuleIso heq
    have hsub :=
      (essentialSubmodule_iff_essentialExtension (LinearMap.range fE)).1 hRangef
    unfold EssentialExtension at hsub ⊢
    refine ⟨hfmono, ?_⟩
    intro P hP
    rw [hmk]
    exact hsub.2 P hP
  exact ⟨ModuleCat.of R E, f, hEssf, hEcat⟩


/- `CategoryTheory.Indecomposable` is Mathlib's canonical additive-category
form of the source's indecomposable-object definition. -/

/-- Every nonzero submodule of an indecomposable injective is essential. -/
theorem indecomposable_injective_submodule_hull
    {R : Type u} [Ring R] (E : ModuleCat.{v} R)
    (hE : CategoryTheory.Injective E)
    (hInd : CategoryTheory.Indecomposable E) :
    ∀ S : Submodule R (E : Type v), S ≠ ⊥ →
      InjectiveHull (ModuleCat.ofHom S.subtype) := by
  intro S hS
  let j : ModuleCat.of R S ⟶ E := ModuleCat.ofHom S.subtype
  have hj : Mono j :=
    ConcreteCategory.mono_of_injective _ Subtype.val_injective
  obtain ⟨H, f, hf⟩ :=
    exists_injective_hull_in_injective E hE (ModuleCat.of R S) j hj
  obtain ⟨I', e, he⟩ := injective_hull_split hf hj hE
  have hH : ¬ IsZero H := by
    intro hH
    obtain ⟨x, hxS, hx0⟩ := S.ne_bot_iff.mp hS
    let xs : S := ⟨x, hxS⟩
    have hfx : f.hom xs = 0 :=
      (ModuleCat.isZero_iff_subsingleton.mp hH).elim _ _
    have hxs : xs = 0 := by
      apply (ModuleCat.mono_iff_injective f).mp hf.1.1
      simpa using hfx
    apply hx0
    exact congrArg Subtype.val hxs
  obtain hH' | hI' := hInd.2 H I' e
  · exact (hH hH').elim
  let a : E ≅ H := e ≪≫ (isoBiprodZero hI').symm
  have hja : j ≫ a.hom = f := by
    simpa [a, Category.assoc] using he
  have haess : EssentialExtension a.inv := by
    unfold EssentialExtension
    refine ⟨inferInstance, ?_⟩
    intro P hP
    simpa [(Subobject.isIso_iff_mk_eq_top a.inv).mp inferInstance] using hP
  have hfaess : EssentialExtension (f ≫ a.inv) :=
    essentialExtension_trans f a.inv hf.1 haess
  have hfj : f ≫ a.inv = j := by
    calc
      f ≫ a.inv = (j ≫ a.hom) ≫ a.inv := by rw [hja]
      _ = j := by simp [Category.assoc]
  change InjectiveHull j
  exact ⟨hfj ▸ hfaess, hE⟩

/-- Any two nonzero submodules of an indecomposable injective meet nontrivially. -/
theorem indecomposable_injective_submodule_intersection
    {R : Type u} [Ring R] (E : ModuleCat.{v} R)
    (hE : CategoryTheory.Injective E)
    (hInd : CategoryTheory.Indecomposable E) :
    ∀ S T : Submodule R (E : Type v), S ≠ ⊥ → T ≠ ⊥ → S ⊓ T ≠ ⊥ := by
  intro S T hS hT
  exact
    ((essentialSubmodule_iff_essentialExtension S).2
      (indecomposable_injective_submodule_hull E hE hInd S hS).1) T hT

private theorem indecomposable_injective_end_isUnit_of_ker_eq_bot
    {R : Type u} [Ring R] (E : ModuleCat.{v} R)
    (hE : CategoryTheory.Injective E)
    (hInd : CategoryTheory.Indecomposable E)
    (φ : Module.End R (E : Type v))
    (hφ : LinearMap.ker φ = ⊥) :
    IsUnit φ := by
  have hφmono : Mono (ModuleCat.ofHom φ) :=
    (ModuleCat.mono_iff_injective _).mpr (LinearMap.ker_eq_bot.mp hφ)
  have hid : InjectiveHull (𝟙 E) := by
    refine ⟨?_, hE⟩
    unfold EssentialExtension
    refine ⟨inferInstance, ?_⟩
    intro P hP
    simpa [(Subobject.isIso_iff_mk_eq_top (𝟙 E)).mp inferInstance] using hP
  obtain ⟨I', e, he⟩ := injective_hull_split hid hφmono hE
  obtain hEzero | hI' := hInd.2 E I' e
  · exact (hInd.1 hEzero).elim
  let a : E ≅ E := e ≪≫ (isoBiprodZero hI').symm
  have hcomp : ModuleCat.ofHom φ ≫ a.hom = 𝟙 E := by
    simpa [a, Category.assoc] using he
  have hφeq : ModuleCat.ofHom φ = a.inv := by
    apply (cancel_mono a.hom).1
    simp [hcomp]
  apply (Module.End.isUnit_iff φ).2
  constructor
  · exact LinearMap.ker_eq_bot.mp hφ
  · intro y
    refine ⟨a.hom.hom y, ?_⟩
    have h := congrArg (fun q : E ⟶ E => q.hom (a.hom.hom y)) hφeq
    have ha := congrArg (fun q : E ⟶ E => q.hom y) a.hom_inv_id
    calc
      φ (a.hom.hom y) = a.inv.hom (a.hom.hom y) := by exact h
      _ = y := by exact ha

/-- The endomorphism ring of an indecomposable injective is local, with its
maximal ideal detected by nonzero kernels. -/
theorem indecomposable_injective_end_is_local
    {R : Type u} [Ring R] (E : ModuleCat.{v} R)
    (hE : CategoryTheory.Injective E)
    (hInd : CategoryTheory.Indecomposable E) :
    IsLocalRing (Module.End R (E : Type v)) ∧
      ∃ I : Ideal (Module.End R (E : Type v)),
        I.IsTwoSided ∧ I.IsMaximal ∧
          ∀ φ : Module.End R (E : Type v),
            φ ∈ I ↔ LinearMap.ker φ ≠ ⊥ := by
  let A := Module.End R (E : Type v)
  have hEne : ¬ IsZero E := hInd.1
  have hEsub : ¬ Subsingleton (E : Type v) := by
    intro h
    exact hEne (ModuleCat.isZero_of_subsingleton E)
  let : Nontrivial (E : Type v) :=
    not_subsingleton_iff_nontrivial.mp hEsub
  have hunit_iff (φ : A) : IsUnit φ ↔ LinearMap.ker φ = ⊥ := by
    constructor
    · intro hφ
      exact LinearMap.ker_eq_bot.mpr ((Module.End.isUnit_iff φ).mp hφ).1
    · intro hφ
      exact indecomposable_injective_end_isUnit_of_ker_eq_bot E hE hInd φ hφ
  let I : Ideal A :=
    { carrier := {φ | LinearMap.ker φ ≠ ⊥}
      zero_mem' := by
        simp [LinearMap.ker_zero]
      add_mem' := by
        intro φ ψ hφ hψ
        obtain ⟨x, hx, hx0⟩ :=
          (LinearMap.ker φ ⊓ LinearMap.ker ψ).ne_bot_iff.mp
            (indecomposable_injective_submodule_intersection E hE hInd
              (LinearMap.ker φ) (LinearMap.ker ψ) hφ hψ)
        refine (LinearMap.ker (φ + ψ)).ne_bot_iff.mpr ⟨x, ?_, hx0⟩
        apply LinearMap.mem_ker.mpr
        change φ x + ψ x = 0
        rw [LinearMap.mem_ker.mp hx.1, LinearMap.mem_ker.mp hx.2, add_zero]
      smul_mem' := by
        intro a φ hφ
        obtain ⟨x, hx, hx0⟩ := (LinearMap.ker φ).ne_bot_iff.mp hφ
        refine (LinearMap.ker (a • φ)).ne_bot_iff.mpr ⟨x, ?_, hx0⟩
        apply LinearMap.mem_ker.mpr
        change (a * φ) x = 0
        rw [Module.End.mul_apply, LinearMap.mem_ker.mp hx, map_zero] }
  have hI : I.IsTwoSided := by
    constructor
    intro φ ψ hφ
    by_cases hψ : LinearMap.ker ψ = ⊥
    · obtain ⟨x, hx, hx0⟩ := (LinearMap.ker φ).ne_bot_iff.mp hφ
      have hψunit : IsUnit ψ := (hunit_iff ψ).mpr hψ
      obtain ⟨y, hy⟩ := ((Module.End.isUnit_iff ψ).mp hψunit).2 x
      refine (LinearMap.ker (φ * ψ)).ne_bot_iff.mpr ⟨y, ?_, ?_⟩
      · apply LinearMap.mem_ker.mpr
        rw [Module.End.mul_apply, hy, LinearMap.mem_ker.mp hx]
      · intro hy0
        apply hx0
        rw [← hy]
        simpa using congrArg ψ hy0
    · obtain ⟨y, hy, hy0⟩ := (LinearMap.ker ψ).ne_bot_iff.mp hψ
      refine (LinearMap.ker (φ * ψ)).ne_bot_iff.mpr ⟨y, ?_, hy0⟩
      apply LinearMap.mem_ker.mpr
      rw [Module.End.mul_apply, LinearMap.mem_ker.mp hy]
      exact map_zero φ
  have hmax : I.IsMaximal := by
    rw [Ideal.isMaximal_iff]
    constructor
    · intro h1
      change LinearMap.ker (1 : A) ≠ ⊥ at h1
      exact h1 (LinearMap.ker_eq_bot.mpr (by intro x y hxy; exact hxy))
    · intro J φ hIJ hφJ hφ
      have hφunit : IsUnit φ := (hunit_iff φ).mpr (by
        by_contra hker
        apply hφJ
        change LinearMap.ker φ ≠ ⊥
        exact hker)
      exact (Ideal.unit_mul_mem_iff_mem J hφunit).mp (by simpa using hφ)
  have hlocal : IsLocalRing A := by
    refine ⟨?_⟩
    intro φ ψ hsum
    by_cases hφ : LinearMap.ker φ = ⊥
    · exact Or.inl ((hunit_iff φ).mpr hφ)
    by_cases hψ : LinearMap.ker ψ = ⊥
    · exact Or.inr ((hunit_iff ψ).mpr hψ)
    · exfalso
      obtain ⟨x, hx, hx0⟩ :=
        (LinearMap.ker φ ⊓ LinearMap.ker ψ).ne_bot_iff.mp
          (indecomposable_injective_submodule_intersection E hE hInd
            (LinearMap.ker φ) (LinearMap.ker ψ) hφ hψ)
      apply hx0
      have hxsum := congrArg (fun q : A => q x) hsum
      change φ x + ψ x = x at hxsum
      rw [LinearMap.mem_ker.mp hx.1, LinearMap.mem_ker.mp hx.2, zero_add] at hxsum
      exact hxsum.symm
  refine ⟨hlocal, I, hI, hmax, ?_⟩
  intro φ
  change LinearMap.ker φ ≠ ⊥ ↔ LinearMap.ker φ ≠ ⊥
  rfl

/- The zero divisors acting on an indecomposable injective form a prime ideal,
and the module is injective after localizing at that ideal. -/
def ModuleZeroDivisors (R M : Type*) [CommRing R] [AddCommGroup M]
    [Module R M] : Set R :=
  {r | ∃ x : M, x ≠ 0 ∧ r • x = 0}

private theorem injective_of_localization_action
    {R : Type u} [CommRing R] {S : Type u} [CommRing S]
    [Algebra R S] (T : Submonoid R) [IsLocalization T S]
    (M : Type v) [AddCommGroup M] [Module R M] [Module S M]
    [IsScalarTower R S M] (hM : Module.Injective R M) :
    Module.Injective S M := by
  refine ⟨?_⟩
  intro X Y _ _ _ _ f hf g
  let : Module R X := Module.compHom X (algebraMap R S)
  let : Module R Y := Module.compHom Y (algebraMap R S)
  let fR : X →ₗ[R] Y :=
    { toFun := f
      map_add' := f.map_add
      map_smul' := fun r x => f.map_smul _ _ }
  let gR : X →ₗ[R] M :=
    { toFun := g
      map_add' := g.map_add
      map_smul' := fun r x => by
        change g ((algebraMap R S r) • x) = r • g x
        rw [g.map_smul, algebraMap_smul S r] }
  obtain ⟨h, hh⟩ := hM.out fR (hf) gR
  let hS : Y →ₗ[S] M :=
    { toFun := h
      map_add' := h.map_add
      map_smul' := by
        intro z y
        obtain ⟨⟨r, s⟩, hz⟩ := IsLocalization.surj (R := R) T z
        apply (IsUnit.smul_left_cancel
          (@IsLocalization.map_units R _ T S _ _ _ s)).mp
        calc
          algebraMap R S (s : R) • h (z • y) = h (algebraMap R S (s : R) • (z • y)) := by
            rw [algebraMap_smul S (s : R)]
            exact (h.map_smul (s : R) _).symm
          _ = h ((z * algebraMap R S (s : R)) • y) := by
            congr 1
            rw [← mul_smul, mul_comm]
          _ = h ((algebraMap R S r) • y) := by rw [hz]
          _ = r • h y := h.map_smul r y
          _ = (algebraMap R S r) • h y := (algebraMap_smul S r (h y)).symm
          _ = (z * algebraMap R S (s : R)) • h y := by rw [hz]
          _ = algebraMap R S (s : R) • (z • h y) := by
            rw [mul_smul, smul_comm] }
  refine ⟨hS, ?_⟩
  exact fun x => by
    change h (f x) = g x
    simpa [fR, gR] using hh x

theorem indecomposable_injective_zero_divisors
    {R : Type u} [CommRing R] (E : ModuleCat.{v} R)
    (hE : CategoryTheory.Injective E)
    (hInd : CategoryTheory.Indecomposable E) :
    ∃ (p : Ideal R) (hp : p.IsPrime),
      (p : Set R) = ModuleZeroDivisors R (E : Type v) ∧
        letI := hp
        ∃ Eₚ : ModuleCat.{v} (Localization.AtPrime p),
            Nonempty
              (ModuleCat.of R (E : Type v) ≅
                (ModuleCat.restrictScalars (algebraMap R (Localization.AtPrime p))).obj Eₚ) ∧
            CategoryTheory.Injective Eₚ := by
  let A := Module.End R (E : Type v)
  obtain ⟨hlocal, I, hI, hmax, hmem⟩ :=
    indecomposable_injective_end_is_local E hE hInd
  let : IsLocalRing A := hlocal
  let : I.IsMaximal := hmax
  let p : Ideal R := I.comap (algebraMap R A)
  have hp : p.IsPrime := by
    constructor
    · intro htop
      have h1 : (1 : R) ∈ p := by simp [htop]
      have h1I : (1 : A) ∈ I := by simpa [p] using h1
      have hker : LinearMap.ker (1 : A) ≠ ⊥ := (hmem _).mp h1I
      exact hker (LinearMap.ker_eq_bot.mpr (by
        intro x y hxy
        exact hxy))
    · intro r s hrs
      change algebraMap R A (r * s) ∈ I at hrs
      by_cases hr : algebraMap R A r ∈ I
      · exact Or.inl (show r ∈ p from hr)
      · have hrker : LinearMap.ker (algebraMap R A r) = ⊥ := by
          by_contra hker
          exact hr ((hmem _).mpr hker)
        have hrun : IsUnit (algebraMap R A r) :=
          indecomposable_injective_end_isUnit_of_ker_eq_bot E hE hInd _ hrker
        have hsmem : algebraMap R A s ∈ I := by
          apply (Ideal.unit_mul_mem_iff_mem I hrun).mp
          simpa [map_mul] using hrs
        exact Or.inr (show s ∈ p from hsmem)
  refine ⟨p, hp, ?_, ?_⟩
  · ext r
    change algebraMap R A r ∈ I ↔ ∃ x : E, x ≠ 0 ∧ r • x = 0
    constructor
    · intro hr
      have hrker : LinearMap.ker (algebraMap R A r) ≠ ⊥ :=
        (hmem (algebraMap R A r)).mp hr
      obtain ⟨x, hx, hx0⟩ := (LinearMap.ker (algebraMap R A r)).ne_bot_iff.mp hrker
      refine ⟨x, hx0, ?_⟩
      simpa [A, Module.algebraMap_end_apply] using LinearMap.mem_ker.mp hx
    · rintro ⟨x, hx, hx0⟩
      apply (hmem (algebraMap R A r)).mpr
      apply (LinearMap.ker (algebraMap R A r)).ne_bot_iff.mpr
      exact ⟨x, LinearMap.mem_ker.mpr (by
        simpa [A, Module.algebraMap_end_apply] using hx0), hx⟩
  · let : p.IsPrime := hp
    let L := Localization.AtPrime p
    let g0 : R →+* A := algebraMap R A
    have hsunit : ∀ s : p.primeCompl, IsUnit (g0 (s : R)) := by
      intro s
      have hker : LinearMap.ker (g0 (s : R)) = ⊥ := by
        by_contra hker
        apply s.2
        change g0 (s : R) ∈ I
        exact (hmem _).mpr hker
      exact indecomposable_injective_end_isUnit_of_ker_eq_bot E hE hInd _ hker
    let Z := Subalgebra.center R A
    let g0z : R →+* Z := algebraMap R Z
    have hsunitZ : ∀ s : p.primeCompl, IsUnit (g0z (s : R)) := by
      intro s
      obtain ⟨u, hu⟩ := hsunit s
      have hu_center : ∀ a : A, a * (u : A) = (u : A) * a := by
        intro a
        rw [hu]
        exact (Algebra.commutes (R := R) (A := A) (s : R) a).symm
      have huinv_center : ∀ a : A,
          a * ((↑(u⁻¹ : Aˣ)) : A) = ((↑(u⁻¹ : Aˣ)) : A) * a := by
        intro a
        calc
          a * ((↑(u⁻¹ : Aˣ)) : A) =
              ((↑(u⁻¹ : Aˣ)) : A) * (u : A) *
                (a * ((↑(u⁻¹ : Aˣ)) : A)) := by
            simp
          _ = ((↑(u⁻¹ : Aˣ)) : A) * ((u : A) * a) *
                ((↑(u⁻¹ : Aˣ)) : A) := by
            simp only [mul_assoc]
          _ = ((↑(u⁻¹ : Aˣ)) : A) * (a * (u : A)) *
                ((↑(u⁻¹ : Aˣ)) : A) := by
            rw [hu_center]
          _ = ((↑(u⁻¹ : Aˣ)) : A) * a := by simp [mul_assoc]
      let uc : (Submonoid.center A)ˣ :=
        { val := ⟨(u : A), Submonoid.mem_center_iff.mpr hu_center⟩
          inv := ⟨(↑(u⁻¹ : Aˣ) : A), Submonoid.mem_center_iff.mpr huinv_center⟩
          val_inv := by
            apply Subtype.ext
            exact Units.val_inv u
          inv_val := by
            apply Subtype.ext
            exact Units.inv_val u }
      let uz : Zˣ :=
        { val := ⟨(uc : A), by
            rw [Subalgebra.mem_center_iff]
            exact Submonoid.mem_center_iff.mp uc.1.prop⟩
          inv := ⟨(↑(uc⁻¹) : A), by
            rw [Subalgebra.mem_center_iff]
            exact Submonoid.mem_center_iff.mp (uc⁻¹).1.prop⟩
          val_inv := by
            apply Subtype.ext
            change ((uc.val : Submonoid.center A) : A) *
                ((uc.inv : Submonoid.center A) : A) = 1
            have h := congrArg (fun z : Submonoid.center A => (z : A)) uc.val_inv
            convert h using 1 <;> rfl
          inv_val := by
            apply Subtype.ext
            change ((uc.inv : Submonoid.center A) : A) *
                ((uc.val : Submonoid.center A) : A) = 1
            have h := congrArg (fun z : Submonoid.center A => (z : A)) uc.inv_val
            convert h using 1 <;> rfl }
      refine ⟨uz, ?_⟩
      apply Subtype.ext
      simpa [uz, uc, g0z, g0] using hu
    let gL : L →+* A := Z.val.toRingHom.comp (IsLocalization.lift hsunitZ)
    have hgL : gL.comp (algebraMap R L) = g0 := by
      apply RingHom.ext
      intro r
      change Z.val ((IsLocalization.lift hsunitZ) (algebraMap R L r)) = g0 r
      rw [IsLocalization.lift_eq]
      rfl
    let : Module L (E : Type v) := Module.compHom (E : Type v) gL
    let : IsScalarTower R L (E : Type v) :=
      { smul_assoc := by
          intro r l x
          change (gL (r • l)) x = r • ((gL l) x)
          have hgr : gL (algebraMap R L r) = g0 r := DFunLike.congr_fun hgL r
          rw [Algebra.smul_def, map_mul, hgr]
          simp [g0, A, Module.End.mul_apply, Module.algebraMap_end_apply] }
    let : CategoryTheory.Injective (ModuleCat.of R (E : Type v)) := hE
    have hEM : Module.Injective R (E : Type v) :=
      Module.injective_module_of_injective_object R (E : Type v)
    have hEL : Module.Injective L (E : Type v) :=
      injective_of_localization_action p.primeCompl (E : Type v) hEM
    let : Module.Injective L (E : Type v) := hEL
    have hEcat : CategoryTheory.Injective (ModuleCat.of L (E : Type v)) :=
      Module.injective_object_of_injective_module L (E : Type v)
    refine ⟨ModuleCat.of L (E : Type v), ?_, hEcat⟩
    let f : ModuleCat.of R (E : Type v) ⟶
        (ModuleCat.restrictScalars (algebraMap R L)).obj (ModuleCat.of L (E : Type v)) :=
      ModuleCat.ofHom (X := ModuleCat.of R (E : Type v))
        (Y := (ModuleCat.restrictScalars (algebraMap R L)).obj (ModuleCat.of L (E : Type v)))
        { toFun := id
          map_add' := by intro x y; rfl
          map_smul' := by
            intro r x
            exact (algebraMap_smul L r x).symm }
    let fInv : (ModuleCat.restrictScalars (algebraMap R L)).obj (ModuleCat.of L (E : Type v)) ⟶
        ModuleCat.of R (E : Type v) :=
      ModuleCat.ofHom
        (X := (ModuleCat.restrictScalars (algebraMap R L)).obj (ModuleCat.of L (E : Type v)))
        (Y := ModuleCat.of R (E : Type v))
        { toFun := id
          map_add' := by intro x y; rfl
          map_smul' := by
            intro r x
            have hsmul :=
              ((ModuleCat.restrictScalars.smul_def'
                  (M := ModuleCat.of L (E : Type v)) (algebraMap R L) r (x : E)).trans
                (algebraMap_smul (M := (E : Type v)) L r x))
            convert congrArg (fun y => (y : E)) hsmul using 1; rfl }
    exact ⟨⟨f, fInv, by
      ext x
      change x = x
      exact rfl, by
      ext x
      change x = x
      exact rfl⟩⟩

/-! ## Prime residue fields and the Noetherian classification -/

/-- The quotient-to-residue-field map, viewed as an R-linear module map. -/
def residueFieldQuotientMap
    {R : Type u} [CommRing R] (p : Ideal R) [p.IsPrime] :
    ModuleCat.of R (R ⧸ p) ⟶ ModuleCat.of R p.ResidueField :=
  ModuleCat.ofHom
    ((Algebra.linearMap (R ⧸ p) p.ResidueField).restrictScalars R)

/-- The injective hull of R/p is indecomposable and is also the hull of the
residue field, over both R and the localization at p. -/
theorem prime_injective_hull_residue_field
    {R : Type u} [CommRing R] (p : Ideal R) [p.IsPrime]
    (E : ModuleCat.{u} R)
    (f : ModuleCat.of R (R ⧸ p) ⟶ E) (hf : InjectiveHull f) :
    CategoryTheory.Indecomposable E ∧
      (∃ g : ModuleCat.of R p.ResidueField ⟶ E,
        InjectiveHull g ∧ residueFieldQuotientMap p ≫ g = f) ∧
        ∃ Eₚ : ModuleCat.{u} (Localization.AtPrime p),
          Nonempty
              (E ≅
              (ModuleCat.restrictScalars (algebraMap R (Localization.AtPrime p))).obj Eₚ) ∧
            ∃ g : ModuleCat.of (Localization.AtPrime p) p.ResidueField ⟶ Eₚ,
              InjectiveHull g := by
  let q := residueFieldQuotientMap p
  have hqmono : Mono q := by
    apply (ModuleCat.mono_iff_injective _).mpr
    change Function.Injective (algebraMap (R ⧸ p) p.ResidueField)
    exact p.injective_algebraMap_quotient_residueField
  have hqess : EssentialExtension q := by
    let S : Submodule R p.ResidueField := LinearMap.range q.hom
    let e : (R ⧸ p) ≃ₗ[R] S :=
      LinearEquiv.ofBijective q.hom.rangeRestrict
        ⟨(LinearMap.injective_rangeRestrict_iff q.hom).2
            (ModuleCat.mono_iff_injective q |>.mp hqmono),
          q.hom.surjective_rangeRestrict⟩
    have hS : EssentialSubmodule S := by
      apply (essentialSubmodule_iff_smul S).2
      intro x hx
      obtain ⟨⟨a, b⟩, hab⟩ :=
        IsLocalization.surj (R := R ⧸ p) (nonZeroDivisors (R ⧸ p)) x
      obtain ⟨s, hs⟩ := Ideal.Quotient.mk_surjective (b : R ⧸ p)
      refine ⟨s, ?_, ?_⟩
      · refine ⟨a, ?_⟩
        dsimp [q, residueFieldQuotientMap]
        change algebraMap (R ⧸ p) p.ResidueField a = s • x
        rw [Algebra.smul_def]
        rw [← Ideal.algebraMap_quotient_residueField_mk]
        rw [hs]
        simpa [mul_comm] using hab.symm
      · have hb0 : algebraMap (R ⧸ p) p.ResidueField (b : R ⧸ p) ≠ 0 :=
          map_ne_zero_of_mem_nonZeroDivisors _ p.injective_algebraMap_quotient_residueField b.2
        have hprod : x * algebraMap (R ⧸ p) p.ResidueField (b : R ⧸ p) ≠ 0 :=
          mul_ne_zero hx hb0
        simpa [Algebra.smul_def, ← IsScalarTower.algebraMap_apply R (R ⧸ p)
          p.ResidueField, ← hs, mul_comm] using hprod
    let : Mono (ModuleCat.ofHom S.subtype) :=
      ConcreteCategory.mono_of_injective _ Subtype.val_injective
    have hcat : EssentialExtension (ModuleCat.ofHom S.subtype) :=
      (essentialSubmodule_iff_essentialExtension S).1 hS
    have heq : e.toModuleIso.hom ≫ ModuleCat.ofHom S.subtype = q := by
      apply ModuleCat.hom_ext
      rfl
    have hmk :
        Subobject.mk q = Subobject.mk (ModuleCat.ofHom S.subtype) :=
      Subobject.mk_eq_mk_of_comm q (ModuleCat.ofHom S.subtype) e.toModuleIso heq
    unfold EssentialExtension at hcat ⊢
    refine ⟨hqmono, ?_⟩
    intro P hP
    rw [hmk]
    exact hcat.2 P hP
  have range_essential :
      ∀ (A B : ModuleCat.{u} R) (u : A ⟶ B), EssentialExtension u →
        EssentialSubmodule (LinearMap.range u.hom) := by
    intro A B u hu
    let : Mono u := hu.1
    let : Mono (ModuleCat.ofHom (LinearMap.range u.hom).subtype) :=
      ConcreteCategory.mono_of_injective _ Subtype.val_injective
    let S : Submodule R (B : Type u) := LinearMap.range u.hom
    let e : (A : Type u) ≃ₗ[R] S :=
      LinearEquiv.ofBijective u.hom.rangeRestrict
        ⟨(LinearMap.injective_rangeRestrict_iff u.hom).2
            (ModuleCat.mono_iff_injective u |>.mp hu.1),
          u.hom.surjective_rangeRestrict⟩
    have heq : e.toModuleIso.hom ≫ ModuleCat.ofHom S.subtype = u := by
      apply ModuleCat.hom_ext
      rfl
    have hmk :
        Subobject.mk u = Subobject.mk (ModuleCat.ofHom S.subtype) :=
      Subobject.mk_eq_mk_of_comm u (ModuleCat.ofHom S.subtype) e.toModuleIso heq
    have hcat : EssentialExtension (ModuleCat.ofHom S.subtype) := by
      unfold EssentialExtension
      refine ⟨inferInstance, ?_⟩
      intro P hP
      rw [← hmk]
      exact hu.2 P hP
    exact (essentialSubmodule_iff_essentialExtension S).2 hcat
  let : CategoryTheory.Injective E := hf.2
  have hRf : EssentialSubmodule (LinearMap.range f.hom) :=
    range_essential _ _ f hf.1
  have hEnonzero : ¬ IsZero E := by
    intro h
    have hsub : ¬ Subsingleton (E : Type u) := by
      intro hs
      apply (not_subsingleton_iff_nontrivial.mpr
        (Ideal.Quotient.nontrivial_iff.mpr (inferInstance : p.IsPrime).ne_top))
      constructor
      intro x y
      apply (ModuleCat.mono_iff_injective f).mp hf.1.1
      exact hs.elim _ _
    exact hsub (ModuleCat.subsingleton_of_isZero h)
  have hquot_uniform :
      ∀ K L : Submodule R (R ⧸ p), K ≠ ⊥ → L ≠ ⊥ → K ⊓ L ≠ ⊥ := by
    intro K L hK hL
    obtain ⟨a, haK, ha0⟩ := K.ne_bot_iff.mp hK
    obtain ⟨b, hbL, hb0⟩ := L.ne_bot_iff.mp hL
    obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective a
    obtain ⟨s, hs⟩ := Ideal.Quotient.mk_surjective b
    have hrp : r ∉ p := by
      intro hrp
      apply ha0
      rw [← hr, Ideal.Quotient.eq_zero_iff_mem.mpr hrp]
    have hsp : s ∉ p := by
      intro hsp
      apply hb0
      rw [← hs, Ideal.Quotient.eq_zero_iff_mem.mpr hsp]
    have hmemK : Ideal.Quotient.mk p (s * r) ∈ K := by
      have h := K.smul_mem s haK
      simpa [← hr, ← Submodule.Quotient.mk_smul, Algebra.smul_def, mul_comm] using h
    have hmemL : Ideal.Quotient.mk p (s * r) ∈ L := by
      have h := L.smul_mem r hbL
      simpa [← hs, ← Submodule.Quotient.mk_smul, Algebra.smul_def, mul_comm] using h
    have hmem0 : Ideal.Quotient.mk p (s * r) ≠ 0 := by
      intro hzero
      have hmem : s * r ∈ p := Ideal.Quotient.eq_zero_iff_mem.mp hzero
      exact (inferInstance : p.IsPrime).mul_notMem hsp hrp hmem
    exact (K ⊓ L).ne_bot_iff.mpr
      ⟨Ideal.Quotient.mk p (s * r), ⟨hmemK, hmemL⟩, hmem0⟩
  have biprod_zero_of_projections :
      ∀ (Y Z : ModuleCat.{u} R) (z : (Y ⊞ Z : ModuleCat.{u} R)),
        (biprod.fst : (Y ⊞ Z) ⟶ Y).hom z = 0 →
          (biprod.snd : (Y ⊞ Z) ⟶ Z).hom z = 0 → z = 0 := by
    intro Y Z z hfst hsnd
    let w := ModuleCat.biprodIsoProd Y Z
    apply (ModuleCat.mono_iff_injective w.hom).mp inferInstance
    apply Prod.ext
    · have hw :
          w.hom ≫ ModuleCat.ofHom (LinearMap.fst R Y Z) = biprod.fst := by
        calc
          w.hom ≫ ModuleCat.ofHom (LinearMap.fst R Y Z) =
              w.hom ≫ (w.inv ≫ biprod.fst) := by
                rw [ModuleCat.biprodIsoProd_inv_comp_fst]
          _ = (w.hom ≫ w.inv) ≫ biprod.fst := by rw [Category.assoc]
          _ = biprod.fst := by rw [w.hom_inv_id, Category.id_comp]
      have h := congrArg (fun k => k.hom z) hw
      simpa using h.trans hfst
    · have hw :
          w.hom ≫ ModuleCat.ofHom (LinearMap.snd R Y Z) = biprod.snd := by
        calc
          w.hom ≫ ModuleCat.ofHom (LinearMap.snd R Y Z) =
              w.hom ≫ (w.inv ≫ biprod.snd) := by
                rw [ModuleCat.biprodIsoProd_inv_comp_snd]
          _ = (w.hom ≫ w.inv) ≫ biprod.snd := by rw [Category.assoc]
          _ = biprod.snd := by rw [w.hom_inv_id, Category.id_comp]
      have h := congrArg (fun k => k.hom z) hw
      simpa using h.trans hsnd
  have hInd : CategoryTheory.Indecomposable E := by
    refine ⟨hEnonzero, ?_⟩
    intro Y Z e
    by_cases hY : IsZero Y
    · exact Or.inl hY
    by_cases hZ : IsZero Z
    · exact Or.inr hZ
    exfalso
    let jY : Y ⟶ E := biprod.inl ≫ e.inv
    let jZ : Z ⟶ E := biprod.inr ≫ e.inv
    let : Mono jY := by
      dsimp [jY]
      infer_instance
    let : Mono jZ := by
      dsimp [jZ]
      infer_instance
    have hYsub : ¬ Subsingleton (Y : Type u) := by
      intro h
      exact hY (ModuleCat.isZero_of_subsingleton Y)
    have hZsub : ¬ Subsingleton (Z : Type u) := by
      intro h
      exact hZ (ModuleCat.isZero_of_subsingleton Z)
    have hRangeY : LinearMap.range jY.hom ≠ ⊥ := by
      intro hbot
      apply hYsub
      constructor
      intro y₁ y₂
      apply (ModuleCat.mono_iff_injective jY).mp inferInstance
      have hy₁ : jY.hom y₁ = 0 := by
        have hy := hbot ▸ (show jY.hom y₁ ∈ LinearMap.range jY.hom from ⟨y₁, rfl⟩)
        simpa using hy
      have hy₂ : jY.hom y₂ = 0 := by
        have hy := hbot ▸ (show jY.hom y₂ ∈ LinearMap.range jY.hom from ⟨y₂, rfl⟩)
        simpa using hy
      rw [hy₁, hy₂]
    have hRangeZ : LinearMap.range jZ.hom ≠ ⊥ := by
      intro hbot
      apply hZsub
      constructor
      intro z₁ z₂
      apply (ModuleCat.mono_iff_injective jZ).mp inferInstance
      have hz₁ : jZ.hom z₁ = 0 := by
        have hz := hbot ▸ (show jZ.hom z₁ ∈ LinearMap.range jZ.hom from ⟨z₁, rfl⟩)
        simpa using hz
      have hz₂ : jZ.hom z₂ = 0 := by
        have hz := hbot ▸ (show jZ.hom z₂ ∈ LinearMap.range jZ.hom from ⟨z₂, rfl⟩)
        simpa using hz
      rw [hz₁, hz₂]
    have hkerZ :
        LinearMap.ker (f ≫ e.hom ≫ (biprod.snd : (Y ⊞ Z) ⟶ Z)).hom ≠ ⊥ := by
      apply (LinearMap.ker _).ne_bot_iff.mpr
      obtain ⟨x, hxmem, hx0⟩ :=
        (LinearMap.range f.hom ⊓ LinearMap.range jY.hom).ne_bot_iff.mp
          (hRf _ hRangeY)
      obtain ⟨m, hm⟩ := hxmem.1
      obtain ⟨y, hy⟩ := hxmem.2
      refine ⟨m, ?_, ?_⟩
      · apply LinearMap.mem_ker.mpr
        have hxy : f.hom m = jY.hom y := hm.trans hy.symm
        have h := congrArg
          (fun z : E => (e.hom ≫ (biprod.snd : (Y ⊞ Z) ⟶ Z)).hom z) hxy
        calc
          (e.hom ≫ (biprod.snd : (Y ⊞ Z) ⟶ Z)).hom (f.hom m) =
              (biprod.snd : (Y ⊞ Z) ⟶ Z).hom
                ((biprod.inl : Y ⟶ Y ⊞ Z).hom y) := by
            simpa [jY, Category.assoc] using h
          _ = 0 := by
            change ((biprod.inl : Y ⟶ Y ⊞ Z) ≫
              (biprod.snd : (Y ⊞ Z) ⟶ Z)).hom y = 0
            rw [biprod.inl_snd]
            rfl
      · intro hm0
        apply hx0
        rw [← hm, hm0, map_zero]
    have hkerY :
        LinearMap.ker (f ≫ e.hom ≫ (biprod.fst : (Y ⊞ Z) ⟶ Y)).hom ≠ ⊥ := by
      apply (LinearMap.ker _).ne_bot_iff.mpr
      obtain ⟨x, hxmem, hx0⟩ :=
        (LinearMap.range f.hom ⊓ LinearMap.range jZ.hom).ne_bot_iff.mp
          (hRf _ hRangeZ)
      obtain ⟨m, hm⟩ := hxmem.1
      obtain ⟨z, hz⟩ := hxmem.2
      refine ⟨m, ?_, ?_⟩
      · apply LinearMap.mem_ker.mpr
        have hxy : f.hom m = jZ.hom z := hm.trans hz.symm
        have h := congrArg
          (fun w : E => (e.hom ≫ (biprod.fst : (Y ⊞ Z) ⟶ Y)).hom w) hxy
        calc
          (e.hom ≫ (biprod.fst : (Y ⊞ Z) ⟶ Y)).hom (f.hom m) =
              (biprod.fst : (Y ⊞ Z) ⟶ Y).hom
                ((biprod.inr : Z ⟶ Y ⊞ Z).hom z) := by
            simpa [jZ, Category.assoc] using h
          _ = 0 := by
            change ((biprod.inr : Z ⟶ Y ⊞ Z) ≫
              (biprod.fst : (Y ⊞ Z) ⟶ Y)).hom z = 0
            rw [biprod.inr_fst]
            rfl
      · intro hm0
        apply hx0
        rw [← hm, hm0, map_zero]
    obtain ⟨m, hmker, hm0⟩ :=
      ((LinearMap.ker (f ≫ e.hom ≫ (biprod.fst : (Y ⊞ Z) ⟶ Y)).hom ⊓
          LinearMap.ker (f ≫ e.hom ≫ (biprod.snd : (Y ⊞ Z) ⟶ Z)).hom).ne_bot_iff).mp
        (hquot_uniform (LinearMap.ker (f ≫ e.hom ≫ (biprod.fst : (Y ⊞ Z) ⟶ Y)).hom)
          (LinearMap.ker (f ≫ e.hom ≫ (biprod.snd : (Y ⊞ Z) ⟶ Z)).hom) hkerY hkerZ)
    have hfst :
        (f ≫ e.hom ≫ (biprod.fst : (Y ⊞ Z) ⟶ Y)).hom m = 0 :=
      LinearMap.mem_ker.mp hmker.1
    have hsnd :
        (f ≫ e.hom ≫ (biprod.snd : (Y ⊞ Z) ⟶ Z)).hom m = 0 :=
      LinearMap.mem_ker.mp hmker.2
    have hpair : e.hom.hom (f.hom m) = 0 := by
      apply biprod_zero_of_projections Y Z (e.hom.hom (f.hom m))
      · simpa [Category.assoc] using hfst
      · simpa [Category.assoc] using hsnd
    have hfzero : f.hom m = 0 := by
      apply (ModuleCat.mono_iff_injective e.hom).mp inferInstance
      simpa using hpair
    have hmzero : m = 0 := by
      apply (ModuleCat.mono_iff_injective f).mp hf.1.1
      simpa using hfzero
    exact hm0 hmzero
  let g : ModuleCat.of R p.ResidueField ⟶ E := Injective.factorThru f q
  have hgfac : q ≫ g = f := Injective.comp_factorThru f q
  have hRg : EssentialSubmodule (LinearMap.range g.hom) := by
    intro T hT
    obtain ⟨x, hxmem, hx0⟩ := (LinearMap.range f.hom ⊓ T).ne_bot_iff.mp (hRf T hT)
    refine (LinearMap.range g.hom ⊓ T).ne_bot_iff.mpr ⟨x, ?_, hx0⟩
    refine ⟨?_, hxmem.2⟩
    obtain ⟨m, hm⟩ := hxmem.1
    refine ⟨q.hom m, ?_⟩
    calc
      g.hom (q.hom m) = (q ≫ g).hom m := rfl
      _ = f.hom m := by rw [hgfac]
      _ = x := hm
  have hgm : Function.Injective g.hom := by
    intro x y hxy
    by_contra hxy0
    have hd0 : x - y ≠ 0 := sub_ne_zero.mpr hxy0
    obtain ⟨r, hrange, hr0⟩ :=
      (essentialSubmodule_iff_smul (LinearMap.range q.hom)).1
        (range_essential _ _ q hqess) (x - y) hd0
    obtain ⟨m, hm⟩ := hrange
    have hgd : g.hom (x - y) = 0 := by
      rw [map_sub, hxy, sub_self]
    have hz : g.hom (r • (x - y)) = 0 := by
      rw [map_smul, hgd, smul_zero]
    have hgmq : g.hom (q.hom m) = 0 := by
      rw [hm, hz]
    have hfm : f.hom m = 0 := by
      calc
        f.hom m = (q ≫ g).hom m := by rw [hgfac]
        _ = g.hom (q.hom m) := rfl
        _ = 0 := hgmq
    have hm0 : m = 0 := by
      apply (ModuleCat.mono_iff_injective f).mp hf.1.1
      simpa using hfm
    apply hr0
    rw [← hm, hm0, map_zero]
  let : Mono g := ConcreteCategory.mono_of_injective _ hgm
  have hgess : EssentialExtension g := by
    let S : Submodule R (E : Type u) := LinearMap.range g.hom
    let e : (p.ResidueField : Type u) ≃ₗ[R] S :=
      LinearEquiv.ofBijective g.hom.rangeRestrict
        ⟨(LinearMap.injective_rangeRestrict_iff g.hom).2 hgm,
          g.hom.surjective_rangeRestrict⟩
    let : Mono (ModuleCat.ofHom S.subtype) :=
      ConcreteCategory.mono_of_injective _ Subtype.val_injective
    have hcat : EssentialExtension (ModuleCat.ofHom S.subtype) :=
      (essentialSubmodule_iff_essentialExtension S).1 hRg
    have heq : e.toModuleIso.hom ≫ ModuleCat.ofHom S.subtype = g := by
      apply ModuleCat.hom_ext
      rfl
    have hmk :
        Subobject.mk g = Subobject.mk (ModuleCat.ofHom S.subtype) :=
      Subobject.mk_eq_mk_of_comm g (ModuleCat.ofHom S.subtype) e.toModuleIso heq
    unfold EssentialExtension at hcat ⊢
    refine ⟨inferInstance, ?_⟩
    intro P hP
    rw [hmk]
    exact hcat.2 P hP
  obtain ⟨p', hp', hpzero, Eₚ, hiso, hEₚ⟩ :=
    indecomposable_injective_zero_divisors E hf.2 hInd
  have hzero :
      (p : Set R) = ModuleZeroDivisors R (E : Type u) := by
    ext r
    constructor
    · intro hr
      refine ⟨f.hom (Ideal.Quotient.mk p (1 : R)), ?_, ?_⟩
      · intro hzero
        have hm1 : (Ideal.Quotient.mk p (1 : R) : R ⧸ p) = 0 := by
          apply (ModuleCat.mono_iff_injective f).mp hf.1.1
          simpa using hzero
        have htop : p = ⊤ := (Ideal.eq_top_iff_one p).mpr
          (Ideal.Quotient.eq_zero_iff_mem.mp hm1)
        exact (inferInstance : p.IsPrime).ne_top htop
      · calc
          r • f.hom (Ideal.Quotient.mk p (1 : R)) =
              f.hom (r • Ideal.Quotient.mk p (1 : R)) :=
            (f.hom.map_smul r _).symm
          _ = f.hom (Ideal.Quotient.mk p r) := by
            congr 1
            simp [Algebra.smul_def]
          _ = 0 := by
            rw [Ideal.Quotient.eq_zero_iff_mem.mpr hr, map_zero]
    · rintro ⟨x, hx, hxr⟩
      by_contra hr
      let φ : Module.End R (E : Type u) := algebraMap R (Module.End R (E : Type u)) r
      have hker : LinearMap.ker φ ≠ ⊥ := by
        apply (LinearMap.ker _).ne_bot_iff.mpr
        refine ⟨x, ?_, hx⟩
        apply LinearMap.mem_ker.mpr
        simpa [φ, Module.algebraMap_end_apply] using hxr
      obtain ⟨y, hymem, hy0⟩ :=
        (LinearMap.range f.hom ⊓ LinearMap.ker φ).ne_bot_iff.mp
          (hRf _ hker)
      obtain ⟨m, hm⟩ := hymem.1
      have hrfm : r • f.hom m = 0 := by
        have h := LinearMap.mem_ker.mp hymem.2
        rw [← hm] at h
        simpa [φ, Module.algebraMap_end_apply] using h
      have hrmm : r • m = 0 := by
        apply (ModuleCat.mono_iff_injective f).mp hf.1.1
        calc
          f.hom (r • m) = r • f.hom m := f.hom.map_smul r m
          _ = 0 := hrfm
          _ = f.hom 0 := by simp
      have hrq : (Ideal.Quotient.mk p r : R ⧸ p) ≠ 0 := by
        intro hrq
        apply hr
        exact Ideal.Quotient.eq_zero_iff_mem.mp hrq
      have hmq : m ≠ 0 := by
        intro hm0
        apply hy0
        rw [← hm, hm0, map_zero]
      have hprod : (Ideal.Quotient.mk p r : R ⧸ p) * m = 0 := by
        simpa [Algebra.smul_def] using hrmm
      exact hmq ((mul_eq_zero.mp hprod).resolve_left hrq)
  have hp_eq : p' = p := by
    apply Submodule.ext
    intro r
    change r ∈ (p' : Set R) ↔ r ∈ (p : Set R)
    rw [hpzero, hzero]
  subst p'
  refine ⟨hInd, ⟨g, ⟨hgess, hf.2⟩, hgfac⟩, ?_⟩
  obtain ⟨hiso⟩ := hiso
  refine ⟨Eₚ, ⟨⟨hiso⟩, ?_⟩⟩
  let gLoc : ModuleCat.of (Localization.AtPrime p) p.ResidueField ⟶ Eₚ :=
    ModuleCat.ofHom
      { toFun := fun x => hiso.hom.hom (g.hom x)
        map_add' := by
          intro x y
          rw [g.hom.map_add, hiso.hom.hom.map_add]
          rfl
        map_smul' := by
          intro z y
          obtain ⟨⟨r, s⟩, hz⟩ :=
            IsLocalization.surj (R := R) p.primeCompl z
          apply (IsUnit.smul_left_cancel
            (@IsLocalization.map_units R _ p.primeCompl (Localization.AtPrime p)
              _ _ _ s)).mp
          calc
            algebraMap R (Localization.AtPrime p) (s : R) •
                hiso.hom.hom (g.hom (z • y)) =
                hiso.hom.hom (g.hom
                  (algebraMap R (Localization.AtPrime p) (s : R) • (z • y))) := by
              rw [show algebraMap R (Localization.AtPrime p) (s : R) • (z • y) =
                  (s : R) • (z • y) from
                    algebraMap_smul (Localization.AtPrime p) (s : R) (z • y)]
              rw [g.hom.map_smul, hiso.hom.hom.map_smul]
              exact (ModuleCat.restrictScalars.smul_def'
                (algebraMap R (Localization.AtPrime p)) (s : R)
                (hiso.hom.hom (g.hom (z • y)))).symm
            _ = hiso.hom.hom (g.hom
                  ((z * algebraMap R (Localization.AtPrime p) (s : R)) • y)) := by
              congr 2
              rw [← mul_smul, mul_comm]
            _ = hiso.hom.hom (g.hom ((algebraMap R (Localization.AtPrime p) r) • y)) := by
              rw [hz]
            _ = hiso.hom.hom (g.hom (r • y)) := by
              rw [algebraMap_smul (Localization.AtPrime p) r y]
            _ = hiso.hom.hom (r • g.hom y) := by rw [g.hom.map_smul]
            _ = r • hiso.hom.hom (g.hom y) := by rw [hiso.hom.hom.map_smul]
            _ = algebraMap R (Localization.AtPrime p) r •
                hiso.hom.hom (g.hom y) := by
              exact ModuleCat.restrictScalars.smul_def'
                (algebraMap R (Localization.AtPrime p)) r
                (hiso.hom.hom (g.hom y))
            _ = (z * algebraMap R (Localization.AtPrime p) (s : R)) •
                hiso.hom.hom (g.hom y) := by rw [hz]
            _ = algebraMap R (Localization.AtPrime p) (s : R) •
                (z • hiso.hom.hom (g.hom y)) := by
              rw [mul_smul, smul_comm] }
  have hgmLoc : Function.Injective gLoc.hom := by
    intro x y hxy
    apply hgm
    apply (ModuleCat.mono_iff_injective hiso.hom).mp inferInstance
    exact hxy
  let : Mono gLoc := ConcreteCategory.mono_of_injective _ hgmLoc
  have hRgLoc : EssentialSubmodule (LinearMap.range gLoc.hom) := by
    intro T hT
    let T_R : Submodule R
        (((ModuleCat.restrictScalars (algebraMap R (Localization.AtPrime p))).obj Eₚ :
          ModuleCat R) : Type u) :=
      { carrier := (T : Set (Eₚ : Type u))
        zero_mem' := T.zero_mem
        add_mem' := T.add_mem
        smul_mem' := by
          intro r x hx
          change algebraMap R (Localization.AtPrime p) r • x ∈ T
          exact T.smul_mem _ hx }
    let U : Submodule R (E : Type u) := T_R.comap hiso.hom.hom
    have hU : U ≠ ⊥ := by
      obtain ⟨z, hzT, hz0⟩ := T.ne_bot_iff.mp hT
      have hz_eq : hiso.hom.hom (hiso.inv.hom z) = z := by
        have h := congrArg (fun k => k.hom z) hiso.inv_hom_id
        change hiso.hom.hom (hiso.inv.hom z) = z at h
        exact h
      refine U.ne_bot_iff.mpr ⟨hiso.inv.hom z, ?_, ?_⟩
      · change hiso.hom.hom (hiso.inv.hom z) ∈ T_R
        rw [hz_eq]
        exact hzT
      · intro hz'
        apply hz0
        rw [← hz_eq, hz', map_zero]
        rfl
    obtain ⟨y, hy, hy0⟩ :=
      (LinearMap.range g.hom ⊓ U).ne_bot_iff.mp (hRg U hU)
    refine (LinearMap.range gLoc.hom ⊓ T).ne_bot_iff.mpr
      ⟨hiso.hom.hom y, ?_, ?_⟩
    · obtain ⟨m, hm⟩ := hy.1
      constructor
      · refine ⟨m, ?_⟩
        change hiso.hom.hom (g.hom m) = hiso.hom.hom y
        rw [hm]
      · change hiso.hom.hom y ∈ T_R
        have hyU := hy.2
        change hiso.hom.hom y ∈ T_R at hyU
        exact hyU
    · intro hz
      apply hy0
      have h := congrArg (fun k : ModuleCat.of R (E : Type u) ⟶
          ModuleCat.of R (E : Type u) => k.hom y) hiso.hom_inv_id
      change hiso.inv.hom (hiso.hom.hom y) = y at h
      have hzR : hiso.hom.hom y =
          (0 : (((ModuleCat.restrictScalars
            (algebraMap R (Localization.AtPrime p))).obj Eₚ : ModuleCat R) : Type u)) := by
        exact hz
      rw [hzR, hiso.inv.hom.map_zero] at h
      exact h.symm
  have hLocEss : EssentialExtension gLoc := by
    let S : Submodule (Localization.AtPrime p) (Eₚ : Type u) :=
      LinearMap.range gLoc.hom
    let eLoc : (p.ResidueField : Type u) ≃ₗ[Localization.AtPrime p] S :=
      LinearEquiv.ofBijective gLoc.hom.rangeRestrict
        ⟨(LinearMap.injective_rangeRestrict_iff gLoc.hom).2 hgmLoc,
          gLoc.hom.surjective_rangeRestrict⟩
    let : Mono (ModuleCat.ofHom S.subtype) :=
      ConcreteCategory.mono_of_injective _ Subtype.val_injective
    have hcat : EssentialExtension (ModuleCat.ofHom S.subtype) :=
      (essentialSubmodule_iff_essentialExtension S).1 hRgLoc
    have heq : eLoc.toModuleIso.hom ≫ ModuleCat.ofHom S.subtype = gLoc := by
      apply ModuleCat.hom_ext
      rfl
    have hmk :
        Subobject.mk gLoc = Subobject.mk (ModuleCat.ofHom S.subtype) :=
      Subobject.mk_eq_mk_of_comm gLoc (ModuleCat.ofHom S.subtype)
        eLoc.toModuleIso heq
    unfold EssentialExtension at hcat ⊢
    refine ⟨inferInstance, ?_⟩
    intro P hP
    rw [hmk]
    exact hcat.2 P hP
  exact ⟨gLoc, ⟨hLocEss, hEₚ⟩⟩

/-- Over a Noetherian ring, every indecomposable injective is a residue-field
injective hull. -/
theorem noetherian_indecomposable_injective_residue_field_hull
    {R : Type u} [CommRing R] [IsNoetherianRing R]
    (E : ModuleCat.{u} R) (hE : CategoryTheory.Injective E)
    (hInd : CategoryTheory.Indecomposable E) :
    ∃ (p : Ideal R) (hp : p.IsPrime),
      letI := hp
      ∃ g : ModuleCat.of R p.ResidueField ⟶ E, InjectiveHull g := by
  classical
  obtain ⟨p, hp, hpzero, _⟩ :=
    indecomposable_injective_zero_divisors E hE hInd
  let : p.IsPrime := hp
  have hEsub : ¬ Subsingleton (E : Type u) := by
    intro h
    exact hInd.1 (ModuleCat.isZero_of_subsingleton E)
  let : Nontrivial (E : Type u) :=
    not_subsingleton_iff_nontrivial.mp hEsub
  obtain ⟨U, hUfin, hUspan⟩ :=
    Submodule.fg_def.mp (Ideal.fg_of_isNoetherianRing p)
  let K : R → Submodule R (E : Type u) := fun r =>
    LinearMap.ker (algebraMap R (Module.End R (E : Type u)) r)
  have hK : ∀ r ∈ U, K r ≠ ⊥ := by
    intro r hr
    have hrp : r ∈ p := by
      rw [← hUspan]
      exact Submodule.subset_span hr
    have hzd : r ∈ ModuleZeroDivisors R (E : Type u) := by
      exact hpzero ▸ hrp
    obtain ⟨x, hx, hxr⟩ := hzd
    apply (K r).ne_bot_iff.mpr
    refine ⟨x, ?_, hx⟩
    apply LinearMap.mem_ker.mpr
    simpa [K, Module.algebraMap_end_apply] using hxr
  have hKfin : ∀ s : Finset R, (∀ r ∈ s, K r ≠ ⊥) → s.inf K ≠ ⊥ := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
        intro _
        simp
    | @insert r s hrs ih =>
        intro hs
        rw [Finset.inf_insert]
        apply indecomposable_injective_submodule_intersection E hE hInd
        · exact hs r (Finset.mem_insert_self r s)
        · apply ih
          intro t ht
          exact hs t (Finset.mem_insert_of_mem ht)
  let u := hUfin.toFinset
  have huK : u.inf K ≠ ⊥ := by
    apply hKfin
    intro r hr
    apply hK
    exact hUfin.mem_toFinset.mp hr
  obtain ⟨x, hxK, hx0⟩ := u.inf K |>.ne_bot_iff.mp huK
  let φ : R →ₗ[R] (E : Type u) :=
    { toFun := fun r => r • x
      map_add' := by intro r s; rw [add_smul]
      map_smul' := by
        intro r s
        simp only [smul_eq_mul, RingHom.id_apply]
        rw [smul_smul] }
  have hpker : (p : Submodule R R) ≤ LinearMap.ker φ := by
    rw [← hUspan]
    apply Submodule.span_le.mpr
    intro r hr
    have hru : r ∈ u := by
      exact hUfin.mem_toFinset.mpr hr
    have hle : u.inf K ≤ K r := Finset.inf_le hru
    have hxKr : x ∈ K r := hle hxK
    apply LinearMap.mem_ker.mpr
    simpa [φ, K, Module.algebraMap_end_apply] using LinearMap.mem_ker.mp hxKr
  have hker : LinearMap.ker φ = (p : Submodule R R) := by
    apply le_antisymm
    · intro r hr
      by_contra hrp
      apply hrp
      have hz : r ∈ ModuleZeroDivisors R (E : Type u) :=
        ⟨x, hx0, by simpa [φ] using LinearMap.mem_ker.mp hr⟩
      change r ∈ (p : Set R)
      rw [hpzero]
      exact hz
    · exact hpker
  let f0 : ModuleCat.of R (R ⧸ p) ⟶ E :=
    ModuleCat.ofHom (p.liftQ φ hpker)
  have hf0mono : Mono f0 := by
    apply (ModuleCat.mono_iff_injective _).mpr
    change Function.Injective (p.liftQ φ hpker)
    exact LinearMap.ker_eq_bot.mp
      (Submodule.ker_liftQ_eq_bot' p φ hker.symm)
  have h1 : f0.hom (Ideal.Quotient.mk p (1 : R)) ≠ 0 := by
    intro hzero
    apply hx0
    change (p.liftQ φ hpker) (Ideal.Quotient.mk p (1 : R)) = 0 at hzero
    rw [← Ideal.Quotient.mk_eq_mk] at hzero
    rw [Submodule.liftQ_apply] at hzero
    simpa [φ] using hzero
  have hS : LinearMap.range f0.hom ≠ ⊥ := by
    apply (LinearMap.range f0.hom).ne_bot_iff.mpr
    refine ⟨f0.hom (Ideal.Quotient.mk p (1 : R)), ?_, h1⟩
    exact ⟨Ideal.Quotient.mk p (1 : R), rfl⟩
  have hrange : EssentialSubmodule (LinearMap.range f0.hom) := by
    let S : Submodule R (E : Type u) := LinearMap.range f0.hom
    exact (essentialSubmodule_iff_essentialExtension S).2
      (indecomposable_injective_submodule_hull E hE hInd S hS).1
  have hf0ess : EssentialExtension f0 := by
    let S : Submodule R (E : Type u) := LinearMap.range f0.hom
    let e : (R ⧸ p : Type u) ≃ₗ[R] S :=
      LinearEquiv.ofBijective f0.hom.rangeRestrict
        ⟨(LinearMap.injective_rangeRestrict_iff f0.hom).2
            ((ModuleCat.mono_iff_injective f0).mp hf0mono),
          f0.hom.surjective_rangeRestrict⟩
    let : Mono (ModuleCat.ofHom S.subtype) :=
      ConcreteCategory.mono_of_injective _ Subtype.val_injective
    have hcat : EssentialExtension (ModuleCat.ofHom S.subtype) :=
      (essentialSubmodule_iff_essentialExtension S).1 hrange
    have heq : e.toModuleIso.hom ≫ ModuleCat.ofHom S.subtype = f0 := by
      apply ModuleCat.hom_ext
      rfl
    have hmk :
        Subobject.mk f0 = Subobject.mk (ModuleCat.ofHom S.subtype) :=
      Subobject.mk_eq_mk_of_comm f0 (ModuleCat.ofHom S.subtype) e.toModuleIso heq
    unfold EssentialExtension at hcat ⊢
    refine ⟨hf0mono, ?_⟩
    intro P hP
    rw [hmk]
    exact hcat.2 P hP
  obtain ⟨_, ⟨g, hg, _⟩, _⟩ :=
    prime_injective_hull_residue_field p E f0 ⟨hf0ess, hE⟩
  exact ⟨p, hp, g, hg⟩

/-- A Noetherian injective module is a direct sum of indecomposable injectives. -/
def IsDirectSumOfIndecomposableInjectives
    {R : Type u} [CommRing R] (I : ModuleCat.{v} R) : Prop :=
  ∃ (ι : Type (max u v)) (E : ι → ModuleCat.{v} R),
    (∀ i, CategoryTheory.Indecomposable (E i) ∧
      CategoryTheory.Injective (E i)) ∧
      Nonempty ((I : Type v) ≃ₗ[R] (⨁ i, (E i : Type v)))

/-- Structure theorem for injectives over a Noetherian ring. -/
theorem structure_of_injectives_noetherian
    {R : Type u} [CommRing R] [IsNoetherianRing R] :
    (∀ [Small.{v} R] (I : ModuleCat.{v} R), CategoryTheory.Injective I →
      IsDirectSumOfIndecomposableInjectives I) ∧
      (∀ E : ModuleCat.{u} R, CategoryTheory.Injective E →
        CategoryTheory.Indecomposable E →
          ∃ (p : Ideal R) (hp : p.IsPrime),
            letI := hp
            ∃ g : ModuleCat.of R p.ResidueField ⟶ E, InjectiveHull g) := by
  sorry

end

end Formalization.Books.Dualizing.Unit05
