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
  rcases hf.1 with ⟨hfmono, _⟩
  let := hfmono
  let := hg.2
  exact ⟨Injective.factorThru (φ ≫ g) f, Injective.comp_factorThru (φ ≫ g) f⟩

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
    exact ⟨b * a, hmem, hnonzero⟩
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
  sorry

/-- An injective module containing the source splits off the hull. -/
theorem injective_hull_split
    {R : Type u} [Ring R] {M E I : ModuleCat.{v} R}
    {f : M ⟶ E} {h : M ⟶ I}
    (hf : InjectiveHull f) (hh : Mono h)
    (hI : CategoryTheory.Injective I) :
    ∃ (I' : ModuleCat.{v} R) (e : I ≅ E ⊞ I'),
      h ≫ e.hom ≫ biprod.fst = f := by
  sorry

/-- Injective hulls of a fixed module are isomorphic. -/
theorem injective_hull_unique_up_to_iso
    {R : Type u} [Ring R] {M E E' : ModuleCat.{v} R}
    {f : M ⟶ E} {g : M ⟶ E'}
    (hf : InjectiveHull f) (hg : InjectiveHull g) :
    Nonempty (E ≅ E') := by
  sorry

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
  sorry

/-! ## Indecomposable injectives -/

/- `CategoryTheory.Indecomposable` is Mathlib's canonical additive-category
form of the source's indecomposable-object definition. -/

/-- Every nonzero submodule of an indecomposable injective is essential. -/
theorem indecomposable_injective_submodule_hull
    {R : Type u} [Ring R] (E : ModuleCat.{v} R)
    (hE : CategoryTheory.Injective E)
    (hInd : CategoryTheory.Indecomposable E) :
    ∀ S : Submodule R (E : Type v), S ≠ ⊥ →
      InjectiveHull (ModuleCat.ofHom S.subtype) := by
  sorry

/-- Any two nonzero submodules of an indecomposable injective meet nontrivially. -/
theorem indecomposable_injective_submodule_intersection
    {R : Type u} [Ring R] (E : ModuleCat.{v} R)
    (hE : CategoryTheory.Injective E)
    (hInd : CategoryTheory.Indecomposable E) :
    ∀ S T : Submodule R (E : Type v), S ≠ ⊥ → T ≠ ⊥ → S ⊓ T ≠ ⊥ := by
  sorry

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
  sorry

/- The zero divisors acting on an indecomposable injective form a prime ideal,
and the module is injective after localizing at that ideal. -/
def ModuleZeroDivisors (R M : Type*) [CommRing R] [AddCommGroup M]
    [Module R M] : Set R :=
  {r | ∃ x : M, x ≠ 0 ∧ r • x = 0}

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
  sorry

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
  sorry

/-- Over a Noetherian ring, every indecomposable injective is a residue-field
injective hull. -/
theorem noetherian_indecomposable_injective_residue_field_hull
    {R : Type u} [CommRing R] [IsNoetherianRing R]
    (E : ModuleCat.{u} R) (hE : CategoryTheory.Injective E)
    (hInd : CategoryTheory.Indecomposable E) :
    ∃ (p : Ideal R) (hp : p.IsPrime),
      letI := hp
      ∃ g : ModuleCat.of R p.ResidueField ⟶ E, InjectiveHull g := by
  sorry

/-- A Noetherian injective module is a direct sum of indecomposable injectives. -/
def IsDirectSumOfIndecomposableInjectives
    {R : Type u} [CommRing R] (I : ModuleCat.{v} R) : Prop :=
  ∃ (ι : Type w) (E : ι → ModuleCat.{v} R),
    (∀ i, CategoryTheory.Indecomposable (E i) ∧
      CategoryTheory.Injective (E i)) ∧
      Nonempty ((I : Type v) ≃ₗ[R] (⨁ i, (E i : Type v)))

/-- Structure theorem for injectives over a Noetherian ring. -/
theorem structure_of_injectives_noetherian
    {R : Type u} [CommRing R] [IsNoetherianRing R] :
    (∀ I : ModuleCat.{v} R, CategoryTheory.Injective I →
      IsDirectSumOfIndecomposableInjectives I) ∧
      (∀ E : ModuleCat.{u} R, CategoryTheory.Injective E →
        CategoryTheory.Indecomposable E →
          ∃ (p : Ideal R) (hp : p.IsPrime),
            letI := hp
            ∃ g : ModuleCat.of R p.ResidueField ⟶ E, InjectiveHull g) := by
  sorry

end

end Formalization.Books.Dualizing.Unit05
