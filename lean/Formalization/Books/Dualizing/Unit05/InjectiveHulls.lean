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
  letI : IsIso ψ :=
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
  letI : Mono (fractionFieldModuleMap (R := R) (K := K)) := hmono
  letI : Mono (ModuleCat.ofHom S.subtype) :=
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
  letI : Module.Injective R K := hKinj
  exact ⟨hEss, Module.injective_object_of_injective_module R K⟩

/-! ## Indecomposable injectives -/
private theorem exists_injective_hull_in_injective
    {R : Type u} [Ring R] (I₀ : ModuleCat.{v} R)
    (hI : CategoryTheory.Injective I₀)
    (M : ModuleCat.{v} R) (j₀ : M ⟶ I₀) (hj₀ : Mono j₀) :
    ∃ (E : ModuleCat.{v} R) (f : M ⟶ E), InjectiveHull f := by
  letI : CategoryTheory.Injective I₀ := hI
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
    simpa [hcomp, Category.assoc]
  apply (Module.End.isUnit_iff φ).2
  constructor
  · exact LinearMap.ker_eq_bot.mp hφ
  · intro y
    refine ⟨a.hom.hom y, ?_⟩
    have h := congrArg (fun q : E ⟶ E => q.hom (a.hom.hom y)) hφeq
    have ha := congrArg (fun q : E ⟶ E => q.hom y) a.hom_inv_id
    calc
      φ (a.hom.hom y) = a.inv.hom (a.hom.hom y) := by simpa using h
      _ = y := by simpa using ha

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
  letI : Nontrivial (E : Type v) :=
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
        simp [LinearMap.ker_zero, bot_ne_top]
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
  letI : Module R X := Module.compHom X (algebraMap R S)
  letI : Module R Y := Module.compHom Y (algebraMap R S)
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
  letI : IsLocalRing A := hlocal
  letI : I.IsMaximal := hmax
  let p : Ideal R := I.comap (algebraMap R A)
  have hp : p.IsPrime := by
    constructor
    · intro htop
      have h1 : (1 : R) ∈ p := by simpa [htop]
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
  · letI : p.IsPrime := hp
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
            simp [mul_assoc]
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
    letI : Module L (E : Type v) := Module.compHom (E : Type v) gL
    letI : IsScalarTower R L (E : Type v) :=
      { smul_assoc := by
          intro r l x
          change (gL (r • l)) x = r • ((gL l) x)
          have hgr : gL (algebraMap R L r) = g0 r := DFunLike.congr_fun hgL r
          rw [Algebra.smul_def, map_mul, hgr]
          simpa [g0, A, Module.End.mul_apply, Module.algebraMap_end_apply] }
    letI : CategoryTheory.Injective (ModuleCat.of R (E : Type v)) := hE
    have hEM : Module.Injective R (E : Type v) :=
      Module.injective_module_of_injective_object R (E : Type v)
    have hEL : Module.Injective L (E : Type v) :=
      injective_of_localization_action p.primeCompl (E : Type v) hEM
    letI : Module.Injective L (E : Type v) := hEL
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
            convert congrArg (fun y => (y : E)) hsmul using 1 <;> rfl }
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
