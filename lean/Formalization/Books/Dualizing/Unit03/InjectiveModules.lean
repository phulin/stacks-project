import Formalization.Books.Dualizing.Unit02.Essential
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.Algebra.Category.Ring.Epi
import Mathlib.Algebra.DirectSum.Finsupp
import Mathlib.Algebra.DirectSum.Module
import Mathlib.Algebra.Module.Injective
import Mathlib.LinearAlgebra.Projection
import Mathlib.Algebra.Module.Torsion.PrimaryComponent
import Mathlib.Algebra.Polynomial.Module.TensorProduct
import Mathlib.Algebra.Category.ModuleCat.InjectiveDimension
import Mathlib.RingTheory.Ideal.MinimalPrime.Localization
import Mathlib.RingTheory.KrullDimension.Zero
import Mathlib.RingTheory.LocalProperties.Injective
import Mathlib.RingTheory.LocalProperties.Reduced
import Mathlib.RingTheory.RingHom.Flat
import Mathlib.RingTheory.Artinian.Module
import Mathlib.RingTheory.SimpleModule.InjectiveProjective

/-!
# Injective modules

This file records the precise statements in Chapter 3 of the dualizing-complexes
book.  The statements use Mathlib's module-theoretic injectivity predicate and
its canonical constructions for change of scalars, localization, torsion, and
polynomial modules.
-/

namespace Formalization.Books.Dualizing.Unit03

universe u v w

open Formalization.Books.Dualizing.Unit02
open CategoryTheory CategoryTheory.Category CategoryTheory.Limits
open scoped TensorProduct
noncomputable section

/-! ### Products and change of rings -/

theorem product_injective
    {R : Type u} [CommRing R] {ι : Type w} {M : ι → Type v}
    [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)]
    [∀ i, Module.Injective R (M i)] [Small.{v} R] :
    Module.Injective R (∀ i, M i) := by
  infer_instance

theorem injective_of_flat
    {R : Type u} {S : Type v} {E : Type w} [CommRing R] [CommRing S]
    [AddCommGroup E] [Module S E] [Small.{w} S] (f : R →+* S) (hf : f.Flat)
    [Module.Injective S E] :
    @Module.Injective R _ E _ (Module.compHom E f) := by
  let _ : Algebra R S := f.toAlgebra
  let _ : Module.Flat R S := hf
  let _ : Module R E := Module.compHom E f
  constructor
  intro X Y _ _ _ _ i hi g
  let _ : IsScalarTower R S E :=
    ⟨fun r s x => by
      change (f r * s) • x = f r • s • x
      rw [mul_smul]⟩
  let iR : X →ₗ[R] Y :=
    { toFun := i
      map_add' := i.map_add
      map_smul' := i.map_smul }
  have hiR : Function.Injective iR := hi
  let gR : X →ₗ[R] E :=
    { toFun := g
      map_add' := g.map_add
      map_smul' := by
        intro r x
        exact g.map_smul r x }
  let iS := TensorProduct.AlgebraTensorModule.lTensor S S iR
  have hiS : Function.Injective iS :=
    Module.Flat.lTensor_preserves_injective_linearMap _ hiR
  let b : S →ₗ[S] X →ₗ[R] E :=
    { toFun := fun s =>
        { toFun := fun x => s • gR x
          map_add' := by
            intro x y
            rw [map_add, smul_add]
          map_smul' := by
            intro r x
            rw [map_smul]
            rw [smul_comm]
            rfl }
      map_add' := by
        intro s t
        ext x
        change (s + t) • gR x = s • gR x + t • gR x
        rw [add_smul]
      map_smul' := by
        intro s t
        ext x
        change (s * t) • gR x = s • t • gR x
        rw [mul_smul] }
  let gS : S ⊗[R] X →ₗ[S] E :=
    TensorProduct.AlgebraTensorModule.lift b
  obtain ⟨hS, hhS⟩ := Module.Injective.extension_property S E _ _ iS hiS gS
  let unitX : X →ₗ[R] S ⊗[R] X :=
    { toFun := fun x => (1 : S) ⊗ₜ[R] x
      map_add' := by
        intro x y
        rw [TensorProduct.tmul_add]
      map_smul' := by
        intro r x
        rw [TensorProduct.tmul_smul]
        rfl }
  let unitY : Y →ₗ[R] S ⊗[R] Y :=
    { toFun := fun y => (1 : S) ⊗ₜ[R] y
      map_add' := by
        intro x y
        rw [TensorProduct.tmul_add]
      map_smul' := by
        intro r x
        rw [TensorProduct.tmul_smul]
        rfl }
  let h : Y →ₗ[R] E := (hS.restrictScalars R).comp unitY
  refine ⟨h, ?_⟩
  intro x
  calc
    h (i x) = hS (iS (unitX x)) := by
      simp [h, unitX, unitY, iS, iR]
    _ = gS (unitX x) := by
      simpa [LinearMap.comp_apply] using
        congrArg (fun q : S ⊗[R] X →ₗ[S] E => q (unitX x)) hhS
    _ = g x := by
      simp [gS, b, unitX, gR]

theorem injective_of_ring_epimorphism
    {R S : Type u} {E : Type v} [CommRing R] [CommRing S] [AddCommGroup E]
    [Module S E] (f : R →+* S) (hf : CategoryTheory.Epi (CommRingCat.ofHom f))
    (hE : @Module.Injective R _ E _ (Module.compHom E f)) :
    Module.Injective S E := by
  let _ : Algebra R S := f.toAlgebra
  have hf' : Algebra.IsEpi R S := by
    apply CommRingCat.epi_iff_epi.mp
    exact hf
  let _ : Module R E := Module.compHom E f
  let _ : Module.Injective R E := hE
  let _ : IsScalarTower R S E :=
    ⟨fun r s x => by
      change (f r * s) • x = f r • s • x
      rw [mul_smul]⟩
  constructor
  intro X Y _ _ _ _ i hi g
  let _ : Module R X := Module.compHom X f
  let _ : Module R Y := Module.compHom Y f
  let _ : IsScalarTower R S Y :=
    ⟨fun r s y => by
      change (f r * s) • y = f r • s • y
      rw [mul_smul]⟩
  let iR : X →ₗ[R] Y :=
    { toFun := i
      map_add' := i.map_add
      map_smul' := by
        intro r x
        change i (f r • x) = f r • i x
        exact i.map_smul (f r) x }
  have hiR : Function.Injective iR := by
    intro x y hxy
    exact hi hxy
  let gR : X →ₗ[R] E :=
    { toFun := g
      map_add' := g.map_add
      map_smul' := by
        intro r x
        change g (f r • x) = f r • g x
        exact g.map_smul (f r) x }
  obtain ⟨hR, hhR⟩ := hE.out iR hiR gR
  let hS : Y →ₗ[S] E :=
    (TensorProduct.lid' R S E).toLinearMap.comp
      ((TensorProduct.AlgebraTensorModule.lTensor S S hR).comp
        (TensorProduct.lid' R S Y).symm.toLinearMap)
  refine ⟨hS, ?_⟩
  intro x
  calc
    hS (i x) = hR (iR x) := by simp [hS, iR]
    _ = gR x := hhR x
    _ = g x := rfl

/-! ### Hom and coextension of scalars -/

theorem hom_injective
    {R : Type u} {S : Type v} {E : Type w} [CommRing R] [CommRing S]
    [AddCommGroup E] [Module R E] [Small.{w} R] (f : R →+* S)
    [Module.Injective R E] :
    Module.Injective S
      ((ModuleCat.coextendScalars f).obj (ModuleCat.of R E) : Type _) := by
  constructor
  intro X Y _ _ _ _ i hi g
  let _ : Module R S := Module.compHom S f
  let _ : Module R X := Module.compHom X f
  let _ : Module R Y := Module.compHom Y f
  let iR : X →ₗ[R] Y :=
    { toFun := i
      map_add' := i.map_add
      map_smul' := by
        intro r x
        change i (f r • x) = f r • i x
        exact i.map_smul (f r) x }
  have hiR : Function.Injective iR := by
    intro x y hxy
    exact hi hxy
  let gx : X → S →ₗ[R] E :=
    fun x => ModuleCat.CoextendScalars.equiv f (ModuleCat.of R E) (g x)
  let g' : X →ₗ[R] E :=
    { toFun := fun x => gx x (1 : S)
      map_add' := by
        intro x y
        have hxy : gx (x + y) = gx x + gx y := by
          ext s
          simp [gx]
          rfl
        exact congrArg (fun q : S →ₗ[R] E => q (1 : S)) hxy
      map_smul' := by
        intro r x
        change (g (f r • x)) (1 : S) = r • (g x) (1 : S)
        rw [map_smul, ModuleCat.CoextendScalars.smul_apply, one_mul]
        have hr : (f r : S) = r • (1 : S) := by
          rw [RingHom.toModule_smul]
          simp
        rw [hr]
        exact (gx x).map_smul r 1 }
  obtain ⟨h', hh'⟩ := Module.Injective.extension_property R E _ _ iR hiR g'
  let h : Y →ₗ[S] ↑((ModuleCat.coextendScalars f).obj (ModuleCat.of R E)) :=
    { toFun := fun y => (ModuleCat.CoextendScalars.equiv f (ModuleCat.of R E)).symm
        { toFun := fun s : S => h' (s • y)
          map_add' := fun s₁ s₂ : S => by
            change h' ((s₁ + s₂) • y) = h' (s₁ • y) + h' (s₂ • y)
            rw [add_smul, map_add]
          map_smul' := fun r (s : S) => by
            change h' ((f r * s) • y) = r • h' (s • y)
            rw [← smul_smul]
            exact h'.map_smul r (s • y) }
      map_add' := fun y z =>
        (ModuleCat.CoextendScalars.equiv f (ModuleCat.of R E)).injective <|
          LinearMap.ext fun s : S => by
            change h' (s • (y + z)) = h' (s • y) + h' (s • z)
            rw [smul_add, map_add]
      map_smul' := fun s y =>
        (ModuleCat.CoextendScalars.equiv f (ModuleCat.of R E)).injective <|
          LinearMap.ext fun t : S => by
            change h' (t • (s • y)) = h' ((t * s) • y)
            rw [smul_smul] }
  refine ⟨h, ?_⟩
  intro x
  apply ModuleCat.CoextendScalars.ext
  refine LinearMap.ext (fun (s : S) => ?_)
  change h' (s • i x) = gx x s
  calc
    h' (s • i x) = h' (i (s • x)) := by rw [i.map_smul]
    _ = g' (s • x) := by
      simpa [iR, LinearMap.comp_apply] using
        congrArg (fun q : X →ₗ[R] E => q (s • x)) hh'
    _ = gx x s := by
      change gx (s • x) (1 : S) = gx x s
      change (g (s • x)) (1 : S) = (g x) s
      rw [map_smul, ModuleCat.CoextendScalars.smul_apply, one_mul]

/-! ### Essential extensions -/

theorem injective_iff_essential_extensions_trivial
    {R I : Type*} [CommRing R] [AddCommGroup I] [Module R I]
    [Module.Injective R I] (E : Submodule R I) :
    Module.Injective R E ↔
      ∀ (E' : Submodule R I) (hEE' : E ≤ E'),
        EssentialExtension (ModuleCat.ofHom (E.inclusion hEE')) → E = E' := by
  constructor
  · intro hE E' hEE' hEssExt
    let j : E →ₗ[R] E' := E.inclusion hEE'
    let S : Submodule R E' := LinearMap.range j
    have hj : Function.Injective j := Submodule.inclusion_injective hEE'
    let e : E ≃ₗ[R] S :=
      LinearEquiv.ofBijective j.rangeRestrict
        ⟨(LinearMap.injective_rangeRestrict_iff j).2 hj, j.surjective_rangeRestrict⟩
    have : Mono (ModuleCat.ofHom j) :=
      ConcreteCategory.mono_of_injective _ hj
    have : Mono (ModuleCat.ofHom S.subtype) :=
      ConcreteCategory.mono_of_injective _ Subtype.val_injective
    have heq :
        e.toModuleIso.hom ≫ ModuleCat.ofHom S.subtype =
          ModuleCat.ofHom j := by
      apply ModuleCat.hom_ext
      rfl
    have hmk :
        Subobject.mk (ModuleCat.ofHom j) =
          Subobject.mk (ModuleCat.ofHom S.subtype) :=
      Subobject.mk_eq_mk_of_comm (ModuleCat.ofHom j)
        (ModuleCat.ofHom S.subtype) e.toModuleIso heq
    have hEssS : EssentialSubmodule S := by
      apply (essentialSubmodule_iff_essentialExtension S).2
      unfold EssentialExtension at hEssExt ⊢
      rcases hEssExt with ⟨hmono, hess⟩
      have := hmono
      refine ⟨inferInstance, ?_⟩
      intro P hP
      rw [← hmk]
      exact hess P hP
    obtain ⟨α, hα⟩ :=
      hE.out j hj (LinearMap.id)
    have hker : LinearMap.ker α = ⊥ := by
      apply (LinearMap.ker α).eq_bot_iff.mpr
      intro x hx
      by_contra hx0
      obtain ⟨r, hrS, hr0⟩ :=
        (essentialSubmodule_iff_smul S).1 hEssS x hx0
      rcases hrS with ⟨e, he⟩
      have he0 : e = 0 := by
        have hzero : α (r • x) = 0 := by
          rw [map_smul, LinearMap.mem_ker.mp hx, smul_zero]
        have hzero' : α (j e) = 0 := by
          rw [he]
          exact hzero
        simpa only [LinearMap.id_apply] using (hα e).symm.trans hzero'
      apply hr0
      rw [← he, he0, map_zero]
    apply le_antisymm hEE'
    intro x hx
    let x' : E' := ⟨x, hx⟩
    have hd : x' - j (α x') ∈ LinearMap.ker α := by
      rw [LinearMap.mem_ker]
      simp only [map_sub, hα, LinearMap.id_apply, sub_self]
    have hd0 : x' - j (α x') = 0 := by
      have : x' - j (α x') ∈ (⊥ : Submodule R E') := hker ▸ hd
      simpa using this
    have hxeq : x' = j (α x') := sub_eq_zero.mp hd0
    have hxeq' : x = (j (α x') : I) := congrArg Subtype.val hxeq
    rw [hxeq']
    exact (α x').property
  · intro htriv
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

theorem injective_iff_essential_extension_maps_trivial
    {R M : Type v} [CommRing R] [AddCommGroup M] [Module R M] :
    Module.Injective R M ↔
      ∀ (N : ModuleCat.{v} R) (f : ModuleCat.of R M ⟶ N),
        EssentialExtension f → Function.Surjective f.hom := by
  constructor
  · intro hM N f hf
    rcases hf with ⟨hfmono, hfess⟩
    have hf_inj : Function.Injective f.hom :=
      (ModuleCat.mono_iff_injective f).mp hfmono
    let S : Submodule R N := LinearMap.range f.hom
    let e : M ≃ₗ[R] S :=
      LinearEquiv.ofBijective f.hom.rangeRestrict
        ⟨(LinearMap.injective_rangeRestrict_iff f.hom).2 hf_inj,
          f.hom.surjective_rangeRestrict⟩
    have heq :
        e.toModuleIso.hom ≫ ModuleCat.ofHom S.subtype = f := by
      apply ModuleCat.hom_ext
      rfl
    have hmk :
        Subobject.mk f = Subobject.mk (ModuleCat.ofHom S.subtype) :=
      Subobject.mk_eq_mk_of_comm f
        (ModuleCat.ofHom S.subtype) e.toModuleIso heq
    have hEssS : EssentialSubmodule S := by
      apply (essentialSubmodule_iff_essentialExtension S).2
      refine ⟨inferInstance, ?_⟩
      intro P hP
      rw [← hmk]
      exact hfess P hP
    obtain ⟨g, hgf⟩ := hM.out f.hom hf_inj (LinearMap.id)
    have hker : LinearMap.ker g = ⊥ := by
      apply (LinearMap.ker g).eq_bot_iff.mpr
      intro x hx
      by_contra hx0
      obtain ⟨r, hrS, hr0⟩ :=
        (essentialSubmodule_iff_smul S).1 hEssS x hx0
      rcases hrS with ⟨m, hm⟩
      have hzero : g (r • x) = 0 := by
        rw [map_smul, LinearMap.mem_ker.mp hx, smul_zero]
      have hzero' : g (f.hom m) = 0 := by
        rw [hm]
        exact hzero
      have hm0 : m = 0 := by
        simpa only [LinearMap.id_apply] using (hgf m).symm.trans hzero'
      apply hr0
      rw [← hm, hm0, map_zero]
    intro y
    refine ⟨g y, ?_⟩
    have hyker : y - f.hom (g y) ∈ LinearMap.ker g := by
      rw [LinearMap.mem_ker]
      simp only [map_sub, hgf, LinearMap.id_apply, sub_self]
    have hy0 : y - f.hom (g y) = 0 := by
      have : y - f.hom (g y) ∈ (⊥ : Submodule R N) := hker ▸ hyker
      simpa using this
    exact (sub_eq_zero.mp hy0).symm
  · intro htriv
    let p : InjectivePresentation (ModuleCat.of R M) :=
      ((ModuleCat.enoughInjectives R).presentation (ModuleCat.of R M)).some
    have hp_inj : CategoryTheory.Injective p.J := p.injective
    have hJ : Module.Injective R (p.J : Type v) :=
      Module.injective_module_of_injective_object R (p.J : Type v)
    let j : M →ₗ[R] (p.J : Type v) := p.f.hom
    have hj : Function.Injective j :=
      (ModuleCat.mono_iff_injective p.f).mp p.mono
    let E : Submodule R (p.J : Type v) := LinearMap.range j
    let e : M ≃ₗ[R] E :=
      LinearEquiv.ofBijective j.rangeRestrict
        ⟨(LinearMap.injective_rangeRestrict_iff j).2 hj,
          j.surjective_rangeRestrict⟩
    have hE : Module.Injective R E := by
      apply (injective_iff_essential_extensions_trivial (R := R)
        (I := (p.J : Type v)) E).2
      intro E' hEE' hEss
      let f : ModuleCat.of R M ⟶ ModuleCat.of R E' :=
        ModuleCat.ofHom ((E.inclusion hEE').comp e.toLinearMap)
      have heq :
          e.toModuleIso.hom ≫ ModuleCat.ofHom (E.inclusion hEE') = f := by
        apply ModuleCat.hom_ext
        rfl
      have hincl : Mono (ModuleCat.ofHom (E.inclusion hEE')) :=
        ConcreteCategory.mono_of_injective _ (Submodule.inclusion_injective hEE')
      have hf_inj : Function.Injective f.hom := by
        intro x y hxy
        apply e.injective
        apply Subtype.ext
        have hxy' := congrArg Subtype.val hxy
        change (e x : (p.J : Type v)) = (e y : (p.J : Type v)) at hxy'
        exact hxy'
      have hmf : Mono f := ConcreteCategory.mono_of_injective _ hf_inj
      have hmk :
          Subobject.mk f =
            Subobject.mk (ModuleCat.ofHom (E.inclusion hEE')) :=
        Subobject.mk_eq_mk_of_comm f
          (ModuleCat.ofHom (E.inclusion hEE')) e.toModuleIso heq
      have hEssF : EssentialExtension f := by
        rcases hEss with ⟨hmono, hess⟩
        have := hmono
        refine ⟨hmf, ?_⟩
        intro P hP
        rw [hmk]
        exact hess P hP
      have hsurj : Function.Surjective f.hom :=
        htriv (ModuleCat.of R E') f hEssF
      apply le_antisymm hEE'
      intro y hy
      obtain ⟨m, hm⟩ := hsurj ⟨y, hy⟩
      have hval : (y : (p.J : Type v)) = (e m : (p.J : Type v)) := by
        simpa [f] using (congrArg Subtype.val hm).symm
      exact hval ▸ (e m).property
    refine ⟨?_⟩
    intro X Y _ _ _ _ i hi g
    obtain ⟨h, hh⟩ := hE.out i hi (e.toLinearMap.comp g)
    refine ⟨e.symm.toLinearMap.comp h, ?_⟩
    intro x
    calc
      e.symm (h (i x)) = e.symm ((e.toLinearMap.comp g) x) :=
        congrArg e.symm (hh x)
      _ = g x := by
        change e.symm (e (g x)) = g x
        exact e.symm_apply_apply (g x)

/-! ### A reduced ring and a minimal-prime localization -/

theorem minimal_prime_localization_isField
    {R : Type u} [CommRing R] [IsReduced R] (p : Ideal R) [p.IsPrime]
    (hp : IsMinimalPrime p) :
    IsField (Localization.AtPrime p) := by
  let _ : IsReduced (Localization.AtPrime p) := inferInstance
  let _ : Nontrivial (Localization.AtPrime p) :=
    IsLocalization.AtPrime.nontrivial (S := Localization.AtPrime p) p
  have hsub : Subsingleton (PrimeSpectrum (Localization.AtPrime p)) :=
    IsLocalization.subsingleton_primeSpectrum_of_mem_minimalPrimes p hp (Localization.AtPrime p)
  exact (PrimeSpectrum.subsingleton_iff_isField_of_isReduced
    (R := Localization.AtPrime p)).mp hsub

theorem minimal_prime_localization_injective
    {R : Type u} [CommRing R] [IsReduced R] (p : Ideal R) [p.IsPrime]
    (hp : IsMinimalPrime p) :
    Module.Injective R (Localization.AtPrime p) := by
  let S := Localization.AtPrime p
  let _ : IsField S := minimal_prime_localization_isField p hp
  let _ : Field S := (minimal_prime_localization_isField p hp).toField
  let _ : IsSemisimpleRing S := IsArtinianRing.isSemisimpleRing_of_isReduced S
  let _ : Module.Injective S S := Module.injective_of_isSemisimpleRing S S
  let hmod : (inferInstance : Module R (Localization.AtPrime p)) =
      Module.compHom (Localization.AtPrime p) (algebraMap R (Localization.AtPrime p)) :=
    Module.ext' (inferInstance : Module R (Localization.AtPrime p))
      (Module.compHom (Localization.AtPrime p) (algebraMap R (Localization.AtPrime p))) (by
        intro r s
        exact (algebraMap_smul (R := R) (A := Localization.AtPrime p)
          (M := Localization.AtPrime p) r s).symm)
  let _ : Module R (Localization.AtPrime p) :=
    Module.compHom (Localization.AtPrime p) (algebraMap R (Localization.AtPrime p))
  have hI : @Module.Injective R _ (Localization.AtPrime p) _
      (Module.compHom (Localization.AtPrime p) (algebraMap R (Localization.AtPrime p))) :=
    injective_of_flat (algebraMap R (Localization.AtPrime p))
      (RingHom.flat_algebraMap_iff.mpr
        (IsLocalization.flat (Localization.AtPrime p) p.primeCompl))
  have heq := congrArg (fun m : Module R (Localization.AtPrime p) =>
      @Module.Injective R _ (Localization.AtPrime p) _ m) hmod
  exact heq.mpr hI

theorem hom_to_minimal_prime_localization_equiv
    {R : Type u} [CommRing R] [IsReduced R]
    {M : Type v} [AddCommGroup M] [Module R M] (p : Ideal R) [p.IsPrime]
    (hp : IsMinimalPrime p) :
    Nonempty
      ((M →ₗ[R] Localization.AtPrime p) ≃+
        (LocalizedModule p.primeCompl M →ₗ[Localization.AtPrime p]
          Localization.AtPrime p)) := by
  have _hp : IsMinimalPrime p := hp
  let A := Localization.AtPrime p
  let hunit : ∀ s : p.primeCompl, IsUnit ((algebraMap R (Module.End R A)) s) := by
    intro s
    rw [Module.End.isUnit_iff]
    constructor
    · intro x y hxy
      apply (IsLocalization.map_units A s).mul_right_injective
      simpa [Algebra.smul_def] using hxy
    · intro x
      let hs := IsLocalization.map_units A s
      refine ⟨hs.unit⁻¹.val * x, ?_⟩
      have hmul : (algebraMap R A (s : R)) * (hs.unit⁻¹.val * x) = x := by
        calc
          (algebraMap R A (s : R)) * (hs.unit⁻¹.val * x) =
              (hs.unit : A) * (hs.unit⁻¹.val * x) := by rw [hs.unit_spec]
          _ = x := by simp [← mul_assoc]
      simpa [Algebra.smul_def] using hmul
  let fM := LocalizedModule.mkLinearMap p.primeCompl M
  have hlift_add (f g : M →ₗ[R] A) :
      IsLocalizedModule.lift p.primeCompl fM (f + g) hunit =
        IsLocalizedModule.lift p.primeCompl fM f hunit +
          IsLocalizedModule.lift p.primeCompl fM g hunit := by
    apply IsLocalizedModule.ext p.primeCompl fM hunit
    rw [IsLocalizedModule.lift_comp]
    rw [LinearMap.add_comp, IsLocalizedModule.lift_comp, IsLocalizedModule.lift_comp]
  let F : (M →ₗ[R] A) →+ (LocalizedModule p.primeCompl M →ₗ[A] A) :=
    { toFun := fun f =>
        (IsLocalizedModule.lift p.primeCompl fM f hunit).extendScalarsOfIsLocalization
          p.primeCompl A
      map_zero' := by
        have hz : IsLocalizedModule.lift p.primeCompl fM 0 hunit = 0 := by
          apply IsLocalizedModule.ext p.primeCompl fM hunit
          rw [IsLocalizedModule.lift_comp]
          simp
        apply LinearMap.ext
        intro x
        exact congrArg (fun q : LocalizedModule p.primeCompl M →ₗ[R] A => q x) hz
      map_add' := by
        intro f g
        apply LinearMap.ext
        intro x
        change (IsLocalizedModule.lift p.primeCompl fM (f + g) hunit) x = _
        rw [hlift_add]
        rfl }
  let G : (LocalizedModule p.primeCompl M →ₗ[A] A) →+ (M →ₗ[R] A) :=
    { toFun := fun g => (g.restrictScalars R).comp fM
      map_zero' := by simp
      map_add' := by
        intro f g
        ext x
        simp }
  have hGF (f : M →ₗ[R] A) : G (F f) = f := by
    ext x
    change (IsLocalizedModule.lift p.primeCompl fM f hunit) (fM x) = f x
    exact IsLocalizedModule.lift_apply p.primeCompl fM f hunit x
  have hFG (g : LocalizedModule p.primeCompl M →ₗ[A] A) : F (G g) = g := by
    have hl : IsLocalizedModule.lift p.primeCompl fM (G g) hunit = g.restrictScalars R := by
      apply IsLocalizedModule.ext p.primeCompl fM hunit
      change (IsLocalizedModule.lift p.primeCompl fM ((g.restrictScalars R).comp fM) hunit).comp fM =
        (g.restrictScalars R).comp fM
      rw [IsLocalizedModule.lift_comp]
    apply LinearMap.ext
    intro x
    change (IsLocalizedModule.lift p.primeCompl fM (G g) hunit) x = g x
    rw [hl]
    simp [LinearMap.restrictScalars_apply]
  let E : (M →ₗ[R] A) ≃+ (LocalizedModule p.primeCompl M →ₗ[A] A) :=
    { toFun := F
      invFun := G
      left_inv := hGF
      right_inv := hFG
      map_add' := by
        intro f g
        exact F.map_add f g }
  exact ⟨E⟩

/-! ### Noetherian sums, localization, and torsion -/

theorem directSum_injective
    {R : Type u} [CommRing R] [IsNoetherianRing R] {ι : Type w}
    {M : ι → Type v} [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)]
    [∀ i, Module.Injective R (M i)] [Small.{v} R] :
    Module.Injective R (DirectSum ι M) := by
  classical
  apply Module.Baer.injective
  intro I g
  obtain ⟨s, hs⟩ := I.fg_of_isNoetherianRing
  let gi (i : ι) : I →ₗ[R] M i :=
    (DirectSum.component R ι M i).comp g
  choose h hh using fun i =>
    Module.Injective.extension_property R (M i) I R I.subtype
      Subtype.val_injective (gi i)
  have hsI : ∀ x ∈ s, x ∈ I := by
    intro x hx
    rw [← hs]
    exact Submodule.subset_span (by simpa using hx)
  let t : Finset ι := s.attach.biUnion (fun x =>
    (g ⟨x.1, hsI x.1 x.2⟩).support)
  let x : DirectSum ι M := DFinsupp.mk t (fun i => h i 1)
  have hxcomp (i : ι) :
      DirectSum.component R ι M i x = if i ∈ t then h i 1 else 0 := by
    by_cases hi : i ∈ t
    · change (DFinsupp.mk t (fun i => h i 1)) i = _
      simp only [DFinsupp.mk_apply]
      split_ifs; rfl
    · change (DFinsupp.mk t (fun i => h i 1)) i = _
      simp only [DFinsupp.mk_apply]
      split_ifs; rfl
  let h' : R →ₗ[R] DirectSum ι M := LinearMap.toSpanSingleton R _ x
  have hcomp : h'.comp I.subtype = g := by
    apply LinearMap.ext
    intro a
    apply DirectSum.ext_component R
    intro i
    rw [LinearMap.comp_apply, LinearMap.toSpanSingleton_apply, map_smul]
    by_cases hi : i ∈ t
    · rw [hxcomp, if_pos hi]
      calc
        (Submodule.subtype I) a • h i 1 =
            h i ((Submodule.subtype I) a • (1 : R)) := by
              rw [map_smul]
        _ = h i ((Submodule.subtype I) a) := by simp
        _ = gi i a := DFunLike.congr_fun (hh i) a
        _ = DirectSum.component R ι M i (g a) := rfl
    · have hzero : gi i a = 0 := by
        have ha : (a : R) ∈ Submodule.span R (↑s : Set R) := by
          change (a : R) ∈ Ideal.span (↑s : Set R)
          rw [hs]
          exact a.property
        have ha' : h i (a : R) = 0 := by
          refine Submodule.span_induction
            (p := fun z _ => h i z = 0)
            (fun r hrs => by
              have hti : i ∉ (g ⟨r, hsI r hrs⟩).support := by
                intro hit
                apply hi
                simp only [t, Finset.mem_biUnion]
                exact ⟨⟨r, hrs⟩, by simp, hit⟩
              have hc : DirectSum.component R ι M i (g ⟨r, hsI r hrs⟩) = 0 := by
                change (g ⟨r, hsI r hrs⟩) i = 0
                exact DFinsupp.notMem_support_iff.mp hti
              have hgi : gi i ⟨r, hsI r hrs⟩ = 0 := by
                simpa [gi] using hc
              calc
                h i r = gi i ⟨r, hsI r hrs⟩ := by
                  simpa [LinearMap.comp_apply] using
                    DFunLike.congr_fun (hh i) ⟨r, hsI r hrs⟩
                _ = 0 := hgi)
            (by simp)
            (fun r q hr hq hpr hpq => by
              rw [map_add, hpr, hpq, add_zero])
            (fun c r hr hpr => by
              rw [map_smul, hpr, smul_zero])
            ha
        calc
          gi i a = h i (a : R) := by
            symm
            simpa [LinearMap.comp_apply] using DFunLike.congr_fun (hh i) a
          _ = 0 := ha'
      rw [hxcomp, if_neg hi]
      simp only [smul_zero]
      simpa [gi] using hzero.symm
  refine ⟨h', ?_⟩
  intro r hr
  exact DFunLike.congr_fun hcomp ⟨r, hr⟩

theorem localization_injective
    {R : Type u} {E : Type v} [CommRing R] [AddCommGroup E] [Module R E]
    [IsNoetherianRing R] [Small.{v} R] (S : Submonoid R) [Module.Injective R E] :
    Module.Injective (Localization S) (LocalizedModule S E) := by
  exact Module.injective_of_isLocalizedModule S (LocalizedModule.mkLinearMap S E)

theorem principal_power_torsion_injective
    {R I : Type*} [CommRing R] [AddCommGroup I] [Module R I]
    [IsNoetherianRing R] [Module.Injective R I] (f : R) :
    Module.Injective R (Submodule.torsion' R I (Submonoid.powers f)) := by
  classical
  let E : Submodule R I := Submodule.torsion' R I (Submonoid.powers f)
  apply (injective_iff_essential_extensions_trivial (R := R) (I := I) E).2
  intro E' hEE' hEss
  apply le_antisymm hEE'
  intro x hx
  by_contra hnot
  let j : E →ₗ[R] E' := E.inclusion hEE'
  let S : Submodule R E' := LinearMap.range j
  have hj : Function.Injective j := Submodule.inclusion_injective hEE'
  let e : E ≃ₗ[R] S :=
    LinearEquiv.ofBijective j.rangeRestrict
      ⟨(LinearMap.injective_rangeRestrict_iff j).2 hj, j.surjective_rangeRestrict⟩
  have : Mono (ModuleCat.ofHom j) := ConcreteCategory.mono_of_injective _ hj
  have : Mono (ModuleCat.ofHom S.subtype) :=
    ConcreteCategory.mono_of_injective _ Subtype.val_injective
  have heq :
      e.toModuleIso.hom ≫ ModuleCat.ofHom S.subtype = ModuleCat.ofHom j := by
    apply ModuleCat.hom_ext
    rfl
  have hmk :
      Subobject.mk (ModuleCat.ofHom j) =
        Subobject.mk (ModuleCat.ofHom S.subtype) :=
    Subobject.mk_eq_mk_of_comm (ModuleCat.ofHom j)
      (ModuleCat.ofHom S.subtype) e.toModuleIso heq
  have hEssS : EssentialSubmodule S := by
    apply (essentialSubmodule_iff_essentialExtension S).2
    unfold EssentialExtension at hEss ⊢
    rcases hEss with ⟨hmono, hess⟩
    have := hmono
    refine ⟨inferInstance, ?_⟩
    intro P hP
    rw [← hmk]
    exact hess P hP
  let g : R →ₗ[R] I := LinearMap.toSpanSingleton R I x
  let J : Ideal R := E.comap g
  obtain ⟨s, hs⟩ := J.fg_of_isNoetherianRing
  have hpow (a : R) (ha : a ∈ s) : ∃ n : ℕ, f ^ n • g a = 0 := by
    have haJ : a ∈ J := by
      rw [← hs]
      exact Submodule.subset_span (by simpa using ha)
    have haE : g a ∈ E := haJ
    obtain ⟨b, hb⟩ := (Submodule.mem_torsion'_iff (R := R) (M := I)
      (S := Submonoid.powers f) (g a)).mp haE
    obtain ⟨n, hn⟩ := b.property
    refine ⟨n, ?_⟩
    change (b : R) • g a = 0 at hb
    simpa [hn] using hb
  let n₀ : {a : R // a ∈ s} → ℕ := fun a => Nat.find (hpow a.1 a.2)
  let n : ℕ := s.attach.sup n₀
  have hn₀ (a : {a : R // a ∈ s}) : n₀ a ≤ n := Finset.le_sup (s.mem_attach a)
  have hgen (a : R) (ha : a ∈ s) : f ^ n • g a = 0 := by
    let a' : {a : R // a ∈ s} := ⟨a, ha⟩
    have hle : n₀ a' ≤ n := hn₀ a'
    have ha0 : f ^ n₀ a' • g a = 0 := Nat.find_spec (hpow a ha)
    rw [← Nat.sub_add_cancel hle, pow_add]
    calc
      (f ^ (n - n₀ a') * f ^ n₀ a') • g a =
          f ^ (n - n₀ a') • (f ^ n₀ a' • g a) := by rw [smul_smul]
      _ = 0 := by rw [ha0, smul_zero]
  have hJ (a : R) (ha : a ∈ J) : f ^ n • g a = 0 := by
    rw [← hs] at ha
    refine Submodule.span_induction (p := fun z _ => f ^ n • g z = 0)
      (fun r hr => hgen r (by simpa using hr))
      (by simp)
      (fun r q hr hq hpr hpq => by
        rw [map_add, smul_add, hpr, hpq, add_zero])
      (fun c r hr hpr => by
        rw [map_smul]
        have hpr' := congrArg (fun z : I => c • z) hpr
        simpa [smul_smul, mul_comm] using hpr')
      ha
  have hzero_of_mem (a : R) (ha : a • (f ^ n • x) ∈ E) :
      a • (f ^ n • x) = 0 := by
    have haJ : a ∈ J := by
      change a • x ∈ E
      rw [Submodule.mem_torsion'_iff]
      obtain ⟨b, hb⟩ := (Submodule.mem_torsion'_iff (R := R) (M := I)
        (S := Submonoid.powers f) (a • (f ^ n • x))).mp ha
      obtain ⟨m, hm⟩ := b.property
      refine ⟨⟨f ^ (m + n), ⟨m + n, rfl⟩⟩, ?_⟩
      change (f ^ (m + n) : R) • (a • x) = 0
      change (b : R) • (a • (f ^ n • x)) = 0 at hb
      simpa [← hm, smul_smul, pow_add, mul_comm, mul_left_comm, mul_assoc] using hb
    simpa [g, smul_smul, mul_comm] using hJ a haJ
  have hx'not : f ^ n • x ∉ E := by
    intro hx'
    rw [Submodule.mem_torsion'_iff] at hx'
    obtain ⟨b, hb⟩ := hx'
    obtain ⟨m, hm⟩ := b.property
    apply hnot
    rw [Submodule.mem_torsion'_iff]
    refine ⟨⟨f ^ (m + n), ⟨m + n, rfl⟩⟩, ?_⟩
    change (f ^ (m + n) : R) • x = 0
    change (b : R) • (f ^ n • x) = 0 at hb
    simpa [← hm, smul_smul, pow_add, mul_comm, mul_left_comm, mul_assoc] using hb
  let x' : E' := ⟨f ^ n • x, E'.smul_mem (f ^ n) hx⟩
  have hx'0 : x' ≠ 0 := by
    intro hx0
    apply hx'not
    have hxval : (f ^ n • x : I) = 0 := congrArg Subtype.val hx0
    rw [hxval]
    exact E.zero_mem
  obtain ⟨r, hrS, hr0⟩ := (essentialSubmodule_iff_smul S).1 hEssS x' hx'0
  obtain ⟨y, hy⟩ := hrS
  apply hr0
  apply Subtype.ext
  change r • (f ^ n • x) = 0
  have hy' := congrArg Subtype.val hy
  have hrmem : r • (f ^ n • x) ∈ E := by
    rw [show r • (f ^ n • x) = (y : I) by simpa [j, x'] using hy'.symm]
    exact y.property
  exact hzero_of_mem r hrmem

theorem ideal_power_torsion_injective
    {R I : Type*} [CommRing R] [AddCommGroup I] [Module R I]
    [IsNoetherianRing R] [Module.Injective R I] (J : Ideal R) :
    Module.Injective R (Ideal.primaryComponent I J) := by
  classical
  have hI : Module.Injective R I := by assumption
  have hprimary (K : Ideal R) (f : R) :
      Ideal.primaryComponent I (K ⊔ Ideal.span {f}) =
        Ideal.primaryComponent I K ⊓
          Submodule.torsion' R I (Submonoid.powers f) := by
    ext x
    constructor
    · intro hx
      rw [Ideal.primaryComponent_mem] at hx
      obtain ⟨n, hx⟩ := hx
      rw [Submodule.mem_torsionBySet_iff] at hx
      constructor
      · change x ∈ Ideal.primaryComponent I K
        rw [Ideal.primaryComponent_mem]
        refine ⟨n, ?_⟩
        rw [Submodule.mem_torsionBySet_iff]
        intro a
        exact hx ⟨(a : R), (Ideal.pow_right_mono le_sup_left n) a.property⟩
      · change x ∈ Submodule.torsion' R I (Submonoid.powers f)
        rw [Submodule.mem_torsion'_iff]
        refine ⟨⟨f ^ n, ⟨n, rfl⟩⟩, ?_⟩
        have hf : f ^ n ∈ (K ⊔ Ideal.span {f}) ^ n :=
          Ideal.pow_mem_pow (Ideal.mem_sup_right (Ideal.subset_span (by simp))) n
        change f ^ n • x = 0
        simpa using hx ⟨f ^ n, hf⟩
    · rintro ⟨hxK, hxf⟩
      change x ∈ Ideal.primaryComponent I K at hxK
      change x ∈ Submodule.torsion' R I (Submonoid.powers f) at hxf
      rw [Ideal.primaryComponent_mem] at hxK ⊢
      obtain ⟨n, hxK⟩ := hxK
      rw [Submodule.mem_torsionBySet_iff] at hxK
      rw [Submodule.mem_torsion'_iff] at hxf
      obtain ⟨b, hb⟩ := hxf
      obtain ⟨m, hm⟩ := b.property
      refine ⟨n + m, ?_⟩
      rw [Submodule.mem_torsionBySet_iff]
      intro a
      have ha : (a : R) ∈ K ^ n ⊔ (Ideal.span {f}) ^ m :=
        (Ideal.sup_pow_add_le_pow_sup_pow (I := K) (J := Ideal.span {f})
          (n := n) (m := m)) a.property
      have hAnn : K ^ n ⊔ (Ideal.span {f}) ^ m ≤ Ideal.torsionOf R I x := by
        apply sup_le
        · intro c hc
          exact (Ideal.mem_torsionOf_iff x c).2 (hxK ⟨c, hc⟩)
        · rw [Ideal.span_singleton_pow]
          apply Ideal.span_le.2
          intro c hc
          rcases Set.mem_singleton_iff.mp hc with rfl
          change (b : R) • x = 0 at hb
          simpa [← hm] using hb
      exact (Ideal.mem_torsionOf_iff x (a : R)).1 (hAnn ha)

  have htransfer {M N : Type u_2} [AddCommGroup M] [AddCommGroup N]
      [Module R M] [Module R N] (e : M ≃ₗ[R] N) (hM : Module.Injective R M) :
      Module.Injective R N := by
    let _ : Module.Injective R M := hM
    constructor
    intro X Y _ _ _ _ g hg k
    obtain ⟨l, hl⟩ := Module.Injective.out g hg (e.symm.toLinearMap.comp k)
    refine ⟨e.toLinearMap.comp l, ?_⟩
    intro x
    have hx := congrArg e (hl x)
    simpa using hx

  have hstep (E : Submodule R I) [Module.Injective R E] (f : R) :
      Module.Injective R
        ↥(E ⊓ Submodule.torsion' R I (Submonoid.powers f)) := by
    let T : Submodule R E := Submodule.torsion' R E (Submonoid.powers f)
    let φ : T →ₗ[R] I := E.subtype.comp T.subtype
    have hφ : Function.Injective φ := by
      intro x y hxy
      apply Subtype.ext
      apply Subtype.ext
      exact hxy
    have hrange : LinearMap.range φ =
        E ⊓ Submodule.torsion' R I (Submonoid.powers f) := by
      ext x
      constructor
      · rintro ⟨y, rfl⟩
        constructor
        · exact y.1.2
        · change φ y ∈ Submodule.torsion' R I (Submonoid.powers f)
          rw [Submodule.mem_torsion'_iff]
          obtain ⟨a, ha⟩ := y.2
          refine ⟨a, ?_⟩
          change (a : R) • (y.1 : I) = 0
          have ha' := congrArg Subtype.val ha
          change (a : R) • (y.1 : I) = 0 at ha'
          exact ha'
      · rintro ⟨hxE, hxT⟩
        change x ∈ Submodule.torsion' R I (Submonoid.powers f) at hxT
        rw [Submodule.mem_torsion'_iff] at hxT
        obtain ⟨a, ha⟩ := hxT
        let y : T := ⟨⟨x, hxE⟩, ?_⟩
        · exact ⟨y, by rfl⟩
        · refine ⟨a, ?_⟩
          apply Subtype.ext
          exact ha
    let e : T ≃ₗ[R] LinearMap.range φ :=
      LinearEquiv.ofBijective φ.rangeRestrict
        ⟨(LinearMap.injective_rangeRestrict_iff φ).2 hφ,
          φ.surjective_rangeRestrict⟩
    let eEq : (LinearMap.range φ) ≃ₗ[R]
        ↥(E ⊓ Submodule.torsion' R I (Submonoid.powers f)) :=
      { toFun := fun x => ⟨x, by rw [← hrange]; exact x.property⟩
        invFun := fun x => ⟨x, by rw [hrange]; exact x.property⟩
        left_inv := by intro x; rfl
        right_inv := by intro x; rfl
        map_add' := by intro x y; rfl
        map_smul' := by intro a x; rfl }
    have hT : Module.Injective R T :=
      principal_power_torsion_injective (R := R) (I := E) f
    exact htransfer (e.trans eEq) hT

  obtain ⟨s, hs⟩ := J.fg_of_isNoetherianRing
  have hfinite : ∀ s : Finset R,
      Module.Injective R ↥(Ideal.primaryComponent I (Ideal.span (s : Set R))) := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
        have hzero : Ideal.primaryComponent I (Ideal.span (∅ : Set R)) = ⊤ := by
          apply top_unique
          intro x _
          rw [Ideal.primaryComponent_mem]
          refine ⟨1, ?_⟩
          rw [Submodule.mem_torsionBySet_iff]
          intro a
          have ha : (a : R) = 0 := by simpa using a.property
          simp [ha]
        rw [show Ideal.span (↑(∅ : Finset R) : Set R) = Ideal.span (∅ : Set R) by simp,
          hzero]
        exact htransfer (M := I) (N := (⊤ : Submodule R I))
          (Submodule.topEquiv : (⊤ : Submodule R I) ≃ₗ[R] I).symm
          hI
    | @insert f s hfs ih =>
        have hspan : Ideal.span ((↑(insert f s) : Set R)) =
            Ideal.span (↑s : Set R) ⊔ Ideal.span {f} := by
          rw [Finset.coe_insert, Ideal.span_insert, sup_comm]
        rw [hspan, hprimary]
        let _ : Module.Injective R
            ↥(Ideal.primaryComponent I (Ideal.span (↑s : Set R))) := ih
        exact hstep _ f
  rw [← hs]
  exact hfinite s

/-! ### Polynomial extensions -/

def polynomial_tensorProduct_equiv
    (A E : Type u) [CommRing A] [AddCommGroup E] [Module A E] :
    (Polynomial A ⊗[A] E) ≃ₗ[Polynomial A] PolynomialModule A E :=
  PolynomialModule.polynomialTensorProductLEquivPolynomialModule A E

def polynomial_module_directSum_equiv
    (A E : Type u) [CommRing A] [AddCommGroup E] [Module A E] :
    PolynomialModule A E ≃ₗ[A] DirectSum ℕ (fun _ : ℕ => E) :=
  (PolynomialModule.coeffLinearEquiv A A).trans
    (finsuppLEquivDirectSum A E ℕ)

abbrev polynomial_hom_module
    (A E : Type u) [CommRing A] [AddCommGroup E] [Module A E] :=
  (ModuleCat.coextendScalars (algebraMap A (Polynomial A))).obj
    ((ModuleCat.restrictScalars (algebraMap A (Polynomial A))).obj
      (ModuleCat.of (Polynomial A) (PolynomialModule A E)))

abbrev polynomial_base_module
    (A : Type u) [CommRing A] :=
  (ModuleCat.restrictScalars (algebraMap A (Polynomial A))).obj
    (ModuleCat.of (Polynomial A) (Polynomial A))

def polynomial_first_map
    (A E : Type u) [CommRing A] [AddCommGroup E] [Module A E] :
    ModuleCat.of (Polynomial A) (PolynomialModule A E) →ₗ[Polynomial A]
      polynomial_hom_module A E :=
  ModuleCat.RestrictionCoextensionAdj.app' (algebraMap A (Polynomial A))
    (ModuleCat.of (Polynomial A) (PolynomialModule A E))

theorem polynomial_first_map_apply
    (A E : Type u) [CommRing A] [AddCommGroup E] [Module A E]
    (p : PolynomialModule A E) (f : polynomial_base_module A) :
    polynomial_first_map A E p f = (let f' : Polynomial A := f; f' • p) := by
  rfl

def polynomial_differential_formula
    (A E : Type u) [CommRing A] [AddCommGroup E] [Module A E]
    (φ : polynomial_hom_module A E) (f : polynomial_base_module A) :
    PolynomialModule A E :=
  let f' : Polynomial A := f
  φ (show polynomial_base_module A from
      (show Polynomial A from (Polynomial.X : Polynomial A) * f')) -
    (Polynomial.X : Polynomial A) • φ f

theorem polynomial_hom_module_as_product
    (A E : Type u) [CommRing A] [AddCommGroup E] [Module A E] :
    Nonempty
      (((ModuleCat.restrictScalars (algebraMap A (Polynomial A))).obj
          (polynomial_hom_module A E)) ≃ₗ[A]
        (ModuleCat.of A (ℕ → PolynomialModule A E))) := by
  let M := PolynomialModule A E
  let _ : Module A (polynomial_hom_module A E) :=
    ModuleCat.isModule
      ((ModuleCat.restrictScalars (algebraMap A (Polynomial A))).obj
        (polynomial_hom_module A E))
  let q := ModuleCat.CoextendScalars.equiv (algebraMap A (Polynomial A))
    ((ModuleCat.restrictScalars (algebraMap A (Polynomial A))).obj
      (ModuleCat.of (Polynomial A) M))
  let qP :
      ((ModuleCat.restrictScalars (algebraMap A (Polynomial A))).obj
          (ModuleCat.of (Polynomial A) (Polynomial A))) ≃ₗ[A] Polynomial A :=
    { toFun := fun p => p
      invFun := fun p => p
      left_inv := by intro p; rfl
      right_inv := by intro p; rfl
      map_add' := by intro p r; rfl
      map_smul' := by
        intro a p
        change Polynomial.C a * (show Polynomial A from p) =
          a • (show Polynomial A from p)
        rw [Polynomial.smul_eq_C_mul] }
  let qM :
      ((ModuleCat.restrictScalars (algebraMap A (Polynomial A))).obj
          (ModuleCat.of (Polynomial A) M)) ≃ₗ[A] M :=
    { toFun := fun m => m
      invFun := fun m => m
      left_inv := by intro m; rfl
      right_inv := by intro m; rfl
      map_add' := by intro m n; rfl
      map_smul' := by
        intro a m
        change Polynomial.C a • (show M from m) = a • (show M from m)
        rw [Polynomial.C_eq_algebraMap]
        exact algebraMap_smul (Polynomial A) a (show M from m) }
  let qA :
      ((ModuleCat.coextendScalars (algebraMap A (Polynomial A))).obj
        ((ModuleCat.restrictScalars (algebraMap A (Polynomial A))).obj
          (ModuleCat.of (Polynomial A) M))) ≃ₗ[A]
        ((ModuleCat.restrictScalars (algebraMap A (Polynomial A))).obj
          (ModuleCat.of (Polynomial A) (Polynomial A)) →ₗ[A]
            (ModuleCat.restrictScalars (algebraMap A (Polynomial A))).obj
              (ModuleCat.of (Polynomial A) M)) :=
    { toFun := q
      invFun := q.symm
      left_inv := q.left_inv
      right_inv := q.right_inv
      map_add' := q.map_add
      map_smul' := by
        intro a z
        apply LinearMap.ext
        intro p
        change (a • z) p = a • (q z) p
        change q (a • z) p = a • (q z) p
        calc
          q (a • z) p = q (Polynomial.C a • z) p := by
            congr 1
          _ = (Polynomial.C a • q z) p := by rw [q.map_smul]
          _ = (q z) ((show Polynomial A from p) * Polynomial.C a) := by rfl
          _ = (q z) (a • p) := by
            congr 1
            change (show Polynomial A from p) * (algebraMap A (Polynomial A)) a =
              (algebraMap A (Polynomial A)) a * (show Polynomial A from p)
            rw [mul_comm]
          _ = a • (q z) p := (q z).map_smul a p
          _ = (algebraMap A (Polynomial A)) a • (q z) p := by
            exact ModuleCat.restrictScalars.smul_def
              (algebraMap A (Polynomial A)) a ((q z) p) }
  let ePoly :
      ((ModuleCat.restrictScalars (algebraMap A (Polynomial A))).obj
          (polynomial_hom_module A E)) ≃ₗ[A] (Polynomial A →ₗ[A] M) :=
    qA.trans (LinearEquiv.arrowCongr qP qM)
  let eCoeff : AddMonoidAlgebra A ℕ ≃ₗ[A] (ℕ →₀ A) :=
    { toFun := AddMonoidAlgebra.coeff
      invFun := AddMonoidAlgebra.ofCoeff
      left_inv := by intro x; exact AddMonoidAlgebra.ofCoeff_coeff x
      right_inv := by intro x; exact AddMonoidAlgebra.coeff_ofCoeff x
      map_add' := by intro x y; rfl
      map_smul' := by intro a x; rfl }
  let eCoeffHom : (AddMonoidAlgebra A ℕ →ₗ[A] M) ≃ₗ[A]
      ((ℕ →₀ A) →ₗ[A] M) :=
    { toFun := fun g => g.comp eCoeff.symm.toLinearMap
      invFun := fun g => g.comp eCoeff.toLinearMap
      left_inv := by intro g; ext x; simp
      right_inv := by intro g; ext x; simp
      map_add' := by intro g h; ext x; simp
      map_smul' := by intro a g; ext x; simp }
  let eF :
      (ℕ → M) ≃ₗ[A] (AddMonoidAlgebra A ℕ →ₗ[A] M) :=
    (Finsupp.llift M A A ℕ).trans eCoeffHom.symm
  let eC :
      (AddMonoidAlgebra A ℕ →ₗ[A] M) ≃ₗ[A] (Polynomial A →ₗ[A] M) :=
    LinearEquiv.arrowCongr (Polynomial.toFinsuppIsoLinear A).symm
      (LinearEquiv.refl A M)
  exact ⟨ePoly.trans (eF.trans eC).symm⟩

theorem polynomial_short_exact
    (A E : Type u) [CommRing A] [AddCommGroup E] [Module A E] :
    ∃ d : polynomial_hom_module A E →ₗ[Polynomial A] polynomial_hom_module A E,
      (∀ φ f, d φ f = polynomial_differential_formula A E φ f) ∧
        Function.Injective (polynomial_first_map A E) ∧
      Function.Exact (polynomial_first_map A E) d ∧
        Function.Surjective d := by
  let mulRight (p : Polynomial A) :
      polynomial_base_module A →ₗ[A] polynomial_base_module A :=
    { toFun := fun f =>
        let f' : Polynomial A := f
        let z : Polynomial A := f' * p
        z
      map_add' := by
        intro f g
        let f' : Polynomial A := f
        let g' : Polynomial A := g
        change (f' + g') * p = f' * p + g' * p
        rw [add_mul]
      map_smul' := by
        intro a f
        let f' : Polynomial A := f
        change ((algebraMap A (Polynomial A)) a * f') * p =
          (algebraMap A (Polynomial A)) a * (f' * p)
        rw [mul_assoc] }
  let M := (ModuleCat.restrictScalars (algebraMap A (Polynomial A))).obj
    (ModuleCat.of (Polynomial A) (PolynomialModule A E))
  let outX : M →ₗ[A] M :=
    { toFun := fun m => (Polynomial.X : Polynomial A) • m
      map_add' := by intro m n; rw [smul_add]
      map_smul' := by
        intro a m
        change (Polynomial.X : Polynomial A) •
            ((algebraMap A (Polynomial A)) a • (m : PolynomialModule A E)) =
          (algebraMap A (Polynomial A)) a •
            ((Polynomial.X : Polynomial A) • (m : PolynomialModule A E))
        rw [smul_comm (Polynomial.X : Polynomial A) (algebraMap A (Polynomial A) a)] }
  let q := ModuleCat.CoextendScalars.equiv (algebraMap A (Polynomial A)) M
  have hsmul
      (g : polynomial_base_module A →ₗ[A] M) (p : Polynomial A) :
      p • g = g.comp (mulRight p) := by
    apply LinearMap.ext
    intro f
    rfl
  have hcomm (p r : Polynomial A) :
      (mulRight p).comp (mulRight r) = (mulRight r).comp (mulRight p) := by
    apply LinearMap.ext
    intro f
    let f' : Polynomial A := f
    change (f' * r) * p = (f' * p) * r
    ring
  let delta (φ : polynomial_hom_module A E) :
      polynomial_base_module A →ₗ[A] M :=
    (q φ).comp (mulRight (Polynomial.X : Polynomial A)) - outX.comp (q φ)
  let d : polynomial_hom_module A E →ₗ[Polynomial A] polynomial_hom_module A E :=
    { toFun := fun φ => q.symm (delta φ)
      map_add' := by
        intro φ ψ
        have hdelta : delta (φ + ψ) = delta φ + delta ψ := by
          apply LinearMap.ext
          intro f
          dsimp [delta]
          rw [q.map_add]
          rw [LinearMap.add_apply, LinearMap.add_apply]
          rw [outX.map_add]
          simp only [sub_add_sub_comm]
        rw [hdelta, q.symm.map_add]
      map_smul' := by
        intro p φ
        rw [← q.symm.map_smul]
        apply q.symm.injective
        change delta (p • φ) = p • delta φ
        dsimp [delta]
        rw [q.map_smul]
        rw [hsmul (q φ) p]
        rw [hsmul ((q φ).comp (mulRight (Polynomial.X : Polynomial A)) -
          outX.comp (q φ)) p]
        apply LinearMap.ext
        intro f
        simp only [LinearMap.sub_apply, LinearMap.comp_apply]
        have hc := congrArg (fun g : polynomial_base_module A →ₗ[A] polynomial_base_module A =>
          g f) (hcomm p (Polynomial.X : Polynomial A))
        simpa using congrArg (q φ) hc }
  refine ⟨d, ?_, ?_, ?_, ?_⟩
  intro φ f
  change q (d φ) f = (show M from polynomial_differential_formula A E φ f)
  dsimp [d]
  rw [q.apply_symm_apply]
  change (delta φ) f =
    (q φ) (show polynomial_base_module A from
      (show Polynomial A from (Polynomial.X : Polynomial A) * (show Polynomial A from f))) -
      (Polynomial.X : Polynomial A) • q φ f
  dsimp [delta, outX]
  have hmul : (mulRight (Polynomial.X : Polynomial A)) f =
      (show polynomial_base_module A from
        (show Polynomial A from (Polynomial.X : Polynomial A) * (show Polynomial A from f))) := by
    change (show Polynomial A from f) * (Polynomial.X : Polynomial A) =
      (Polynomial.X : Polynomial A) * (show Polynomial A from f)
    ring
  rw [hmul]
  · intro p r h
    have h1 := congrArg (fun F => F
      (show polynomial_base_module A from (1 : Polynomial A))) h
    change (1 : Polynomial A) • p = (1 : Polynomial A) • r at h1
    simpa only [one_smul] using h1
  · intro φ
    constructor
    · intro hφ
      have hdelta : delta φ = 0 := by
        have h := congrArg q hφ
        simpa [d] using h
      let p : M := q φ (show polynomial_base_module A from (1 : Polynomial A))
      have hX (f : Polynomial A) :
          q φ (show polynomial_base_module A from (Polynomial.X : Polynomial A) * f) =
            (Polynomial.X : Polynomial A) • q φ f := by
        have hf := congrArg (fun F => F (show polynomial_base_module A from f)) hdelta
        change (q φ) ((mulRight (Polynomial.X : Polynomial A)) f) -
            (Polynomial.X : Polynomial A) • q φ f = 0 at hf
        have hf' := sub_eq_zero.mp hf
        change q φ (f * (Polynomial.X : Polynomial A)) =
          (Polynomial.X : Polynomial A) • q φ f at hf'
        simpa [mul_comm] using hf'
      have hvalue (f : Polynomial A) :
          q φ (show polynomial_base_module A from f) = f • p := by
        induction f using Polynomial.induction_on' with
        | add f g hf hg =>
            change q φ (f + g) = (f + g) • p
            calc
              q φ (show polynomial_base_module A from f + g) =
                  q φ (show polynomial_base_module A from f) +
                    q φ (show polynomial_base_module A from g) :=
                (q φ).map_add _ _
              _ = f • p + g • p := by rw [hf, hg]
              _ = (f + g) • p := (add_smul f g p).symm
        | monomial n a =>
            induction n with
            | zero =>
                change q φ (Polynomial.C a) = (Polynomial.C a) • p
                have hbase :
                    (show polynomial_base_module A from Polynomial.C a) =
                      a • (show polynomial_base_module A from (1 : Polynomial A)) := by
                  change (Polynomial.C a : Polynomial A) =
                    (algebraMap A (Polynomial A) a) * (1 : Polynomial A)
                  rw [Polynomial.C_eq_algebraMap, mul_one]
                calc
                  q φ (show polynomial_base_module A from Polynomial.C a) =
                      q φ (a • (show polynomial_base_module A from (1 : Polynomial A))) := by
                    exact congrArg (q φ) hbase
                  _ = a • q φ (show polynomial_base_module A from (1 : Polynomial A)) :=
                    (q φ).map_smul a _
                  _ = (Polynomial.C a) • p := by
                    dsimp [p]
                    rw [Polynomial.C_eq_algebraMap]
                    rfl
            | succ n ih =>
                rw [show (Polynomial.monomial (Nat.succ n) a : Polynomial A) =
                  (Polynomial.X : Polynomial A) * Polynomial.monomial n a by
                  rw [← Polynomial.monomial_mul_X, mul_comm]]
                rw [hX, ih, smul_smul]
      refine ⟨p, ?_⟩
      apply q.injective
      apply LinearMap.ext
      intro f
      change q (polynomial_first_map A E p) f = q φ f
      exact (hvalue f).symm
    · rintro ⟨p, rfl⟩
      change q.symm (delta (polynomial_first_map A E p)) = q.symm 0
      apply congrArg q.symm
      apply LinearMap.ext
      intro f
      dsimp [delta]
      let f' : Polynomial A := f
      change ((f' * (Polynomial.X : Polynomial A)) • p) -
          (Polynomial.X : Polynomial A) •
            (f' • p) = 0
      rw [mul_smul, smul_comm, sub_self]
  · intro ψ
    let eCoeff : AddMonoidAlgebra A ℕ ≃ₗ[A] (ℕ →₀ A) :=
      { toFun := AddMonoidAlgebra.coeff
        invFun := AddMonoidAlgebra.ofCoeff
        left_inv := by intro x; exact AddMonoidAlgebra.ofCoeff_coeff x
        right_inv := by intro x; exact AddMonoidAlgebra.coeff_ofCoeff x
        map_add' := by intro x y; rfl
        map_smul' := by intro a x; rfl }
    let eCoeffHom : (AddMonoidAlgebra A ℕ →ₗ[A] M) ≃ₗ[A]
        ((ℕ →₀ A) →ₗ[A] M) :=
      { toFun := fun g => g.comp eCoeff.symm.toLinearMap
        invFun := fun g => g.comp eCoeff.toLinearMap
        left_inv := by intro g; ext x; simp
        right_inv := by intro g; ext x; simp
        map_add' := by intro g h; ext x; simp
        map_smul' := by intro a g; ext x; simp }
    let eF :
        (ℕ → M) ≃ₗ[A] (AddMonoidAlgebra A ℕ →ₗ[A] M) :=
      (Finsupp.llift M A A ℕ).trans eCoeffHom.symm
    let eC :
        (AddMonoidAlgebra A ℕ →ₗ[A] M) ≃ₗ[A] (Polynomial A →ₗ[A] M) :=
      LinearEquiv.arrowCongr (Polynomial.toFinsuppIsoLinear A).symm
        (LinearEquiv.refl A M)
    let qP : polynomial_base_module A ≃ₗ[A] Polynomial A :=
      { toFun := fun p => p
        invFun := fun p => p
        left_inv := by intro p; rfl
        right_inv := by intro p; rfl
        map_add' := by intro p r; rfl
        map_smul' := by
          intro a p
          change Polynomial.C a * (show Polynomial A from p) =
            a • (show Polynomial A from p)
          rw [Polynomial.smul_eq_C_mul] }
    let v : ℕ → M :=
      Nat.rec 0 (fun n z => q ψ
        (show polynomial_base_module A from (Polynomial.X : Polynomial A) ^ n) +
        outX z)
    let g : polynomial_base_module A →ₗ[A] M :=
      (eF.trans eC v).comp qP.toLinearMap
    let φ : polynomial_hom_module A E := q.symm g
    have hv (n : ℕ) :
        v (n + 1) = q ψ
            (show polynomial_base_module A from (Polynomial.X : Polynomial A) ^ n) +
          outX (v n) := by
      rfl
    have hg (n : ℕ) (a : A) :
        g (show polynomial_base_module A from Polynomial.monomial n a) = a • v n := by
      change (eF.trans eC v) (Polynomial.monomial n a) = a • v n
      dsimp [eF, eC, eCoeffHom, eCoeff]
      simp
      change (Finsupp.single n a).sum (fun x r => r • v x) = a • v n
      rw [Finsupp.sum_single_index
        (h := fun x r => r • v x)
        (h_zero := by exact zero_smul A (v n))]
    have hdeltaψ (f : Polynomial A) :
        (delta φ) (show polynomial_base_module A from f) = q ψ f := by
      induction f using Polynomial.induction_on' with
      | add f h hf hh =>
          calc
            (delta φ) (show polynomial_base_module A from f + h) =
                delta φ (show polynomial_base_module A from f) +
                  delta φ (show polynomial_base_module A from h) :=
              (delta φ).map_add _ _
            _ = q ψ f + q ψ h := by rw [hf, hh]
            _ = q ψ (f + h) := (q ψ).map_add _ _ |>.symm
      | monomial n a =>
          dsimp [delta]
          change q φ (mulRight (Polynomial.X : Polynomial A)
              (show polynomial_base_module A from Polynomial.monomial n a)) -
            outX (q φ (show polynomial_base_module A from Polynomial.monomial n a)) =
              q ψ (Polynomial.monomial n a)
          rw [show (mulRight (Polynomial.X : Polynomial A))
              (show polynomial_base_module A from Polynomial.monomial n a) =
              (show polynomial_base_module A from Polynomial.monomial (n + 1) a) by
                change Polynomial.monomial n a * (Polynomial.X : Polynomial A) =
                  Polynomial.monomial (n + 1) a
                exact Polynomial.monomial_mul_X n a]
          have hqφ (f : Polynomial A) :
              q φ (show polynomial_base_module A from f) = g f := by
            dsimp [φ]
            rw [q.apply_symm_apply]
          rw [hqφ, hqφ, hg, hg, hv]
          rw [outX.map_smul]
          rw [show (Polynomial.monomial n a : Polynomial A) =
              a • (Polynomial.X ^ n) by
                rw [Algebra.smul_def, ← Polynomial.C_eq_algebraMap,
                  Polynomial.C_mul_X_pow_eq_monomial]]
          rw [smul_add, add_sub_cancel_right]
          have hpow :
              (show polynomial_base_module A from a • (Polynomial.X ^ n)) =
                a • (show polynomial_base_module A from (Polynomial.X ^ n)) := by
            change (a • (Polynomial.X ^ n : Polynomial A)) =
              (algebraMap A (Polynomial A) a) * Polynomial.X ^ n
            rw [Polynomial.smul_eq_C_mul, Polynomial.C_eq_algebraMap]
          calc
            a • (q ψ) (show polynomial_base_module A from Polynomial.X ^ n) =
                (q ψ) (a • (show polynomial_base_module A from Polynomial.X ^ n)) :=
              ((q ψ).map_smul a
                (show polynomial_base_module A from Polynomial.X ^ n)).symm
            _ = (q ψ) (show polynomial_base_module A from a • (Polynomial.X ^ n)) :=
              congrArg (q ψ) hpow.symm
    refine ⟨φ, ?_⟩
    apply q.injective
    change delta φ = q ψ
    dsimp [φ]
    exact LinearMap.ext hdeltaψ

theorem polynomial_module_injective_amplitude
    (A E : Type u) [CommRing A] [AddCommGroup E] [Module A E]
    [IsNoetherianRing A] [Module.Injective A E] :
    CategoryTheory.HasInjectiveDimensionLE
        (ModuleCat.of (Polynomial A) (PolynomialModule A E)) 1 ∧
      CategoryTheory.injectiveDimension
          (ModuleCat.of (Polynomial A) (PolynomialModule A E)) ≠ ⊤ := by
  have hD : Module.Injective A (DirectSum ℕ (fun _ : ℕ => E)) :=
    directSum_injective
  let eR :
      ((ModuleCat.restrictScalars (algebraMap A (Polynomial A))).obj
        (ModuleCat.of (Polynomial A) (PolynomialModule A E)) : Type _) ≃ₗ[A]
      DirectSum ℕ (fun _ : ℕ => E) :=
    { toFun := fun p => polynomial_module_directSum_equiv A E p
      invFun := fun p => (polynomial_module_directSum_equiv A E).symm p
      left_inv := by
        intro p
        exact (polynomial_module_directSum_equiv A E).symm_apply_apply p
      right_inv := by
        intro p
        exact (polynomial_module_directSum_equiv A E).apply_symm_apply p
      map_add' := by
        intro p r
        exact (polynomial_module_directSum_equiv A E).map_add p r
      map_smul' := by
        intro a p
        change polynomial_module_directSum_equiv A E
            (Polynomial.C a • (show PolynomialModule A E from p)) = a •
          polynomial_module_directSum_equiv A E p
        rw [Polynomial.C_eq_algebraMap, algebraMap_smul (Polynomial A)]
        exact (polynomial_module_directSum_equiv A E).map_smul a p }
  have hR : Module.Injective A
      ((ModuleCat.restrictScalars (algebraMap A (Polynomial A))).obj
        (ModuleCat.of (Polynomial A) (PolynomialModule A E)) : Type _) := by
    constructor
    intro X Y _ _ _ _ f hf g
    obtain ⟨h, hh⟩ := Module.Injective.out (self := hD) f hf
      (eR.toLinearMap.comp g)
    refine ⟨eR.symm.toLinearMap.comp h, ?_⟩
    intro x
    change eR.symm (h (f x)) = g x
    rw [hh]
    simp
  have hhom : Module.Injective (Polynomial A) (polynomial_hom_module A E) :=
    @hom_injective A (Polynomial A)
      ((ModuleCat.restrictScalars (algebraMap A (Polynomial A))).obj
        (ModuleCat.of (Polynomial A) (PolynomialModule A E)) : Type _)
      inferInstance inferInstance inferInstance inferInstance inferInstance
      (algebraMap A (Polynomial A)) hR
  obtain ⟨d, _, hinj, hex, hsurj⟩ := polynomial_short_exact A E
  let S : ShortComplex (ModuleCat (Polynomial A)) :=
    ShortComplex.moduleCatMk (polynomial_first_map A E) d hex.linearMap_comp_eq_zero
  have hS : S.ShortExact :=
    ModuleCat.shortComplex_shortExact S hex hinj hsurj
  have hX2 : CategoryTheory.Injective S.X₂ := by
    change CategoryTheory.Injective
      (ModuleCat.of (Polynomial A) (polynomial_hom_module A E))
    exact Module.injective_object_of_injective_module (inj := hhom)
      (Polynomial A) (polynomial_hom_module A E)
  have hX3 : CategoryTheory.Injective S.X₃ := by
    change CategoryTheory.Injective
      (ModuleCat.of (Polynomial A) (polynomial_hom_module A E))
    exact Module.injective_object_of_injective_module (inj := hhom)
      (Polynomial A) (polynomial_hom_module A E)
  have hX3dim : CategoryTheory.HasInjectiveDimensionLT S.X₃ 1 :=
    CategoryTheory.injective_iff_hasInjectiveDimensionLT_one.mp hX3
  have hX2dim1 : CategoryTheory.HasInjectiveDimensionLT S.X₂ 1 :=
    CategoryTheory.injective_iff_hasInjectiveDimensionLT_one.mp hX2
  have hX2dim : CategoryTheory.HasInjectiveDimensionLT S.X₂ 2 := by
    exact @CategoryTheory.hasInjectiveDimensionLT_of_ge _ _ _ S.X₂ 1 2
      (by norm_num) hX2dim1
  have hdimS : CategoryTheory.HasInjectiveDimensionLT S.X₁ 2 :=
    hS.hasInjectiveDimensionLT_X₁ 1 hX3dim hX2dim
  have hdim : CategoryTheory.HasInjectiveDimensionLE
      (ModuleCat.of (Polynomial A) (PolynomialModule A E)) 1 := by
    exact hdimS
  refine ⟨hdim, ?_⟩
  apply (CategoryTheory.injectiveDimension_ne_top_iff _).2
  exact ⟨1, hdim⟩

end
end Formalization.Books.Dualizing.Unit03
