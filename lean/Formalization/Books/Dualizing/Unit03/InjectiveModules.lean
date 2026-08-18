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
            change s • gR (x + y) = s • gR x + s • gR y
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
    letI : Mono (ModuleCat.ofHom j) :=
      ConcreteCategory.mono_of_injective _ hj
    letI : Mono (ModuleCat.ofHom S.subtype) :=
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
      letI := hmono
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
    simpa [j] using (α x').property
  · intro htriv
    refine ⟨?_⟩
    intro X Y _ _ _ _ i hi g
    letI : Fact (Function.Injective i) := ⟨hi⟩
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
      letI : Mono (ModuleCat.ofHom (E.inclusion hHE)) :=
        ConcreteCategory.mono_of_injective _ (Submodule.inclusion_injective hHE)
      letI : Mono (ModuleCat.ofHom jH) :=
        ConcreteCategory.mono_of_injective _ hjH
      letI : Mono (ModuleCat.ofHom S.subtype) :=
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
        letI := hmono
        refine ⟨inferInstance, ?_⟩
        intro P hP
        rw [hmk]
        exact hess P hP
      have hKexists : ∃ K : Submodule R H, K ≠ ⊥ ∧ S ⊓ K = ⊥ := by
        by_contra hK
        apply hnotS
        intro K hKne
        intro hzero
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
  sorry

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
  sorry

theorem hom_to_minimal_prime_localization_equiv
    {R : Type u} [CommRing R] [IsReduced R]
    {M : Type v} [AddCommGroup M] [Module R M] (p : Ideal R) [p.IsPrime]
    (hp : IsMinimalPrime p) :
    Nonempty
      ((M →ₗ[R] Localization.AtPrime p) ≃+
        (LocalizedModule p.primeCompl M →ₗ[Localization.AtPrime p]
          Localization.AtPrime p)) := by
  sorry

/-! ### Noetherian sums, localization, and torsion -/

theorem directSum_injective
    {R : Type u} [CommRing R] [IsNoetherianRing R] {ι : Type w}
    {M : ι → Type v} [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)]
    [∀ i, Module.Injective R (M i)] [Small.{v} R] :
    Module.Injective R (DirectSum ι M) := by
  sorry

theorem localization_injective
    {R : Type u} {E : Type v} [CommRing R] [AddCommGroup E] [Module R E]
    [IsNoetherianRing R] [Small.{v} R] (S : Submonoid R) [Module.Injective R E] :
    Module.Injective (Localization S) (LocalizedModule S E) := by
  sorry

theorem principal_power_torsion_injective
    {R I : Type*} [CommRing R] [AddCommGroup I] [Module R I]
    [IsNoetherianRing R] [Module.Injective R I] (f : R) :
    Module.Injective R (Submodule.torsion' R I (Submonoid.powers f)) := by
  sorry

theorem ideal_power_torsion_injective
    {R I : Type*} [CommRing R] [AddCommGroup I] [Module R I]
    [IsNoetherianRing R] [Module.Injective R I] (J : Ideal R) :
    Module.Injective R (Ideal.primaryComponent I J) := by
  sorry

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
  sorry

theorem polynomial_short_exact
    (A E : Type u) [CommRing A] [AddCommGroup E] [Module A E] :
    ∃ d : polynomial_hom_module A E →ₗ[Polynomial A] polynomial_hom_module A E,
      (∀ φ f, d φ f = polynomial_differential_formula A E φ f) ∧
        Function.Injective (polynomial_first_map A E) ∧
        Function.Exact (polynomial_first_map A E) d ∧
        Function.Surjective d := by
  sorry

theorem polynomial_module_injective_amplitude
    (A E : Type u) [CommRing A] [AddCommGroup E] [Module A E]
    [IsNoetherianRing A] [Module.Injective A E] :
    CategoryTheory.HasInjectiveDimensionLE
        (ModuleCat.of (Polynomial A) (PolynomialModule A E)) 1 ∧
      CategoryTheory.injectiveDimension
          (ModuleCat.of (Polynomial A) (PolynomialModule A E)) ≠ ⊤ := by
  sorry

end
end Formalization.Books.Dualizing.Unit03
