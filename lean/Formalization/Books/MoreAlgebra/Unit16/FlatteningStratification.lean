import Formalization.Books.Algebra.Unit14.BaseChange
import Formalization.Books.Algebra.Unit39.FlatModules
import Mathlib.Algebra.Module.Torsion.Basic

/-!
# More on Algebra, Chapter 16: Flattening stratification

The source's base changes are represented by the canonical extension-of-scalars
model `Formalization.Books.Algebra.Unit14.baseChangeModule`.  This retains the
`S ⊗[R] R'`-module structure while giving the module its induced `R'`-action.
-/

namespace Formalization.Books.MoreAlgebra.Unit16

open scoped TensorProduct

universe u v

noncomputable section

/-! ## Flattening stratification -/

/- The source's notation `S' = S ⊗[R] R'` and `M' = M ⊗[R] R'` is already
   implemented by the earlier chapter's `baseChangeRingMap` and
   `baseChangeModule`; no parallel base-change construction is introduced. -/

/-- A ring map `R → R'` flattens an `S`-module `M` when its base change is flat
over the base-changed ring `R'`.  The base-changed module uses the canonical
extension-of-scalars model from the earlier base-change chapter. -/
def Flattens
    {R S R' M : Type*} [CommRing R] [CommRing S] [CommRing R']
    [AddCommGroup M] [Module S M]
    (f : R →+* S) (g : R →+* R') : Prop :=
  letI : Algebra R S := f.toAlgebra
  letI : Algebra R R' := g.toAlgebra
  letI : Algebra R' (S ⊗[R] R') :=
    (Formalization.Books.Algebra.Unit14.baseChangeRingMap f g).toAlgebra
  letI : Module R' (Formalization.Books.Algebra.Unit14.baseChangeModule
      (M := M) f g) :=
    Module.compHom
      (Formalization.Books.Algebra.Unit14.baseChangeModule (M := M) f g)
      (Formalization.Books.Algebra.Unit14.baseChangeRingMap f g)
  Module.Flat R'
    (Formalization.Books.Algebra.Unit14.baseChangeModule (M := M) f g)

/-- The universal property of a flattening: it is a flattening, and every
other flattening `R → R''` factors through it by a ring map over `R`. -/
def IsUniversalFlattening
    {R S R' M : Type*} [CommRing R] [CommRing S] [CommRing R']
    [AddCommGroup M] [Module S M]
    (f : R →+* S) (g : R →+* R') : Prop :=
  Flattens (M := M) f g ∧
    ∀ (R'' : Type*) [CommRing R''] (g' : R →+* R''),
      Flattens (M := M) f g' → ∃ h : R' →+* R'', h.comp g = g'

/- The opening discussion of the collection of flattening maps is represented
   by `Flattens` and `IsUniversalFlattening`.  The statement that a universal
   solution “usually does not exist” is intentionally left as prose:
   “usually” is not a precise proposition.  The scheme-theoretic setting
   `𝓕 / X / S`, and the conditional identification of the corresponding
   morphism `Spec(R_univ) ⟶ Spec(R)` as a universal flattening of `M tilde`,
   are roadmap assertions for the later scheme-theoretic source section and
   have no separate algebraic declaration at this source boundary. -/

private def quotient_restrictScalars_equiv
    {R A M : Type*} [CommRing R] [CommRing A] [AddCommGroup M]
    [Module R M] [Module A M] [Algebra R A] [IsScalarTower R A M]
    (p : Submodule A M) :
    (M ⧸ p) ≃ₗ[R] (M ⧸ p.restrictScalars R) := by
  let pR : Submodule R M := p.restrictScalars R
  let e : (M ⧸ p) ≃ₗ[R] (M ⧸ pR) := {
    toFun := Quotient.lift (fun x => (Submodule.Quotient.mk x : M ⧸ pR)) (by
      intro x y hxy
      rw [Submodule.Quotient.eq]
      simpa [pR] using p.quotientRel_def.mp hxy)
    invFun := Quotient.lift (fun x => (Submodule.Quotient.mk x : M ⧸ p)) (by
      intro x y hxy
      rw [Submodule.Quotient.eq]
      simpa [pR] using pR.quotientRel_def.mp hxy)
    map_add' := by
      intro x y
      induction x using Submodule.Quotient.induction_on with
      | _ x =>
        induction y using Submodule.Quotient.induction_on with
        | _ y => rfl
    map_smul' := by
      intro r x
      induction x using Submodule.Quotient.induction_on with
      | _ x => rfl
    left_inv := by
      intro x
      induction x using Submodule.Quotient.induction_on with
      | _ x => rfl
    right_inv := by
      intro x
      induction x using Submodule.Quotient.induction_on with
      | _ x => rfl
  }
  exact e

private theorem flat_of_ringEquiv_of_addEquiv
    {B C S T : Type*} [CommRing B] [CommRing C]
    [AddCommGroup S] [AddCommGroup T] [Module B S] [Module C T]
    (eRing : B ≃+* C) (eAdd : S ≃+ T)
    (hsmul : ∀ (c : C) (x : S),
      eAdd (eRing.symm c • x) = c • eAdd x)
    (hT : Module.Flat C T) : Module.Flat B S :=
  letI : Algebra B C := eRing.toRingHom.toAlgebra
  letI : Module C S := Module.compHom S eRing.symm.toRingHom
  let eMod : S ≃ₗ[C] T := {
    __ := eAdd
    map_smul' := by
      intro c x
      exact hsmul c x
  }
  let eRingLin : B ≃ₗ[B] C := {
    __ := eRing.toAddEquiv
    map_smul' := by
      intro b c
      change eRing (b * c) = eRing b * eRing c
      exact eRing.map_mul b c
  }
  letI : Module.Flat B C := Module.Flat.of_linearEquiv eRingLin.symm
  letI : Module.Flat C T := hT
  letI : Module.Flat C S := Module.Flat.of_linearEquiv eMod
  letI : IsScalarTower B C S := ⟨by
    intro b c x
    change eRing.symm (eRing b * c) • x = b • (eRing.symm c • x)
    rw [map_mul, eRing.symm_apply_apply]
    rw [mul_smul]
  ⟩
  Module.Flat.trans B C S

/-! ## The intersection lemma -/

/-- If the reductions of an `R`-module modulo two ideals are flat over the
corresponding quotient rings, then the reduction modulo their intersection is
flat over the quotient by that intersection.  Ideal intersection is written
using the canonical lattice infimum `I₁ ⊓ I₂`. -/
private theorem flat_of_flat_quotients_of_inf_eq_bot
    {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (I₁ I₂ : Ideal R) (hI : I₁ ⊓ I₂ = ⊥)
    (h₁ : Module.Flat (R ⧸ I₁)
      (M ⧸ (I₁ • (⊤ : Submodule R M))))
    (h₂ : Module.Flat (R ⧸ I₂)
      (M ⧸ (I₂ • (⊤ : Submodule R M)))) :
    Module.Flat R M := by
  rw [Module.Flat.iff_rTensor_injective']
  intro J
  let A := R ⧸ I₁
  let N := M ⧸ (I₁ • (⊤ : Submodule R M))
  let P : Ideal A := J.map I₁.mkQ
  have hA : Function.Surjective (algebraMap R A) := by
    simpa [A] using Ideal.Quotient.mk_surjective
  let e0 : (A ⊗[R] M) ≃ₗ[A] N :=
    (TensorProduct.quotTensorEquivQuotSMul M I₁).extendScalarsOfSurjective
      hA
  let ebase : (P ⊗[A] (A ⊗[R] M)) ≃ₗ[A] (P ⊗[R] M) :=
    TensorProduct.AlgebraTensorModule.cancelBaseChange R A A P M
  let e1 : (P ⊗[R] M) ≃ₗ[A] (P ⊗[A] N) :=
    ebase.symm ≪≫ₗ
      TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl A P) e0
  have hP : Function.Injective (P.subtype.rTensor N) :=
    (Module.Flat.iff_rTensor_injective'.mp h₁) P
  let qM : M →ₗ[R] N := (I₁ • (⊤ : Submodule R M)).mkQ
  have he0 (m : M) : e0 (1 ⊗ₜ[R] m) = qM m := by
    change (TensorProduct.quotTensorEquivQuotSMul M I₁) (1 ⊗ₜ[R] m) = qM m
    rw [TensorProduct.quotTensorEquivQuotSMul_mk_one_tmul]
    rfl
  let φP : (P ⊗[R] M) →ₗ[R] N :=
    (TensorProduct.lid A N).restrictScalars R ∘ₗ
      (P.subtype.rTensor N).restrictScalars R ∘ₗ e1.restrictScalars R
  let φP0 : (P ⊗[R] M) →ₗ[R] N := TensorProduct.lift {
    toFun := fun p => {
      toFun := fun m => (p : A) • qM m
      map_add' := by intro m n; simp
      map_smul' := by
        intro r m
        rw [qM.map_smul, smul_comm]
        simp
    }
    map_add' := by
      intro p p'
      ext m
      dsimp
      rw [add_smul]
    map_smul' := by
      intro r p
      ext m
      dsimp
      rw [smul_assoc]
  }
  have hφP0 : φP = φP0 := by
    apply TensorProduct.ext'
    intro p m
    simp [φP, φP0, qM, e1, ebase]
    rw [he0]
  have hφP : Function.Injective φP := by
    exact (TensorProduct.lid A N).injective.comp
      (hP.comp e1.injective)
  let f : J →ₗ[R] P := {
    toFun := fun x => ⟨I₁.mkQ x, Ideal.mem_map_of_mem I₁.mkQ x.property⟩
    map_add' := by intro x y; ext; simp
    map_smul' := by
      intro r x
      apply Subtype.ext
      change (Ideal.Quotient.mk I₁ r) * (Ideal.Quotient.mk I₁ (x : R)) =
        algebraMap R A r * (Ideal.Quotient.mk I₁ (x : R))
      rfl
  }
  have hcomm : φP.comp (f.rTensor M) =
      qM.comp ((TensorProduct.lid R M).comp (J.subtype.rTensor M)) := by
    rw [hφP0]
    apply TensorProduct.ext'
    intro j m
    simp [φP0, f, qM]; rfl
  let A₂ := R ⧸ I₂
  let N₂ := M ⧸ (I₂ • (⊤ : Submodule R M))
  let P₂ : Ideal A₂ := (J ⊓ I₁).map I₂.mkQ
  have hA₂ : Function.Surjective (algebraMap R A₂) := by
    simpa [A₂] using Ideal.Quotient.mk_surjective
  let e02 : (A₂ ⊗[R] M) ≃ₗ[A₂] N₂ :=
    (TensorProduct.quotTensorEquivQuotSMul M I₂).extendScalarsOfSurjective
      hA₂
  let ebase₂ : (P₂ ⊗[A₂] (A₂ ⊗[R] M)) ≃ₗ[A₂] (P₂ ⊗[R] M) :=
    TensorProduct.AlgebraTensorModule.cancelBaseChange R A₂ A₂ P₂ M
  let e2 : (P₂ ⊗[R] M) ≃ₗ[A₂] (P₂ ⊗[A₂] N₂) :=
    ebase₂.symm ≪≫ₗ
      TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl A₂ P₂) e02
  have hP₂ : Function.Injective (P₂.subtype.rTensor N₂) :=
    (Module.Flat.iff_rTensor_injective'.mp h₂) P₂
  let qM₂ : M →ₗ[R] N₂ := (I₂ • (⊤ : Submodule R M)).mkQ
  have he02 (m : M) : e02 (1 ⊗ₜ[R] m) = qM₂ m := by
    change (TensorProduct.quotTensorEquivQuotSMul M I₂) (1 ⊗ₜ[R] m) = qM₂ m
    rw [TensorProduct.quotTensorEquivQuotSMul_mk_one_tmul]
    rfl
  let φP₂ : (P₂ ⊗[R] M) →ₗ[R] N₂ :=
    (TensorProduct.lid A₂ N₂).restrictScalars R ∘ₗ
      (P₂.subtype.rTensor N₂).restrictScalars R ∘ₗ e2.restrictScalars R
  let φP₂0 : (P₂ ⊗[R] M) →ₗ[R] N₂ := TensorProduct.lift {
    toFun := fun p => {
      toFun := fun m => (p : A₂) • qM₂ m
      map_add' := by intro m n; simp
      map_smul' := by
        intro r m
        rw [qM₂.map_smul, smul_comm]
        simp
    }
    map_add' := by
      intro p p'
      ext m
      dsimp
      rw [add_smul]
    map_smul' := by
      intro r p
      ext m
      dsimp
      rw [smul_assoc]
  }
  have hφP₂0 : φP₂ = φP₂0 := by
    apply TensorProduct.ext'
    intro p m
    simp [φP₂, φP₂0, qM₂, e2, ebase₂]
    rw [he02]
  have hφP₂ : Function.Injective φP₂ := by
    exact (TensorProduct.lid A₂ N₂).injective.comp
      (hP₂.comp e2.injective)
  have hf : Function.Surjective f := by
    intro x
    obtain ⟨y, hy, hxy⟩ := Ideal.mem_map_iff_of_surjective
      (Ideal.Quotient.mk I₁) Ideal.Quotient.mk_surjective |>.mp x.property
    exact ⟨⟨y, hy⟩, Subtype.ext hxy⟩
  let K : Ideal R := J ⊓ I₁
  let k : K →ₗ[R] J := {
    toFun := fun x => ⟨x, x.property.1⟩
    map_add' := by intro x y; rfl
    map_smul' := by intro r x; rfl
  }
  let g : K →ₗ[R] P₂ := {
    toFun := fun x => ⟨I₂.mkQ x, Ideal.mem_map_of_mem I₂.mkQ x.property⟩
    map_add' := by intro x y; ext; simp
    map_smul' := by
      intro r x
      apply Subtype.ext
      change (Ideal.Quotient.mk I₂ r) * (Ideal.Quotient.mk I₂ (x : R)) =
        algebraMap R A₂ r * (Ideal.Quotient.mk I₂ (x : R))
      rfl
  }
  have hg : Function.Injective g := by
    intro x y hxy
    apply Subtype.ext
    have hz : I₂.mkQ (x : R) - I₂.mkQ (y : R) = 0 := by
      exact sub_eq_zero.mpr (congrArg Subtype.val hxy)
    have hz' : (x : R) - (y : R) ∈ I₂ := by
      apply Ideal.Quotient.eq_zero_iff_mem.mp
      simpa using hz
    have hbot : (x : R) - (y : R) ∈ I₁ ⊓ I₂ :=
      ⟨sub_mem (show (x : R) ∈ I₁ from x.property.2)
          (show (y : R) ∈ I₁ from y.property.2), hz'⟩
    rw [hI] at hbot
    exact sub_eq_zero.mp hbot
  have hg_surj : Function.Surjective g := by
    intro x
    obtain ⟨y, hy, hxy⟩ := Ideal.mem_map_iff_of_surjective
      (Ideal.Quotient.mk I₂) Ideal.Quotient.mk_surjective |>.mp x.property
    exact ⟨⟨y, hy⟩, Subtype.ext hxy⟩
  let eg : K ≃ₗ[R] P₂ := LinearEquiv.ofBijective g ⟨hg, hg_surj⟩
  have hgT : Function.Injective (g.rTensor M) := by
    have heg : eg.toLinearMap = g := by
      ext x
      rfl
    rw [← heg]
    exact (eg.rTensor M).injective
  have hfk : Function.Exact k f := by
    rw [LinearMap.exact_iff]
    apply le_antisymm
    · intro x hx
      have hxI : (x : R) ∈ I₁ := by
        apply Ideal.Quotient.eq_zero_iff_mem.mp
        simpa [f] using LinearMap.mem_ker.mp hx
      refine ⟨⟨(x : R), ⟨x.property, hxI⟩⟩, ?_⟩
      rfl
    · rintro x ⟨y, rfl⟩
      change f (k y) = 0
      apply Subtype.ext
      exact Ideal.Quotient.eq_zero_iff_mem.mpr y.property.2
  have hcomm₂ : φP₂.comp (g.rTensor M) =
      qM₂.comp ((TensorProduct.lid R M).comp (K.subtype.rTensor M)) := by
    rw [hφP₂0]
    apply TensorProduct.ext'
    intro x m
    simp [φP₂0, g, qM₂]; rfl
  let φJ : (J ⊗[R] M) →ₗ[R] M :=
    (TensorProduct.lid R M).comp (J.subtype.rTensor M)
  have hφJ : Function.Injective φJ := by
    apply LinearMap.ker_eq_bot.mp
    rw [eq_bot_iff]
    intro x hx
    have hzero : φP (f.rTensor M x) = 0 := by
      change (φP.comp (f.rTensor M)) x = 0
      rw [hcomm, LinearMap.comp_apply, hx]
      simp
    have hfx : (f.rTensor M) x = 0 := hφP hzero
    have hex : Function.Exact (k.rTensor M) (f.rTensor M) :=
      rTensor_exact M hfk hf
    have hxrange : x ∈ LinearMap.range (k.rTensor M) := by
      rw [← hex.linearMap_ker_eq]
      exact hfx
    obtain ⟨y, hy⟩ := hxrange
    have hyzero : (TensorProduct.lid R M)
        ((J.subtype.rTensor M) ((k.rTensor M) y)) = 0 := by
      rw [hy]
      exact hx
    have hKzero : (TensorProduct.lid R M) ((K.subtype.rTensor M) y) = 0 := by
      have hcomp : (Submodule.subtype J).comp k = Submodule.subtype K := by
        ext z
        rfl
      rw [← hcomp, LinearMap.rTensor_comp_apply]
      exact hyzero
    have hgy : (g.rTensor M) y = 0 := by
      apply hφP₂
      change (φP₂.comp (g.rTensor M)) y = 0
      rw [hcomm₂]
      simp only [LinearMap.comp_apply]
      simpa using congrArg (fun z : M => qM₂ z) hKzero
    have hy0 : y = 0 := hgT hgy
    rw [← hy, hy0]
    simp
  
  intro x y hxy
  apply hφJ
  simpa [φJ] using congrArg (TensorProduct.lid R M) hxy

theorem flat_quotient_inf_of_flat_quotients
    {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (I₁ I₂ : Ideal R)
    (h₁ : Module.Flat (R ⧸ I₁)
      (M ⧸ (I₁ • (⊤ : Submodule R M))))
    (h₂ : Module.Flat (R ⧸ I₂)
      (M ⧸ (I₂ • (⊤ : Submodule R M)))) :
      Module.Flat (R ⧸ (I₁ ⊓ I₂))
      (M ⧸ ((I₁ ⊓ I₂) • (⊤ : Submodule R M))) := by
  let K : Ideal R := I₁ ⊓ I₂
  let A := R ⧸ K
  let N := M ⧸ (K • (⊤ : Submodule R M))
  let I₁' : Ideal A := I₁.map (Ideal.Quotient.mk K)
  let I₂' : Ideal A := I₂.map (Ideal.Quotient.mk K)
  have hK₁ : K ≤ I₁ := by exact inf_le_left
  have hK₂ : K ≤ I₂ := by exact inf_le_right
  have hI' : I₁' ⊓ I₂' = ⊥ := by
    apply le_antisymm
    · intro x hx
      obtain ⟨r₁, hr₁, e₁⟩ := Ideal.mem_map_iff_of_surjective
        (Ideal.Quotient.mk K) Ideal.Quotient.mk_surjective |>.mp hx.1
      obtain ⟨r₂, hr₂, e₂⟩ := Ideal.mem_map_iff_of_surjective
        (Ideal.Quotient.mk K) Ideal.Quotient.mk_surjective |>.mp hx.2
      have hrel : r₁ - r₂ ∈ K := by
        apply Ideal.Quotient.eq_zero_iff_mem.mp
        rw [map_sub, e₁, e₂]
        simp
      have hr₁₂ : r₁ ∈ I₂ := by
        rw [show r₁ = r₂ + (r₁ - r₂) by ring]
        exact I₂.add_mem hr₂ (hK₂ hrel)
      have hr₁K : r₁ ∈ K := ⟨hr₁, hr₁₂⟩
      change x = 0
      rw [← e₁]
      exact Ideal.Quotient.eq_zero_iff_mem.mpr hr₁K
    · exact bot_le
  have hSub₁ : K • (⊤ : Submodule R M) ≤ I₁ • (⊤ : Submodule R M) :=
    Submodule.smul_mono hK₁ le_rfl
  let B₁ := A ⧸ I₁'
  let C₁ := R ⧸ I₁
  let S₁ := N ⧸ (I₁' • (⊤ : Submodule A N))
  let T₁ := M ⧸ (I₁ • (⊤ : Submodule R M))
  let eRing₁ : B₁ ≃+* C₁ := DoubleQuot.quotQuotEquivQuotOfLE hK₁
  have hden₁ :
      (I₁' • (⊤ : Submodule A N)).restrictScalars R =
        Submodule.map ((K • (⊤ : Submodule R M)).mkQ)
          (I₁ • (⊤ : Submodule R M)) := by
    change (I₁.map (algebraMap R A) • (⊤ : Submodule A N)).restrictScalars R = _
    rw [Ideal.smul_restrictScalars, Submodule.map_smul'']
    rw [Submodule.map_top,
      LinearMap.range_eq_top.mpr (K • (⊤ : Submodule R M)).mkQ_surjective]
    rfl
  let eMod₁R : S₁ ≃ₗ[R] T₁ := by
    let eRestr := quotient_restrictScalars_equiv
      (R := R) (A := A) (M := N) (I₁' • (⊤ : Submodule A N))
    let eQuot := Submodule.quotEquivOfEq _ _ hden₁
    let eBase := Submodule.quotientQuotientEquivQuotient
      (K • (⊤ : Submodule R M)) (I₁ • (⊤ : Submodule R M)) hSub₁
    exact eRestr.trans (eQuot.trans eBase)
  have h₁' : Module.Flat B₁ S₁ :=
    flat_of_ringEquiv_of_addEquiv eRing₁ eMod₁R.toAddEquiv (by
      intro c x
      obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective c
      induction x using Submodule.Quotient.induction_on with
      | _ x =>
        induction x using Submodule.Quotient.induction_on with
        | _ x =>
          rfl
    ) h₁
  have hSub₂ : K • (⊤ : Submodule R M) ≤ I₂ • (⊤ : Submodule R M) :=
    Submodule.smul_mono hK₂ le_rfl
  let B₂ := A ⧸ I₂'
  let C₂ := R ⧸ I₂
  let S₂ := N ⧸ (I₂' • (⊤ : Submodule A N))
  let T₂ := M ⧸ (I₂ • (⊤ : Submodule R M))
  let eRing₂ : B₂ ≃+* C₂ := DoubleQuot.quotQuotEquivQuotOfLE hK₂
  have hden₂ :
      (I₂' • (⊤ : Submodule A N)).restrictScalars R =
        Submodule.map ((K • (⊤ : Submodule R M)).mkQ)
          (I₂ • (⊤ : Submodule R M)) := by
    change (I₂.map (algebraMap R A) • (⊤ : Submodule A N)).restrictScalars R = _
    rw [Ideal.smul_restrictScalars, Submodule.map_smul'']
    rw [Submodule.map_top,
      LinearMap.range_eq_top.mpr (K • (⊤ : Submodule R M)).mkQ_surjective]
    rfl
  let eMod₂R : S₂ ≃ₗ[R] T₂ := by
    let eRestr := quotient_restrictScalars_equiv
      (R := R) (A := A) (M := N) (I₂' • (⊤ : Submodule A N))
    let eQuot := Submodule.quotEquivOfEq _ _ hden₂
    let eBase := Submodule.quotientQuotientEquivQuotient
      (K • (⊤ : Submodule R M)) (I₂ • (⊤ : Submodule R M)) hSub₂
    exact eRestr.trans (eQuot.trans eBase)
  have h₂' : Module.Flat B₂ S₂ :=
    flat_of_ringEquiv_of_addEquiv eRing₂ eMod₂R.toAddEquiv (by
      intro c x
      obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective c
      induction x using Submodule.Quotient.induction_on with
      | _ x =>
        induction x using Submodule.Quotient.induction_on with
        | _ x =>
          rfl
    ) h₂
  exact flat_of_flat_quotients_of_inf_eq_bot I₁' I₂' hI' h₁' h₂'

/- The proof's displayed tensor identity identifies the quotient of `J` by
`J ∩ I₁` with `(J + I₁) / I₁`, after tensoring with the corresponding module
quotient.  Its exact-sequence diagram is the standard right-exact tensor
sequence used by the flatness criterion; these proof details are subsumed by
the source-faithful theorem above and the canonical tensor/flatness APIs. -/

end

end Formalization.Books.MoreAlgebra.Unit16
