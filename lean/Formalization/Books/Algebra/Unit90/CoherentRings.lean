import Formalization.Books.Algebra.Unit89.InterchangingDirectProductsWithTensor
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Category.ModuleCat.Biproducts
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.CategoryTheory.Abelian.Subcategory
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.RingTheory.Valuation.ValuationRing
import Mathlib.RingTheory.Finiteness.Prod

/-!
# Commutative Algebra, Chapter 90: Coherent rings

Coherent modules are defined using Mathlib's canonical notions of finite
generation and finite presentation.  Short exact sequences are represented by
`ShortComplex.ShortExact` in the category of modules, and the category of
coherent modules is the corresponding full subcategory.
-/

namespace Formalization.Books.Algebra.Unit90

open CategoryTheory
open CategoryTheory.Limits
open Formalization.Books.Algebra.Unit89

universe u v w

noncomputable section

/-! ## Coherent modules and coherent rings -/

/-- A module is coherent when it is finitely generated and each finitely
generated submodule is finitely presented. -/
def IsCoherentModule (R : Type u) [CommRing R] (M : ModuleCat.{v} R) : Prop :=
  Module.Finite R (M : Type v) ∧
    ∀ N : Submodule R (M : Type v),
      Module.Finite R (N : Type v) →
        Module.FinitePresentation R (N : Type v)

/-- A ring is coherent when it is coherent as a module over itself. -/
def IsCoherentRing (R : Type u) [CommRing R] : Prop :=
  IsCoherentModule R (ModuleCat.of R R)

/-- The module formulation of coherence specializes to finitely generated
ideals in the regular module. -/
theorem coherentRing_iff_finitelyPresented_ideals
    (R : Type u) [CommRing R] :
    IsCoherentRing R ↔
      ∀ I : Ideal R, I.FG → Module.FinitePresentation R (I : Type u) := by
  change (Module.Finite R R ∧
      ∀ N : Submodule R R, Module.Finite R (N : Type u) →
        Module.FinitePresentation R (N : Type u)) ↔ _
  constructor
  · rintro ⟨_, h⟩ I hI
    exact h I (Module.Finite.of_fg hI)
  · intro h
    refine ⟨inferInstance, ?_⟩
    intro N hN
    exact h N (Module.Finite.iff_fg.mp hN)

/-! ## The coherent-module category -/

/-- The object property defining the full category of coherent modules. -/
def coherentModuleProperty (R : Type u) [CommRing R] :
    ObjectProperty (ModuleCat.{v} R) :=
  fun M => IsCoherentModule R M

/-- The category of coherent `R`-modules. -/
abbrev CoherentModuleCat (R : Type u) [CommRing R] :=
  (coherentModuleProperty.{u, v} R).FullSubcategory

private theorem coherent_submodule_of_finite_aux
    {R : Type u} [CommRing R] {M : ModuleCat.{v} R}
    (hM : IsCoherentModule R M) (N : Submodule R (M : Type v))
    (hN : Module.Finite R (N : Type v)) :
    IsCoherentModule R (ModuleCat.of R (N : Type v)) := by
  refine ⟨hN, ?_⟩
  intro P hP
  have hPmap : Module.Finite R (P.map N.subtype : Submodule R (M : Type v)) :=
    Module.Finite.of_fg (Submodule.FG.map N.subtype (Module.Finite.iff_fg.mp hP))
  have hPmap_fp := hM.2 (P.map N.subtype) hPmap
  exact ((Submodule.equivSubtypeMap N P).symm.finitePresentation_iff).mp hPmap_fp

private theorem coherent_of_linearEquiv
    {R : Type u} [CommRing R] {M N : Type v}
    [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N]
    (e : M ≃ₗ[R] N) (hM : IsCoherentModule R (ModuleCat.of R M)) :
    IsCoherentModule R (ModuleCat.of R N) := by
  let : Module.Finite R M := hM.1
  refine ⟨Module.Finite.equiv e, ?_⟩
  intro P hP
  let : Module.Finite R P := hP
  let eP : (P.comap e.toLinearMap) ≃ₗ[R] P :=
    Submodule.comap_equiv_self_of_inj_of_le e.injective (by
      intro x hx
      exact ⟨e.symm x, by simp⟩)
  have hP' : Module.Finite R (P.comap e.toLinearMap) :=
    Module.Finite.equiv eP.symm
  have hPfp := hM.2 (P.comap e.toLinearMap) hP'
  let : Module.FinitePresentation R (P.comap e.toLinearMap) := hPfp
  exact Module.FinitePresentation.of_equiv eP

private theorem finite_kernel_of_finite_to_coherent_aux
    {R : Type u} [CommRing R] {N : Type w} {M : Type v}
    [AddCommGroup N] [AddCommGroup M] [Module R N] [Module R M]
    (φ : N →ₗ[R] M) (hN : Module.Finite R N)
    (hM : IsCoherentModule R (ModuleCat.of R M)) :
    Module.Finite R (LinearMap.ker φ) := by
  let : Module.Finite R N := hN
  let : Module.Finite R M := hM.1
  let Q : Submodule R M := LinearMap.range φ
  have hQfp : Module.FinitePresentation R (Q : Type v) := hM.2 Q inferInstance
  let : Module.FinitePresentation R (Q : Type v) := hQfp
  have hkerfg : (LinearMap.ker φ.rangeRestrict).FG :=
    Module.FinitePresentation.fg_ker φ.rangeRestrict
      (LinearMap.surjective_rangeRestrict φ)
  rw [← LinearMap.ker_rangeRestrict]
  exact Module.Finite.of_fg hkerfg

private theorem coherent_kernel_image_cokernel_of_finite_aux
    {R : Type u} [CommRing R] {N M : ModuleCat.{v} R}
    (φ : N ⟶ M) (hN : Module.Finite R (N : Type v))
    (hM : IsCoherentModule R M) :
    Module.Finite R (LinearMap.ker φ.hom) ∧
      IsCoherentModule R (ModuleCat.of R (LinearMap.range φ.hom)) ∧
        IsCoherentModule R
          (ModuleCat.of R ((M : Type v) ⧸ LinearMap.range φ.hom)) := by
  let : Module.Finite R (N : Type v) := hN
  let : Module.Finite R (M : Type v) := hM.1
  let Q : Submodule R (M : Type v) := LinearMap.range φ.hom
  have hQ : Module.Finite R (Q : Type v) := inferInstance
  have hQcoh : IsCoherentModule R (ModuleCat.of R (Q : Type v)) :=
    coherent_submodule_of_finite_aux hM Q hQ
  have hQfp : Module.FinitePresentation R (Q : Type v) := hM.2 Q hQ
  let : Module.FinitePresentation R (Q : Type v) := hQfp
  have hφsurj : Function.Surjective φ.hom.rangeRestrict :=
    LinearMap.surjective_rangeRestrict φ.hom
  have hkerfg : (LinearMap.ker φ.hom.rangeRestrict).FG :=
    Module.FinitePresentation.fg_ker φ.hom.rangeRestrict hφsurj
  have hker : Module.Finite R (LinearMap.ker φ.hom) := by
    rw [← LinearMap.ker_rangeRestrict]
    exact Module.Finite.of_fg hkerfg
  refine ⟨hker, hQcoh, ?_⟩
  change IsCoherentModule R (ModuleCat.of R ((M : Type v) ⧸ Q))
  refine ⟨inferInstance, ?_⟩
  intro E hE
  have hE' : Module.Finite R (E.comap Q.mkQ : Submodule R (M : Type v)) := by
    let E' : Submodule R (M : Type v) := E.comap Q.mkQ
    let fE : (Q : Type v) →ₗ[R] (E' : Type v) :=
      Q.subtype.codRestrict E' (by
        intro x
        change Q.mkQ (x : (M : Type v)) ∈ E
        have hx0 : Q.mkQ (x : (M : Type v)) = 0 := by
          apply (LinearMap.mem_ker).1
          simp [Q.ker_mkQ]
        rw [hx0]
        exact E.zero_mem)
    let gE : (E' : Type v) →ₗ[R] (E : Type v) :=
      LinearMap.codRestrict E (Q.mkQ.domRestrict E') (by intro x; exact x.property)
    apply Module.Finite.of_exact (f := fE) (g := gE)
    · rw [LinearMap.exact_iff]
      ext x
      constructor
      · intro hx
        change gE x = 0 at hx
        have hx0 : Q.mkQ (x : (M : Type v)) = 0 := congrArg Subtype.val hx
        have hxQ : (x : (M : Type v)) ∈ Q := by
          have hxker : (x : (M : Type v)) ∈ LinearMap.ker Q.mkQ :=
            (LinearMap.mem_ker).2 hx0
          simpa [Q.ker_mkQ] using hxker
        exact ⟨⟨(x : (M : Type v)), hxQ⟩, by ext; rfl⟩
      · rintro ⟨y, rfl⟩
        apply Subtype.ext
        change Q.mkQ (y : (M : Type v)) = 0
        apply (LinearMap.mem_ker).1
        simp [Q.ker_mkQ]
    · intro y
      obtain ⟨x, hx⟩ := Q.mkQ_surjective (y : (M : Type v) ⧸ Q)
      refine ⟨⟨x, ?_⟩, ?_⟩
      · change Q.mkQ x ∈ E
        rw [hx]
        exact y.property
      · exact Subtype.ext hx
  let : Module.Finite R (E.comap Q.mkQ : Submodule R (M : Type v)) := hE'
  have hEfp : Module.FinitePresentation R
      (E.comap Q.mkQ : Submodule R (M : Type v)) :=
    hM.2 (E.comap Q.mkQ) hE'
  let : Module.FinitePresentation R
      (E.comap Q.mkQ : Submodule R (M : Type v)) := hEfp
  let gE : (E.comap Q.mkQ : Type v) →ₗ[R] (E : Type v) :=
    LinearMap.codRestrict E (Q.mkQ.domRestrict (E.comap Q.mkQ))
      (by intro x; exact x.property)
  have hgEsurj : Function.Surjective gE := by
    intro y
    obtain ⟨x, hx⟩ := Q.mkQ_surjective (y : (M : Type v) ⧸ Q)
    refine ⟨⟨x, ?_⟩, ?_⟩
    · change Q.mkQ x ∈ E
      rw [hx]
      exact y.property
    · exact Subtype.ext hx
  have hkerE : Module.Finite R (LinearMap.ker gE) := by
    let fE : (Q : Type v) →ₗ[R] (E.comap Q.mkQ : Type v) :=
      Q.subtype.codRestrict (E.comap Q.mkQ) (by
        intro x
        change Q.mkQ (x : (M : Type v)) ∈ E
        have hx0 : Q.mkQ (x : (M : Type v)) = 0 := by
          apply (LinearMap.mem_ker).1
          simp [Q.ker_mkQ]
        rw [hx0]
        exact E.zero_mem)
    have hExactE : Function.Exact fE gE := by
      rw [LinearMap.exact_iff]
      ext z
      constructor
      · intro hz
        change gE z = 0 at hz
        have hz0 : Q.mkQ (z : (M : Type v)) = 0 := congrArg Subtype.val hz
        have hzQ : (z : (M : Type v)) ∈ Q := by
          have hzker : (z : (M : Type v)) ∈ LinearMap.ker Q.mkQ :=
            (LinearMap.mem_ker).2 hz0
          simpa [Q.ker_mkQ] using hzker
        exact ⟨⟨(z : (M : Type v)), hzQ⟩, by ext; rfl⟩
      · rintro ⟨y, rfl⟩
        apply Subtype.ext
        change Q.mkQ (y : (M : Type v)) = 0
        apply (LinearMap.mem_ker).1
        simp [Q.ker_mkQ]
    have hrangeE : LinearMap.range fE = LinearMap.ker gE :=
      (LinearMap.exact_iff.mp hExactE).symm
    have hfE : Function.Surjective
        (fE.codRestrict (LinearMap.ker gE) (by
          intro x
          rw [← hrangeE]
          exact LinearMap.mem_range_self fE x)) := by
      intro y
      have hy : (y : (E.comap Q.mkQ : Type v)) ∈ LinearMap.range fE := by
        rw [hrangeE]
        exact y.property
      obtain ⟨x, hx⟩ := hy
      refine ⟨x, ?_⟩
      apply Subtype.ext
      exact hx
    exact Module.Finite.of_surjective _ hfE
  have hEfp' : Module.FinitePresentation R (E : Type v) :=
    Module.finitePresentation_of_surjective gE hgEsurj (Module.Finite.iff_fg.mp hkerE)
  exact hEfp'

private theorem coherent_product_aux
    {R : Type u} [CommRing R] {M N : ModuleCat.{v} R}
    (hM : IsCoherentModule R M) (hN : IsCoherentModule R N) :
    IsCoherentModule R (ModuleCat.of R (M × N)) := by
  let : Module.Finite R (M : Type v) := hM.1
  let : Module.Finite R (N : Type v) := hN.1
  refine ⟨inferInstance, ?_⟩
  intro P hP
  let : Module.Finite R (P : Type v) := hP
  let fP : (P : Type v) →ₗ[R] (M : Type v) :=
    (LinearMap.fst R M N).domRestrict P
  have hkernel : Module.Finite R (LinearMap.ker fP) :=
    (coherent_kernel_image_cokernel_of_finite_aux
      (ModuleCat.ofHom fP) hP hM).1
  have himage : Module.Finite R (LinearMap.range fP) := inferInstance
  have himage_fp : Module.FinitePresentation R (LinearMap.range fP) :=
    hM.2 (LinearMap.range fP) himage
  let s : (LinearMap.ker fP) →ₗ[R] (N : Type v) :=
    (LinearMap.snd R M N).comp
      (P.subtype.comp (LinearMap.ker fP).subtype)
  have hs : Function.Injective s := by
    intro x y hxy
    apply Subtype.ext
    apply Subtype.ext
    apply Prod.ext
    · change fP x = fP y
      rw [x.property, y.property]
    · change s x = s y
      exact hxy
  have hsimage : Module.Finite R (LinearMap.range s) := inferInstance
  have hsimage_fp : Module.FinitePresentation R (LinearMap.range s) :=
    hN.2 (LinearMap.range s) hsimage
  let : Module.FinitePresentation R (LinearMap.range s) := hsimage_fp
  have hkernel_fp : Module.FinitePresentation R (LinearMap.ker fP) :=
    Module.FinitePresentation.of_equiv (LinearEquiv.ofInjective s hs).symm
  let : Module.FinitePresentation R (LinearMap.range fP) := himage_fp
  let : Module.FinitePresentation R (LinearMap.ker fP.rangeRestrict) := by
    rw [LinearMap.ker_rangeRestrict]
    exact hkernel_fp
  exact Module.finitePresentation_of_ker fP.rangeRestrict
    (LinearMap.surjective_rangeRestrict fP)

private theorem coherent_fin_fun_aux
    {R : Type u} [CommRing R] (n : ℕ)
    (hR : IsCoherentModule R (ModuleCat.of R R)) :
    IsCoherentModule R (ModuleCat.of R (Fin n → R)) := by
  apply Module.pi_induction' R
    (motive := fun (N : Type u) [AddCommGroup N] [Module R N] =>
      IsCoherentModule R (ModuleCat.of R N))
    (motive' := fun (N : Type u) [AddCommGroup N] [Module R N] =>
      IsCoherentModule R (ModuleCat.of R N))
    (equiv := by
      intro N N' _ _ _ _ e hN
      exact coherent_of_linearEquiv e hN)
    (equiv' := by
      intro N N' _ _ _ _ e hN
      exact coherent_of_linearEquiv e hN)
    (unit := by
      refine ⟨inferInstance, ?_⟩
      intro P _
      exact inferInstance)
    (prod := by
      intro N N' _ _ _ _ hN hN'
      exact coherent_product_aux (R := R) hN hN')
    (fun _ : Fin n => R) (by intro i; exact hR)

/-- The category of coherent modules is abelian. -/
instance coherentModuleCat_abelian
    (R : Type u) [CommRing R] : Abelian (CoherentModuleCat.{u, v} R) := by
  let P := coherentModuleProperty.{u, v} R
  letI : P.IsClosedUnderIsomorphisms := {
    of_iso := by
      intro X Y e hX
      let e' := e.toLinearEquiv
      let : Module.Finite R (X : Type v) := hX.1
      refine ⟨Module.Finite.equiv e', ?_⟩
      intro N hN
      let : Module.Finite R (N : Type v) := hN
      let eN : (N.comap e'.toLinearMap) ≃ₗ[R] N :=
        Submodule.comap_equiv_self_of_inj_of_le e'.injective (by
          intro x hx
          exact ⟨e'.symm x, by simp⟩)
      have hN' : Module.Finite R (N.comap e'.toLinearMap) :=
        Module.Finite.equiv eN.symm
      have hNfp := hX.2 (N.comap e'.toLinearMap) hN'
      let : Module.FinitePresentation R (N.comap e'.toLinearMap) := hNfp
      exact Module.FinitePresentation.of_equiv eN
  }
  letI : P.ContainsZero := {
    exists_zero := by
      refine ⟨ModuleCat.of R (ULift.{v} PUnit), ModuleCat.isZero_of_subsingleton _, ?_⟩
      refine ⟨inferInstance, ?_⟩
      intro N _
      exact inferInstance
  }
  letI : P.IsClosedUnderBinaryProducts := by
    apply ObjectProperty.IsClosedUnderLimitsOfShape.mk'
    rintro X ⟨F, hF⟩
    let X₁ := F.obj ⟨WalkingPair.left⟩
    let X₂ := F.obj ⟨WalkingPair.right⟩
    have hprod := coherent_product_aux (R := R) (M := X₁) (N := X₂)
      (hF ⟨WalkingPair.left⟩) (hF ⟨WalkingPair.right⟩)
    have eprod : ModuleCat.of R (X₁ × X₂) ≅ limit F :=
      IsLimit.conePointUniqueUpToIso
        (F := pair X₁ X₂)
        (s := (ModuleCat.binaryProductLimitCone X₁ X₂).cone)
        (t := ((Cone.postcompose (diagramIsoPair F).hom).obj (limit.cone F)))
        (ModuleCat.binaryProductLimitCone X₁ X₂).isLimit
        ((IsLimit.postcomposeHomEquiv (diagramIsoPair F) (limit.cone F)).2
          (limit.isLimit F))
    exact P.prop_of_iso eprod hprod
  letI : P.IsClosedUnderFiniteProducts := ObjectProperty.IsClosedUnderFiniteProducts.mk'
  letI : P.IsClosedUnderKernels := {
    kernels_le := by
      rintro X ⟨f, k, hk, hf⟩
      have h := coherent_kernel_image_cokernel_of_finite_aux f hf.1.1 hf.2
      have hker : P (ModuleCat.of R (LinearMap.ker f.hom)) :=
        coherent_submodule_of_finite_aux hf.1 (LinearMap.ker f.hom) h.1
      exact P.prop_of_iso
        (IsLimit.conePointUniqueUpToIso (ModuleCat.kernelIsLimit f) hk) hker
  }
  letI : P.IsClosedUnderCokernels := {
    cokernels_le := by
      rintro X ⟨f, k, hk, hf⟩
      have h := coherent_kernel_image_cokernel_of_finite_aux f hf.1.1 hf.2
      exact P.prop_of_iso
        (IsColimit.coconePointUniqueUpToIso (ModuleCat.cokernelIsColimit f) hk) h.2.2
  }
  exact inferInstance

/-! ## Permanence of coherence -/

/-- A finitely generated submodule of a coherent module is coherent. -/
theorem coherent_submodule_of_finite
    {R : Type u} [CommRing R] {M : ModuleCat.{v} R}
    (hM : IsCoherentModule R M) (N : Submodule R (M : Type v))
    (hN : Module.Finite R (N : Type v)) :
    IsCoherentModule R (ModuleCat.of R (N : Type v)) := by
  exact coherent_submodule_of_finite_aux hM N hN

/-- The kernel, image, and cokernel of a map from a finitely generated module
to a coherent module have the finiteness properties in the source. -/
theorem coherent_kernel_image_cokernel_of_finite
    {R : Type u} [CommRing R] {N M : ModuleCat.{v} R}
    (φ : N ⟶ M) (hN : Module.Finite R (N : Type v))
    (hM : IsCoherentModule R M) :
    Module.Finite R (LinearMap.ker φ.hom) ∧
      IsCoherentModule R (ModuleCat.of R (LinearMap.range φ.hom)) ∧
        IsCoherentModule R
          (ModuleCat.of R ((M : Type v) ⧸ LinearMap.range φ.hom)) := by
  exact coherent_kernel_image_cokernel_of_finite_aux φ hN hM

/-- Kernels and cokernels of maps between coherent modules are coherent. -/
theorem coherent_kernel_cokernel_of_coherent
    {R : Type u} [CommRing R] {N M : ModuleCat.{v} R}
    (φ : N ⟶ M) (hN : IsCoherentModule R N)
    (hM : IsCoherentModule R M) :
    IsCoherentModule R (ModuleCat.of R (LinearMap.ker φ.hom)) ∧
      IsCoherentModule R
        (ModuleCat.of R ((M : Type v) ⧸ LinearMap.range φ.hom)) := by
  have h := coherent_kernel_image_cokernel_of_finite φ hN.1 hM
  exact ⟨coherent_submodule_of_finite hN _ h.1, h.2.2⟩

/-- In a short exact sequence, any two coherent modules imply coherence of the
third. -/
theorem coherent_of_shortExact
    {R : Type u} [CommRing R]
    {S : ShortComplex (ModuleCat.{v} R)} (hS : S.ShortExact) :
    (IsCoherentModule R S.X₁ ∧ IsCoherentModule R S.X₂ →
        IsCoherentModule R S.X₃) ∧
      (IsCoherentModule R S.X₁ ∧ IsCoherentModule R S.X₃ →
        IsCoherentModule R S.X₂) ∧
        (IsCoherentModule R S.X₂ ∧ IsCoherentModule R S.X₃ →
          IsCoherentModule R S.X₁) := by
  have hex : Function.Exact S.f.hom S.g.hom :=
    (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact S).mp hS.exact
  have hfg : LinearMap.range S.f.hom = LinearMap.ker S.g.hom :=
    hS.exact.moduleCat_range_eq_ker
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨h₁, h₂⟩
    have hC := coherent_kernel_image_cokernel_of_finite_aux S.f h₁.1 h₂
    let qg : ((S.X₂ : Type v) ⧸ LinearMap.range S.f.hom) →ₗ[R]
        (S.X₃ : Type v) :=
      (LinearMap.range S.f.hom).liftQ S.g.hom (by rw [hfg])
    have hqker : LinearMap.ker qg = (⊥ : Submodule R
        ((S.X₂ : Type v) ⧸ LinearMap.range S.f.hom)) := by
      dsimp [qg]
      exact Submodule.ker_liftQ_eq_bot (LinearMap.range S.f.hom) S.g.hom
        (by rw [hfg]) hfg.ge
    have hqsurj : Function.Surjective qg := by
      intro y
      obtain ⟨x, hx⟩ := hS.moduleCat_surjective_g y
      refine ⟨(LinearMap.range S.f.hom).mkQ x, ?_⟩
      simpa [qg] using hx
    let eq : ((S.X₂ : Type v) ⧸ LinearMap.range S.f.hom) ≃ₗ[R]
        (S.X₃ : Type v) :=
      LinearEquiv.ofBijective qg ⟨LinearMap.ker_eq_bot.mp hqker, hqsurj⟩
    exact coherent_of_linearEquiv eq hC.2.2
  · rintro ⟨h₁, h₃⟩
    let : Module.Finite R (S.X₁ : Type v) := h₁.1
    let : Module.Finite R (S.X₃ : Type v) := h₃.1
    have hX₂ : Module.Finite R (S.X₂ : Type v) :=
      Module.Finite.of_exact hex hS.moduleCat_surjective_g
    refine ⟨hX₂, ?_⟩
    intro N₂ hN₂
    let : Module.Finite R (N₂ : Type v) := hN₂
    let N₃ : Submodule R (S.X₃ : Type v) := N₂.map S.g.hom
    let gN : (N₂ : Type v) →ₗ[R] (N₃ : Type v) :=
      (S.g.hom.domRestrict N₂).codRestrict N₃ (by
        intro x
        exact ⟨x, x.property, rfl⟩)
    have hgN : Function.Surjective gN := by
      intro y
      obtain ⟨x, hx, hxy⟩ := y.property
      refine ⟨⟨x, hx⟩, ?_⟩
      apply Subtype.ext
      exact hxy
    have hN₃ : Module.Finite R (N₃ : Type v) :=
      Module.Finite.of_surjective gN hgN
    have hN₃fp : Module.FinitePresentation R (N₃ : Type v) :=
      h₃.2 N₃ hN₃
    let : Module.FinitePresentation R (N₃ : Type v) := hN₃fp
    have hkerfg : (LinearMap.ker gN).FG :=
      Module.FinitePresentation.fg_ker gN hgN
    have hkerfin : Module.Finite R (LinearMap.ker gN) :=
      Module.Finite.of_fg hkerfg
    let : Module.Finite R (LinearMap.ker gN) := hkerfin
    let N₁ : Submodule R (S.X₁ : Type v) := N₂.comap S.f.hom
    let fN₂ : (N₁ : Type v) →ₗ[R] (N₂ : Type v) :=
      (S.f.hom.domRestrict N₁).codRestrict N₂ (by
        intro x
        exact x.property)
    let fN : (N₁ : Type v) →ₗ[R] (LinearMap.ker gN : Type v) :=
      fN₂.codRestrict (LinearMap.ker gN) (by
        intro x
        apply (LinearMap.mem_ker).1
        apply Subtype.ext
        change S.g.hom (S.f.hom (x : (S.X₁ : Type v))) = 0
        apply (LinearMap.mem_ker).1
        rw [← hfg]
        exact LinearMap.mem_range_self S.f.hom (x : (S.X₁ : Type v)))
    have hfNinj : Function.Injective fN := by
      intro x y hxy
      apply Subtype.ext
      apply hS.moduleCat_injective_f
      change S.f.hom (x : (S.X₁ : Type v)) = S.f.hom (y : (S.X₁ : Type v))
      have hxy' : fN₂ x = fN₂ y := by
        have hz : (fN x : (N₂ : Type v)) = (fN y : (N₂ : Type v)) :=
          congrArg (fun z : (LinearMap.ker gN : Type v) =>
            (z : (N₂ : Type v))) hxy
        apply Subtype.ext
        calc
          (fN₂ x : (S.X₂ : Type v)) =
              ((fN x : (N₂ : Type v)) : (S.X₂ : Type v)) := by rfl
          _ = ((fN y : (N₂ : Type v)) : (S.X₂ : Type v)) :=
            congrArg (fun z : (N₂ : Type v) => (z : (S.X₂ : Type v))) hz
          _ = (fN₂ y : (S.X₂ : Type v)) := by rfl
      change (fN₂ x : (S.X₂ : Type v)) = (fN₂ y : (S.X₂ : Type v))
      exact congrArg Subtype.val hxy'
    have hfNsurj : Function.Surjective fN := by
      intro y
      have hyker : ((y : (N₂ : Type v)) : (S.X₂ : Type v)) ∈
          LinearMap.ker S.g.hom := by
        apply (LinearMap.mem_ker).2
        change S.g.hom ((y : (N₂ : Type v)) : (S.X₂ : Type v)) = 0
        exact congrArg (fun z : (N₃ : Type v) => (z : (S.X₃ : Type v))) y.property
      have hyrange : ((y : (N₂ : Type v)) : (S.X₂ : Type v)) ∈
          LinearMap.range S.f.hom := by
        rw [hfg]
        exact hyker
      obtain ⟨x, hx⟩ := hyrange
      refine ⟨⟨x, ?_⟩, ?_⟩
      · change S.f.hom x ∈ N₂
        rw [hx]
        exact (y : (N₂ : Type v)).property
      · apply Subtype.ext
        apply Subtype.ext
        exact hx
    let eN : (N₁ : Type v) ≃ₗ[R] (LinearMap.ker gN : Type v) :=
      LinearEquiv.ofBijective fN ⟨hfNinj, hfNsurj⟩
    have hN₁ : Module.Finite R (N₁ : Type v) :=
      Module.Finite.equiv eN.symm
    have hN₁fp : Module.FinitePresentation R (N₁ : Type v) :=
      h₁.2 N₁ hN₁
    let : Module.FinitePresentation R (N₁ : Type v) := hN₁fp
    let : Module.FinitePresentation R (LinearMap.ker gN : Type v) :=
      Module.FinitePresentation.of_equiv eN
    exact Module.finitePresentation_of_ker gN hgN
  · rintro ⟨h₂, h₃⟩
    have hker := coherent_kernel_cokernel_of_coherent S.g h₂ h₃
    let fker : (S.X₁ : Type v) →ₗ[R] (LinearMap.ker S.g.hom : Type v) :=
      S.f.hom.codRestrict (LinearMap.ker S.g.hom) (by
        intro x
        apply (LinearMap.mem_ker).1
        rw [← hfg]
        exact LinearMap.mem_range_self S.f.hom x)
    have hfkerinj : Function.Injective fker := by
      intro x y hxy
      apply hS.moduleCat_injective_f
      exact congrArg Subtype.val hxy
    have hfkersurj : Function.Surjective fker := by
      intro y
      have hyrange : (y : (S.X₂ : Type v)) ∈ LinearMap.range S.f.hom := by
        rw [hfg]
        exact y.property
      obtain ⟨x, hx⟩ := hyrange
      refine ⟨x, ?_⟩
      apply Subtype.ext
      exact hx
    let efker : (S.X₁ : Type v) ≃ₗ[R] (LinearMap.ker S.g.hom : Type v) :=
      LinearEquiv.ofBijective fker ⟨hfkerinj, hfkersurj⟩
    exact coherent_of_linearEquiv efker.symm hker.1

/-! ## Coherent rings -/

/-- A valuation ring is coherent. -/
theorem valuationRing_isCoherent
    {R : Type u} [CommRing R] [IsDomain R] [ValuationRing R] :
    IsCoherentRing R := by
  rw [coherentRing_iff_finitelyPresented_ideals]
  intro I hI
  let : IsBezout R :=
    (ValuationRing.iff_local_bezout_domain.mp
      (inferInstance : ValuationRing R)).2
  let : I.IsPrincipal := IsBezout.isPrincipal_of_FG I hI
  by_cases hI0 : I = ⊥
  · let f : R →ₗ[R] (I : Type u) := 0
    apply Module.finitePresentation_of_surjective f
    · intro x
      refine ⟨0, ?_⟩
      apply Subtype.ext
      have hx : (x : R) ∈ (⊥ : Ideal R) := by
        rw [← hI0]
        exact x.property
      have hx0 : (x : R) = 0 := Ideal.mem_bot.mp hx
      simp [hx0]
    · have hfker : LinearMap.ker f = (⊤ : Submodule R R) := by
        apply top_unique
        intro x _
        change f x = 0
        simp [f]
      rw [hfker]
      exact Module.Finite.fg_top
  · exact Module.FinitePresentation.of_equiv (Ideal.isoBaseOfIsPrincipal hI0)

/-- Over a coherent ring, coherence of a module is equivalent to finite
presentation. -/
theorem coherentModule_iff_finitePresentation
    {R : Type u} [CommRing R] (hR : IsCoherentRing R)
    (M : ModuleCat.{v} R) :
    IsCoherentModule R M ↔ Module.FinitePresentation R (M : Type v) := by
  constructor
  · intro hM
    let : Module.Finite R (M : Type v) := hM.1
    obtain ⟨n, f, hf⟩ := Module.Finite.exists_fin' R (M : Type v)
    have hker := finite_kernel_of_finite_to_coherent_aux f inferInstance hM
    exact Module.finitePresentation_of_free_of_surjective f hf
      (Module.Finite.iff_fg.mp hker)
  · intro hM
    let : Module.FinitePresentation R (M : Type v) := hM
    refine ⟨inferInstance, ?_⟩
    intro N hN
    let : Module.Finite R (N : Type v) := hN
    obtain ⟨n, m, f, g, hf, hgf⟩ :=
      Module.FinitePresentation.exists_fin' R (M : Type v)
    have hF := coherent_fin_fun_aux (R := R) n (show
      IsCoherentModule R (ModuleCat.of R R) from hR)
    have hKfg : (LinearMap.ker f).FG :=
      Module.FinitePresentation.fg_ker f hf
    have hKfin : Module.Finite R (LinearMap.ker f) :=
      Module.Finite.of_fg hKfg
    let P : Submodule R (Fin n → R) := N.comap f
    let fP : (P : Type u) →ₗ[R] (N : Type v) :=
      (f.domRestrict P).codRestrict N (by
        intro x
        exact x.property)
    let fK : (LinearMap.ker f : Type u) →ₗ[R] (P : Type u) :=
      (LinearMap.ker f).subtype.codRestrict P (by
        intro x
        change f (x : (Fin n → R)) ∈ N
        rw [x.property]
        exact N.zero_mem)
    have hExactP : Function.Exact fK fP := by
      rw [LinearMap.exact_iff]
      ext x
      constructor
      · intro hx
        change fP x = 0 at hx
        have hx0 : f (x : (Fin n → R)) = 0 := congrArg Subtype.val hx
        exact ⟨⟨(x : (Fin n → R)), (LinearMap.mem_ker).2 hx0⟩, by
          apply Subtype.ext
          rfl⟩
      · rintro ⟨y, rfl⟩
        apply Subtype.ext
        exact y.property
    have hSurjP : Function.Surjective fP := by
      intro y
      obtain ⟨x, hx⟩ := hf y
      refine ⟨⟨x, ?_⟩, ?_⟩
      · change f x ∈ N
        rw [hx]
        exact y.property
      · apply Subtype.ext
        exact hx
    have hPfin : Module.Finite R (P : Type u) :=
      Module.Finite.of_exact hExactP hSurjP
    have hPfp : Module.FinitePresentation R (P : Type u) :=
      hF.2 P hPfin
    let : Module.FinitePresentation R (P : Type u) := hPfp
    have hkerP : Module.Finite R (LinearMap.ker fP) := by
      have hrange : LinearMap.range fK = LinearMap.ker fP :=
        (LinearMap.exact_iff.mp hExactP).symm
      rw [← hrange]
      infer_instance
    exact Module.finitePresentation_of_surjective fP hSurjP
      (Module.Finite.iff_fg.mp hkerP)

/-- A Noetherian ring is coherent. -/
theorem isCoherentRing_of_isNoetherianRing
    (R : Type u) [CommRing R] [IsNoetherianRing R] :
    IsCoherentRing R := by
  rw [coherentRing_iff_finitelyPresented_ideals]
  intro I hI
  let : Module.Finite R (I : Type u) := Module.Finite.of_fg hI
  exact Module.finitePresentation_of_finite R (I : Type u)

/-! ## Products of flat modules -/

/-- Chase's characterization of coherent rings by products of flat modules. -/
theorem coherentRing_characterization
    (R : Type u) [CommRing R] :
    List.TFAE [
      IsCoherentRing R,
      ∀ (A : Type v) (Q : A → ModuleCat.{w} R),
        (∀ a, Module.Flat R (Q a : Type w)) →
          Module.Flat R (∀ a, (Q a : Type w)),
      ∀ (A : Type v), Module.Flat R (modulePower R A)
  ] := by
  tfae_have 1 → 2 := by
    intro hR A Q hQ
    rw [Module.Flat.iff_rTensor_injective]
    intro I hI
    let P : ModuleCat.{u} R := ModuleCat.of R (I : Type u)
    have hP : Module.FinitePresentation R (P : Type u) := by
      dsimp [P]
      exact (coherentRing_iff_finitelyPresented_ideals R).mp hR I hI
    have hbij : Function.Bijective (productTensorMap P Q) :=
      ((finite_presentation_tensor_iff P).out 0 1).mp hP
    have hnat
        (z : TensorProduct R (I : Type u) (∀ a, (Q a : Type w))) (a : A) :
        congrFun ((TensorProduct.rid R (∀ a, (Q a : Type w)))
          ((I.subtype.rTensor (∀ a, (Q a : Type w))) z)) a =
          (TensorProduct.rid R (Q a : Type w))
            ((I.subtype.rTensor (Q a : Type w)) ((productTensorMap P Q z) a)) := by
      induction z using TensorProduct.induction_on with
      | zero => simp
      | tmul i q => simp [productTensorMap]
      | add x y hx hy => simp [map_add, hx, hy]
    intro x y hxy
    apply hbij.1
    funext a
    letI : Module.Flat R (Q a : Type w) := hQ a
    apply Module.Flat.rTensor_preserves_injective_linearMap
      (M := Q a) I.subtype I.subtype_injective
    apply (TensorProduct.rid R (Q a : Type w)).injective
    have hxy' := congrArg (TensorProduct.rid R (∀ a, (Q a : Type w))) hxy
    rw [← hnat x a, ← hnat y a]
    exact congrFun hxy' a
  tfae_have 2 → 3 := by
    intro h A
    exact h A (fun _ => ModuleCat.of R R) (by
      intro a
      exact Module.Flat.self)
  tfae_have 3 → 1 := by
    intro hR
    rw [coherentRing_iff_finitelyPresented_ideals]
    intro I hI
    let P : ModuleCat.{u} R := ModuleCat.of R (I : Type u)
    have hfinite : Module.Finite R (P : Type u) := Module.Finite.of_fg hI
    have hbij : ∀ A : Type v,
        Function.Bijective (tensorModulePowerMap P (A := A)) := by
      intro A
      have hnat
          (z : TensorProduct R (I : Type u) (modulePower R A)) :
          (TensorProduct.rid R (modulePower R A))
              (I.subtype.rTensor (modulePower R A) z) =
            fun a => I.subtype ((tensorModulePowerMap P (A := A) z) a) := by
        induction z using TensorProduct.induction_on with
        | zero => ext a; simp
        | tmul i q => ext a; simp [tensorModulePowerMap, productTensorMap]
        | add x y hx hy => ext a; simp [map_add, hx, hy]
      have hinj : Function.Injective (tensorModulePowerMap P (A := A)) := by
        intro x y hxy
        apply (TensorProduct.rid R (modulePower R A)).injective
        rw [hnat x, hnat y]
        exact congrArg (fun f => fun a => I.subtype (f a)) hxy
      have hsurj : Function.Surjective (tensorModulePowerMap P (A := A)) :=
        ((finite_generation_tensor_iff P).out 0 3).mp hfinite A
      exact ⟨hinj, hsurj⟩
    exact ((finite_presentation_tensor_iff P).out 0 3).mpr hbij
  tfae_finish

end

end Formalization.Books.Algebra.Unit90
