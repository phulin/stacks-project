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
          simpa [Q.ker_mkQ] using x.property
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
        simpa [Q.ker_mkQ] using y.property
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
          simpa [Q.ker_mkQ] using x.property
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
        simpa [Q.ker_mkQ] using y.property
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
  sorry

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
  sorry

/-! ## Coherent rings -/

/-- A valuation ring is coherent. -/
theorem valuationRing_isCoherent
    {R : Type u} [CommRing R] [IsDomain R] [ValuationRing R] :
    IsCoherentRing R := by
  sorry

/-- Over a coherent ring, coherence of a module is equivalent to finite
presentation. -/
theorem coherentModule_iff_finitePresentation
    {R : Type u} [CommRing R] (hR : IsCoherentRing R)
    (M : ModuleCat.{v} R) :
    IsCoherentModule R M ↔ Module.FinitePresentation R (M : Type v) := by
  sorry

/-- A Noetherian ring is coherent. -/
theorem isCoherentRing_of_isNoetherianRing
    (R : Type u) [CommRing R] [IsNoetherianRing R] :
    IsCoherentRing R := by
  sorry

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
  sorry

end

end Formalization.Books.Algebra.Unit90
