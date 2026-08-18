import Formalization.Books.Algebra.Unit71.ExtGroups
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.Algebra.Module.Projective
import Mathlib.LinearAlgebra.Dual.Defs
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.RingTheory.Ideal.Maps
import Mathlib.RingTheory.Finiteness.Finsupp
import Mathlib.Tactic.TFAE

/-!
# More on Algebra, Chapter 71: Modules which are close to being projective

The source's factorization conditions are expressed using the canonical
`Module.Projective`, `Module.Free`, and `Module.Finite` predicates.  Modules
are represented by `ModuleCat`, so exact sequences and the canonical `ExtGroup`
API can be used directly.
-/

namespace Formalization.Books.MoreAlgebra.Unit71

open CategoryTheory
open Formalization.Books.Algebra.Unit71

universe u

section FactorThrough

variable {R : Type u} [CommRing R]

/-- A module map factors through a projective module. -/
def FactorsThroughProjective {M N : ModuleCat.{u} R} (φ : M ⟶ N) : Prop :=
  ∃ (P : ModuleCat.{u} R) (_ : Module.Projective R P),
    ∃ (f : M ⟶ P) (g : P ⟶ N), f ≫ g = φ

/-- A module map factors through a free module. -/
def FactorsThroughFree {M N : ModuleCat.{u} R} (φ : M ⟶ N) : Prop :=
  ∃ (P : ModuleCat.{u} R) (_ : Module.Free R P),
    ∃ (f : M ⟶ P) (g : P ⟶ N), f ≫ g = φ

/-- A module map factors through a finite projective module. -/
def FactorsThroughFiniteProjective {M N : ModuleCat.{u} R} (φ : M ⟶ N) : Prop :=
  ∃ (P : ModuleCat.{u} R) (_ : Module.Finite R P) (_ : Module.Projective R P),
    ∃ (f : M ⟶ P) (g : P ⟶ N), f ≫ g = φ

/-- The maps factoring through projectives form the span of those maps. -/
def factorsThroughProjectiveSubmodule (M N : ModuleCat.{u} R) :
    Submodule R (M ⟶ N) :=
  Submodule.span R {φ : M ⟶ N | FactorsThroughProjective φ}

/-- Every map factoring through a projective module factors through a free module. -/
theorem factorsThroughProjective_iff_factorsThroughFree
    {M N : ModuleCat.{u} R} (φ : M ⟶ N) :
    FactorsThroughProjective φ ↔ FactorsThroughFree φ := by
  constructor
  · rintro ⟨P, hP, f, g, h⟩
    obtain ⟨s, hs⟩ := hP.out
    refine ⟨ModuleCat.of R (P →₀ R), inferInstance,
      ModuleCat.ofHom (s.comp f.hom),
      ModuleCat.ofHom (g.hom.comp (Finsupp.linearCombination R id)), ?_⟩
    apply ModuleCat.hom_ext
    ext x
    change g.hom (Finsupp.linearCombination R id (s (f.hom x))) = φ.hom x
    rw [hs (f.hom x)]
    simpa only [ModuleCat.comp_apply] using congrArg (fun k : M ⟶ N => k x) h
  · rintro ⟨P, hP, f, g, h⟩
    exact ⟨P, inferInstance, f, g, h⟩

/-- The maps factoring through projectives are exactly the carrier of the
submodule introduced above. -/
theorem mem_factorsThroughProjectiveSubmodule_iff
    {M N : ModuleCat.{u} R} (φ : M ⟶ N) :
    φ ∈ factorsThroughProjectiveSubmodule M N ↔ FactorsThroughProjective φ := by
  constructor
  · intro hφ
    change φ ∈ Submodule.span R {φ : M ⟶ N | FactorsThroughProjective φ} at hφ
    refine Submodule.span_induction
      (p := fun x _ => FactorsThroughProjective x) ?_ ?_ ?_ ?_ hφ
    · intro x hx
      exact hx
    · exact ⟨ModuleCat.of R R, inferInstance, 0, 0, by simp⟩
    · intro φ₁ φ₂ _ _ h₁ h₂
      rcases h₁ with ⟨P₁, hP₁, f₁, g₁, e₁⟩
      rcases h₂ with ⟨P₂, hP₂, f₂, g₂, e₂⟩
      have hprod : Module.Projective R (P₁ × P₂) := by
        refine Module.Projective.of_lifting_property'' fun q hq => ?_
        rcases Module.projective_lifting_property (P := P₁) (h := hP₁) q
            (LinearMap.inl R P₁ P₂) hq with ⟨u₁, hu₁⟩
        rcases Module.projective_lifting_property (P := P₂) (h := hP₂) q
            (LinearMap.inr R P₁ P₂) hq with ⟨u₂, hu₂⟩
        exact ⟨LinearMap.coprod u₁ u₂, by
          rw [LinearMap.comp_coprod, hu₁, hu₂, LinearMap.coprod_inl_inr]⟩
      refine ⟨ModuleCat.of R (P₁ × P₂), hprod,
        ModuleCat.ofHom (LinearMap.prod f₁.hom f₂.hom),
        ModuleCat.ofHom (LinearMap.coprod g₁.hom g₂.hom), ?_⟩
      apply ModuleCat.hom_ext
      ext x
      change g₁.hom (f₁.hom x) + g₂.hom (f₂.hom x) = (φ₁ + φ₂).hom x
      rw [show g₁.hom (f₁.hom x) = φ₁.hom x by
        simpa only [ModuleCat.comp_apply] using congrArg (fun k : M ⟶ N => k x) e₁]
      rw [show g₂.hom (f₂.hom x) = φ₂.hom x by
        simpa only [ModuleCat.comp_apply] using congrArg (fun k : M ⟶ N => k x) e₂]
      rfl
    · intro a φ _ hφ
      rcases hφ with ⟨P, hP, f, g, e⟩
      refine ⟨P, hP, a • f, g, ?_⟩
      simp [e]
  · intro hφ
    exact Submodule.subset_span hφ

/-- Factoring through a projective module is stable under pre- and
postcomposition. -/
theorem factorsThroughProjective_comp
    {M M' N N' : ModuleCat.{u} R} {φ : M ⟶ N}
    (hφ : FactorsThroughProjective φ) (ψ : M' ⟶ M) (ξ : N ⟶ N') :
    FactorsThroughProjective (ψ ≫ φ ≫ ξ) := by
  rcases hφ with ⟨P, hP, f, g, h⟩
  refine ⟨P, hP, ψ ≫ f, g ≫ ξ, ?_⟩
  simpa only [Category.assoc] using congrArg (fun k : M ⟶ N => ψ ≫ k ≫ ξ) h

/-- Factoring through a free module is stable under pre- and postcomposition. -/
theorem factorsThroughFree_comp
    {M M' N N' : ModuleCat.{u} R} {φ : M ⟶ N}
    (hφ : FactorsThroughFree φ) (ψ : M' ⟶ M) (ξ : N ⟶ N') :
    FactorsThroughFree (ψ ≫ φ ≫ ξ) := by
  rcases hφ with ⟨P, hP, f, g, h⟩
  refine ⟨P, hP, ψ ≫ f, g ≫ ξ, ?_⟩
  simpa only [Category.assoc] using congrArg (fun k : M ⟶ N => ψ ≫ k ≫ ξ) h

/-- A module is projective exactly when its identity map factors through a
projective module. -/
theorem moduleProjective_iff_id_factorsThroughProjective
    (M : ModuleCat.{u} R) :
    Module.Projective R M ↔ FactorsThroughProjective (𝟙 M) := by
  constructor
  · intro hM
    exact ⟨M, hM, 𝟙 M, 𝟙 M, by simp⟩
  · rintro ⟨P, hP, f, g, h⟩
    letI : Module.Projective R (P : Type u) := hP
    apply Module.Projective.of_split f.hom g.hom
    exact ModuleCat.hom_ext_iff.mp h

/-- If the source module is finite, a factorization through a projective module
can be chosen through a finite projective module. -/
theorem factorsThroughFiniteProjective_of_factorsThroughProjective
    {M N : ModuleCat.{u} R} [Module.Finite R M] {φ : M ⟶ N}
    (hφ : FactorsThroughProjective φ) :
    FactorsThroughFiniteProjective φ := by
  classical
  rcases hφ with ⟨P, hP, f, g, hfg⟩
  obtain ⟨s, hs⟩ := hP.out
  let f₀ : M →ₗ[R] (P →₀ R) := s.comp f.hom
  have hfg₀ : (LinearMap.range f₀).FG := Submodule.fg_range f₀
  obtain ⟨T, hT⟩ := hfg₀
  let S : Finset P := T.biUnion Finsupp.support
  let U : Submodule R (P →₀ R) := Finsupp.supported R R (↑S : Set P)
  have hTU : ∀ x ∈ T, x ∈ U := by
    intro x hx
    rw [Finsupp.mem_supported]
    intro p hp
    exact Finset.mem_biUnion.mpr ⟨x, hx, hp⟩
  have hrange : LinearMap.range f₀ ≤ U := by
    rw [← hT]
    exact Submodule.span_le.2 hTU
  have hmem : ∀ x, f₀ x ∈ U := fun x => hrange ⟨x, rfl⟩
  let e : U ≃ₗ[R] (S →₀ R) :=
    Finsupp.supportedEquivFinsupp (R := R) (M := R) (↑S : Set P)
  let f₁ : M →ₗ[R] (S →₀ R) :=
    e.toLinearMap.comp (LinearMap.codRestrict U f₀ hmem)
  let i : (S →₀ R) →ₗ[R] (P →₀ R) :=
    (Submodule.subtype U).comp e.symm.toLinearMap
  have hi : i.comp f₁ = f₀ := by
    ext x p
    simp [i, f₁]
  let g₁ : (S →₀ R) →ₗ[R] N :=
    (g.hom : P →ₗ[R] N).comp
      ((Finsupp.linearCombination R (id : P → P)).comp i)
  have h₁ : g₁.comp f₁ = φ.hom := by
    ext x
    change g.hom ((Finsupp.linearCombination R (id : P → P)) (i (f₁ x))) = φ.hom x
    rw [show i (f₁ x) = f₀ x by rw [← LinearMap.comp_apply, hi]]
    change g.hom ((Finsupp.linearCombination R id) (s (f.hom x))) = φ.hom x
    rw [hs (f.hom x)]
    simpa only [ModuleCat.comp_apply] using congrArg (fun k : M ⟶ N => k x) hfg
  refine ⟨ModuleCat.of R (S →₀ R), inferInstance, inferInstance,
    ModuleCat.ofHom f₁, ModuleCat.ofHom g₁, ?_⟩
  apply ModuleCat.hom_ext
  exact h₁

end FactorThrough

section NearProjective

variable {R : Type u} [CommRing R]

/-- Every degree-one `Ext` group with first argument `M` is annihilated by `I`.
This is the Ext formulation of being close to projective. -/
def ExtOneAnnihilatedByIdeal (I : Ideal R) (M : ModuleCat.{u} R) : Prop :=
  ∀ (N : ModuleCat.{u} R) (a : R), a ∈ I →
    ∀ e : ExtGroup M N 1, a • e = 0

/-- The three source characterizations of an `I`-projective module. -/
theorem nearProjective_characterization (I : Ideal R) (M : ModuleCat.{u} R) :
    List.TFAE [
      (∀ a : R, a ∈ I → FactorsThroughProjective (a • 𝟙 M)),
      (∀ a : R, a ∈ I → FactorsThroughFree (a • 𝟙 M)),
      ExtOneAnnihilatedByIdeal I M] := by
  tfae_have 1 ↔ 2 := by
    constructor
    · intro h a ha
      exact (factorsThroughProjective_iff_factorsThroughFree (a • 𝟙 M)).mp (h a ha)
    · intro h a ha
      exact (factorsThroughProjective_iff_factorsThroughFree (a • 𝟙 M)).mpr (h a ha)
  tfae_have 1 → 3 := by
    intro h N a ha e
    rcases h a ha with ⟨P, hP, f, g, hfg⟩
    let _ : Module.Projective R (P : Type u) := hP
    have hcomp :
        (CategoryTheory.Abelian.Ext.mk₀ (a • 𝟙 M)).comp e
            (zero_add 1) = 0 := by
      rw [← hfg, ← CategoryTheory.Abelian.Ext.mk₀_comp_mk₀_assoc]
      have hz :
          (CategoryTheory.Abelian.Ext.mk₀ g).comp e (zero_add 1) = 0 :=
        CategoryTheory.Abelian.Ext.eq_zero_of_projective _
      rw [hz]
      simp only [CategoryTheory.Abelian.Ext.comp_zero]
    simpa only [CategoryTheory.Abelian.Ext.mk₀_smul,
      CategoryTheory.Abelian.Ext.smul_comp,
      CategoryTheory.Abelian.Ext.mk₀_id_comp] using hcomp
  tfae_have 3 → 1 := by
    intro h a ha
    let S := ModuleCat.projectiveShortComplex M
    have hS : S.ShortExact := ModuleCat.shortExact_projectiveShortComplex M
    have hP : Module.Projective R S.X₂ := inferInstance
    have hzero : a • hS.extClass = 0 := h S.X₁ a ha hS.extClass
    have hcomp :
        (CategoryTheory.Abelian.Ext.mk₀ (a • 𝟙 M)).comp hS.extClass
            (zero_add 1) = 0 := by
      simpa only [CategoryTheory.Abelian.Ext.mk₀_smul,
        CategoryTheory.Abelian.Ext.smul_comp,
        CategoryTheory.Abelian.Ext.mk₀_id_comp] using hzero
    obtain ⟨x₂, hx₂⟩ :=
      CategoryTheory.Abelian.Ext.covariant_sequence_exact₃ S.X₃ hS
        (CategoryTheory.Abelian.Ext.mk₀ (a • 𝟙 M)) (zero_add 1) hcomp
    obtain ⟨f', rfl⟩ :=
      CategoryTheory.Abelian.Ext.homEquiv₀.symm.surjective x₂
    have hfa : f' ≫ S.g = a • 𝟙 M :=
      CategoryTheory.Abelian.Ext.homEquiv₀.symm.injective (by simpa using hx₂)
    exact ⟨S.X₂, hP, f', S.g, hfa⟩
  tfae_finish

/-- A module is `I`-projective when multiplication by every element of `I`
factors through a projective module.  This notation is nonstandard. -/
def IsIdealProjective (I : Ideal R) (M : ModuleCat.{u} R) : Prop :=
  ∀ a : R, a ∈ I → FactorsThroughProjective (a • 𝟙 M)

/-- A module annihilated by `I` is `I`-projective. -/
theorem isIdealProjective_of_annihilated
    (I : Ideal R) (M : ModuleCat.{u} R)
    (hM : I ≤ Module.annihilator R M) :
    IsIdealProjective I M := by
  intro a ha
  have hzero : a • 𝟙 M = 0 := by
    simp [← ModuleCat.lsmul_eq_smul_id,
      Module.mem_annihilator_iff_lsmul_eq_zero.mp (hM ha)]
  exact ⟨ModuleCat.of R R, inferInstance, 0, 0, by simp [hzero]⟩

/-- In a short exact sequence, an `I`-projective quotient and a projective
middle module imply that the left module is `I`-projective. -/
theorem isIdealProjective_of_shortExact
    (I : Ideal R) (S : ShortComplex (ModuleCat.{u} R))
    (hS : S.ShortExact) (hP : Module.Projective R S.X₂)
    (hM : IsIdealProjective I S.X₃) :
    IsIdealProjective I S.X₁ := by
  intro a ha
  rcases hM a ha with ⟨Q, hQ, f, g, hfg⟩
  letI : Module.Projective R (Q : Type u) := hQ
  have hcomp :
      (CategoryTheory.Abelian.Ext.mk₀ (a • 𝟙 S.X₃)).comp hS.extClass
          (zero_add 1) = 0 := by
    rw [← hfg, ← CategoryTheory.Abelian.Ext.mk₀_comp_mk₀_assoc]
    simp only [CategoryTheory.Abelian.Ext.eq_zero_of_projective,
      CategoryTheory.Abelian.Ext.comp_zero]
  have hx₁ :
      hS.extClass.comp
          (CategoryTheory.Abelian.Ext.mk₀ (a • 𝟙 S.X₁)) (add_zero 1) = 0 := by
    simpa only [CategoryTheory.Abelian.Ext.mk₀_smul,
      CategoryTheory.Abelian.Ext.comp_smul,
      CategoryTheory.Abelian.Ext.comp_mk₀_id] using
      (show a • hS.extClass = 0 by
        simpa only [CategoryTheory.Abelian.Ext.mk₀_smul,
          CategoryTheory.Abelian.Ext.smul_comp,
          CategoryTheory.Abelian.Ext.mk₀_id_comp] using hcomp)
  obtain ⟨x₂, hx₂⟩ :=
    CategoryTheory.Abelian.Ext.contravariant_sequence_exact₁ hS S.X₁
      (CategoryTheory.Abelian.Ext.mk₀ (a • 𝟙 S.X₁)) (by simp) hx₁
  obtain ⟨f', rfl⟩ :=
    CategoryTheory.Abelian.Ext.homEquiv₀.symm.surjective x₂
  have hfa : S.f ≫ f' = a • 𝟙 S.X₁ :=
    CategoryTheory.Abelian.Ext.homEquiv₀.symm.injective (by simpa using hx₂)
  exact ⟨S.X₂, hP, S.f, f', hfa⟩

/-- The dual of a finite `I`-projective module is `I`-projective. -/
theorem isIdealProjective_dual
    (I : Ideal R) (M : ModuleCat.{u} R) [Module.Finite R M]
    (hM : IsIdealProjective I M) :
    IsIdealProjective I (ModuleCat.of R (Module.Dual R M)) := by
  intro a ha
  obtain ⟨Q, hQf, hQp, f, g, hfg⟩ :=
    factorsThroughFiniteProjective_of_factorsThroughProjective (hM a ha)
  let _ : Module.Finite R (Q : Type u) := hQf
  let _ : Module.Projective R (Q : Type u) := hQp
  refine ⟨ModuleCat.of R (Module.Dual R (Q : Type u)), inferInstance,
    ModuleCat.ofHom g.hom.dualMap, ModuleCat.ofHom f.hom.dualMap, ?_⟩
  apply ModuleCat.hom_ext
  change f.hom.dualMap.comp g.hom.dualMap =
    (a • 𝟙 (ModuleCat.of R (Module.Dual R M))).hom
  rw [LinearMap.dualMap_comp_dualMap]
  have hfg' : g.hom.comp f.hom = (a • 𝟙 M).hom :=
    ModuleCat.hom_ext_iff.mp hfg
  rw [hfg']
  ext ψ x
  change ψ (a • x) = a • ψ x
  rw [map_smul]

end NearProjective

end Formalization.Books.MoreAlgebra.Unit71
