import Formalization.Books.Algebra.Unit03.BasicNotions
import Formalization.Books.Algebra.Unit10.InternalHom
import Formalization.Books.Algebra.Unit32.LocallyNilpotent
import Formalization.Books.Algebra.Unit71.ExtGroups
import Formalization.Books.Algebra.Unit20.Nakayama
import Mathlib.Algebra.Module.FinitePresentation
import Mathlib.Algebra.Module.Projective
import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.CategoryTheory.Abelian.Projective.Dimension
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.RingTheory.FiniteLength
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.Flat.Equalizer
import Mathlib.LinearAlgebra.TensorProduct.Quotient
import Mathlib.RingTheory.Ideal.Finsupp
import Mathlib.RingTheory.LocalProperties.Projective
import Mathlib.RingTheory.LocalRing.Module
import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
import Mathlib.RingTheory.Noetherian.Basic

/-!
# Commutative Algebra, Chapter 77: Projective modules

The source's projective-module predicate is Mathlib's canonical
`Module.Projective`.  The source's `Ext^1` groups are represented by the
canonical `ExtGroup` interface from Chapter 71, and quotients by `IM` use the
canonical submodule quotient `M ⧸ I • ⊤`.
-/

namespace Formalization.Books.Algebra.Unit77

open Formalization.Books.Algebra.Unit10
open Formalization.Books.Algebra.Unit71
open scoped Pointwise

universe u

/-! ## The definition and the three characterizations -/

/- The source defines projectivity by exactness of `Hom_R(P, -)`.  We use
Mathlib's equivalent canonical predicate `Module.Projective`; the lifting
statement below records the source's immediate surjectivity consequence. -/

/-- The `Hom_R(P, -)` map induced by a surjection is surjective for a
projective module. -/
theorem projective_hom_map_surjective
    {R P M N : Type u} [CommRing R]
    [AddCommGroup P] [Module R P]
    [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N]
    [Module.Projective R P]
    (f : M →ₗ[R] N) (hf : Function.Surjective f) :
    Function.Surjective (internalHomPostcomp (M := P) f) := by
  intro g
  obtain ⟨h, hh⟩ := Module.projective_lifting_property f g hf
  exact ⟨h, hh⟩

/- `Module.Projective.iff_split` is Mathlib's source-faithful direct-summand
characterization.  The following TFAE records all three conditions in the
source, including its Ext formulation. -/

/- The predicate is stated on the bundled module category because Chapter 71's
canonical `ExtGroup` is indexed by `ModuleCat` objects. -/
def ExtOneVanishes {R : Type u} [Ring R] (P : ModuleCat.{u} R) : Prop :=
  ∀ M : ModuleCat.{u} R, ∀ e : ExtGroup P M 1, e = 0

/-- The three equivalent characterizations of a projective module. -/
theorem projective_characterization
    {R P : Type u} [CommRing R]
    [AddCommGroup P] [Module R P] :
    List.TFAE [
      Module.Projective R P,
      ∃ (F : Type u) (_ : AddCommGroup F) (_ : Module R F) (_ : Module.Free R F)
        (i : P →ₗ[R] F) (s : F →ₗ[R] P), s.comp i = LinearMap.id,
      ExtOneVanishes (ModuleCat.of R P)] := by
  tfae_have 1 ↔ 2 := by
    constructor
    · intro h
      obtain ⟨s, hs⟩ := h.out
      refine ⟨P →₀ R, inferInstance, inferInstance, inferInstance, s,
        Finsupp.linearCombination R id, ?_⟩
      ext x
      exact hs x
    · rintro ⟨F, _, _, _, i, s, hs⟩
      exact Module.Projective.of_split i s hs
  tfae_have 1 ↔ 3 := by
    rw [IsProjective.iff_projective]
    rw [CategoryTheory.projective_iff_subsingleton_ext_one]
    constructor
    · intro h M e
      exact Subsingleton.elim e 0
    · intro h M
      exact ⟨fun e₁ e₂ => (h M e₁).trans (h M e₂).symm⟩
  tfae_finish

/-! ## Ext-vanishing criteria for finite modules -/

/-- Vanishing of `Ext^1_R(P, -)` on finite modules. -/
def ExtOneVanishesOnFiniteModules {R : Type u} [Ring R]
    (P : ModuleCat.{u} R) : Prop :=
  ∀ M : ModuleCat.{u} R, Module.Finite R M →
    ∀ e : ExtGroup P M 1, e = 0

/-- Over a Noetherian ring, Ext-vanishing on finite modules detects
projectivity of a finite module. -/
theorem projective_of_ext_one_vanishes_on_finite_modules
    {R P : Type u} [CommRing R] [IsNoetherianRing R]
    [AddCommGroup P] [Module R P] [Module.Finite R P]
    (hP : ExtOneVanishesOnFiniteModules (ModuleCat.of R P)) :
    Module.Projective R P := by
  let _ : Module.FinitePresentation R P := Module.finitePresentation_of_finite R P
  obtain ⟨n, m, f, g, hf, hg⟩ := Module.FinitePresentation.exists_fin' R P
  let _ : IsNoetherian R (Fin n → R) :=
    isNoetherian_of_isNoetherianRing_of_finite R _
  let _ : Module.Finite R (LinearMap.ker f) :=
    Module.Finite.of_injective (R := R) (S := R)
      (M := LinearMap.ker f) (N := Fin n → R) (LinearMap.ker f).subtype
      (LinearMap.ker f).injective_subtype
  let S : CategoryTheory.ShortComplex (ModuleCat.{u} R) := f.shortComplexKer
  have hS : S.ShortExact := LinearMap.shortExact_shortComplexKer hf
  have hzero : hS.extClass = 0 := hP S.X₁ inferInstance hS.extClass
  let x₃ : CategoryTheory.Abelian.Ext S.X₃ S.X₃ 0 :=
    CategoryTheory.Abelian.Ext.mk₀
      (X := S.X₃) (Y := S.X₃) (CategoryTheory.CategoryStruct.id S.X₃)
  obtain ⟨x, hx⟩ :=
    CategoryTheory.Abelian.Ext.covariant_sequence_exact₃ S.X₃ hS x₃
      (zero_add 1) (by simp [hzero])
  obtain ⟨s, rfl⟩ :=
    CategoryTheory.Abelian.Ext.homEquiv₀.symm.surjective x
  have hs : CategoryTheory.CategoryStruct.comp s S.g =
      CategoryTheory.CategoryStruct.id S.X₃ :=
    CategoryTheory.Abelian.Ext.homEquiv₀.symm.injective (by simpa using hx)
  apply Module.Projective.of_split s.hom S.g.hom
  exact ModuleCat.hom_ext_iff.mp hs

/- The source also records the two standard strengthenings of this criterion:
finite presentation removes Noetherianity, and finite-length test modules
suffice in the Noetherian case. -/

/-- The finite-presentation strengthening of the finite-module criterion. -/
theorem projective_of_ext_one_vanishes_of_finite_presentation
    {R P : Type u} [CommRing R]
    [AddCommGroup P] [Module R P] [Module.FinitePresentation R P]
    (hP : ExtOneVanishesOnFiniteModules (ModuleCat.of R P)) :
    Module.Projective R P := by
  obtain ⟨n, m, f, g, hf, hg⟩ := Module.FinitePresentation.exists_fin' R P
  let _ : Module.Finite R (LinearMap.ker f) :=
    Module.Finite.of_fg (Module.FinitePresentation.fg_ker f hf)
  let S : CategoryTheory.ShortComplex (ModuleCat.{u} R) := f.shortComplexKer
  have hS : S.ShortExact := LinearMap.shortExact_shortComplexKer hf
  have hzero : hS.extClass = 0 := hP S.X₁ inferInstance hS.extClass
  let x₃ : CategoryTheory.Abelian.Ext S.X₃ S.X₃ 0 :=
    CategoryTheory.Abelian.Ext.mk₀
      (X := S.X₃) (Y := S.X₃) (CategoryTheory.CategoryStruct.id S.X₃)
  obtain ⟨x, hx⟩ :=
    CategoryTheory.Abelian.Ext.covariant_sequence_exact₃ S.X₃ hS x₃
      (zero_add 1) (by simp [hzero])
  obtain ⟨s, rfl⟩ :=
    CategoryTheory.Abelian.Ext.homEquiv₀.symm.surjective x
  have hs : CategoryTheory.CategoryStruct.comp s S.g =
      CategoryTheory.CategoryStruct.id S.X₃ :=
    CategoryTheory.Abelian.Ext.homEquiv₀.symm.injective (by simpa using hx)
  apply Module.Projective.of_split s.hom S.g.hom
  exact ModuleCat.hom_ext_iff.mp hs

/-- Over a Noetherian ring, finite-length test modules suffice for the
Ext-vanishing criterion. -/
theorem projective_of_ext_one_vanishes_on_finite_length_modules
    {R P : Type u} [CommRing R] [IsNoetherianRing R]
    [AddCommGroup P] [Module R P] [Module.Finite R P]
    (hP : ∀ M : ModuleCat.{u} R, IsFiniteLength R M →
      ∀ e : ExtGroup (ModuleCat.of R P) M 1, e = 0) :
    Module.Projective R P := by
  let _ : Module.FinitePresentation R P :=
    Module.finitePresentation_of_finite R P
  obtain ⟨n, m, f, g, hf, hg⟩ := Module.FinitePresentation.exists_fin' R P
  apply Module.projective_of_localization_maximal
  intro I hI
  let _ : I.IsPrime := hI.isPrime
  let _ := Ideal.Quotient.field I
  let e := IsLocalization.AtPrime.equivQuotMaximalIdeal I (Localization.AtPrime I)
  let eR : (R ⧸ I) ≃ₗ[R] (Localization.AtPrime I) ⧸
      IsLocalRing.maximalIdeal (Localization.AtPrime I) :=
    { e with
      map_smul' := by
        intro r x
        simp only [Algebra.smul_def, Ideal.Quotient.algebraMap_eq]
        change e (Ideal.Quotient.mk I r * x) =
          Ideal.Quotient.mk _ (algebraMap R (Localization.AtPrime I) r) * e x
        rw [← IsLocalization.AtPrime.equivQuotMaximalIdeal_apply_mk (p := I)
          (Rₚ := Localization.AtPrime I) r, ← map_mul] }
  let _ : IsSimpleModule R (R ⧸ I) :=
    (isSimpleModule_iff_isSimpleModule_of_algebraMap_surjective
      (R := R) (S := R ⧸ I) (M := R ⧸ I) Ideal.Quotient.mk_surjective).2 inferInstance
  let _ : IsSimpleModule R I.ResidueField := IsSimpleModule.congr eR.symm
  let _ : IsSimpleModule R (I.ResidueField ⧸
      (⊥ : Submodule R I.ResidueField)) :=
    IsSimpleModule.congr (Submodule.quotEquivOfEqBot _ rfl)
  have hfinite : IsFiniteLength R I.ResidueField :=
    IsFiniteLength.of_simple_quotient
      (M := I.ResidueField) (N := (⊥ : Submodule R I.ResidueField))
      (by exact IsFiniteLength.of_subsingleton)
  let Sx : CategoryTheory.ShortComplex (ModuleCat.{u} R) := f.shortComplexKer
  have hSx : Sx.ShortExact := LinearMap.shortExact_shortComplexKer hf
  have hHomSurj : Function.Surjective
      (fun q : Sx.X₂ ⟶ ModuleCat.of R I.ResidueField =>
        CategoryTheory.CategoryStruct.comp Sx.f q) := by
    intro q
    let x₁ : CategoryTheory.Abelian.Ext Sx.X₁
        (ModuleCat.of R I.ResidueField) 0 :=
      CategoryTheory.Abelian.Ext.homEquiv₀.symm q
    have hx₁ : hSx.extClass.comp x₁ (add_zero 1) = 0 := by
      exact hP (ModuleCat.of R I.ResidueField) hfinite
        (hSx.extClass.comp x₁ (add_zero 1))
    obtain ⟨x₂, hx₂⟩ :=
      CategoryTheory.Abelian.Ext.contravariant_sequence_exact₁
        hSx (ModuleCat.of R I.ResidueField) x₁ (add_zero 1) hx₁
    obtain ⟨q₂, rfl⟩ :=
      CategoryTheory.Abelian.Ext.homEquiv₀.symm.surjective x₂
    refine ⟨q₂, ?_⟩
    exact CategoryTheory.Abelian.Ext.homEquiv₀.symm.injective (by simpa [x₁] using hx₂)
  let kmap := (LinearMap.ker f).subtype
  let f' := LocalizedModule.map I.primeCompl f
  let k' := LocalizedModule.map I.primeCompl kmap
  have hfg' : Function.Exact k' f' :=
    LocalizedModule.map_exact I.primeCompl kmap f f.exact_subtype_ker_map
  have hsurj' : Function.Surjective f' :=
    LocalizedModule.map_surjective I.primeCompl f hf
  let _ : Module.Free (Localization.AtPrime I)
      (LocalizedModule I.primeCompl (Fin n → R)) :=
    Module.free_of_isLocalizedModule I.primeCompl
      (LocalizedModule.mkLinearMap I.primeCompl (Fin n → R))
  have hPfree : Module.Free (Localization.AtPrime I)
      (LocalizedModule I.primeCompl P) := by
    apply Module.free_of_lTensor_residueField_injective
      (M := LocalizedModule I.primeCompl (LinearMap.ker f))
      (N := LocalizedModule I.primeCompl (Fin n → R))
      (P := LocalizedModule I.primeCompl P) (f := k') (g := f') hsurj' hfg'
    let l : TensorProduct (Localization.AtPrime I) I.ResidueField
          (LocalizedModule I.primeCompl (LinearMap.ker f)) →ₗ[I.ResidueField]
          TensorProduct (Localization.AtPrime I) I.ResidueField
            (LocalizedModule I.primeCompl (Fin n → R)) :=
      TensorProduct.AlgebraTensorModule.map
        (R := Localization.AtPrime I) (A := I.ResidueField)
        (M := I.ResidueField) (P := I.ResidueField)
        (N := LocalizedModule I.primeCompl (LinearMap.ker f))
        (Q := LocalizedModule I.primeCompl (Fin n → R)) LinearMap.id k'
    have hl : Function.Injective l := by
      apply (LinearMap.dualMap_surjective_iff (f := l)).mp
      intro q
      let qK : LocalizedModule I.primeCompl (LinearMap.ker f) →ₗ[Localization.AtPrime I]
          I.ResidueField :=
        (q.restrictScalars (Localization.AtPrime I)).comp
          (TensorProduct.mk (Localization.AtPrime I) I.ResidueField
            (LocalizedModule I.primeCompl (LinearMap.ker f)) 1)
      let q0 : (LinearMap.ker f) →ₗ[R] I.ResidueField :=
        (qK.restrictScalars R).comp
          (LocalizedModule.mkLinearMap I.primeCompl (LinearMap.ker f))
      let qcat : Sx.X₁ ⟶ ModuleCat.of R I.ResidueField := ModuleCat.ofHom q0
      obtain ⟨q₂, hq₂⟩ := hHomSurj qcat
      let q₂' : (Fin n → R) →ₗ[R] I.ResidueField := q₂.hom
      have hq₂' : q₂'.comp kmap = q0 := by
        exact ModuleCat.hom_ext_iff.mp hq₂
      have hunit : ∀ s : I.primeCompl,
          IsUnit (algebraMap R (Module.End R I.ResidueField) s) := by
        intro s
        have hs0 : algebraMap R I.ResidueField (s : R) ≠ 0 := by
          intro hs0
          exact s.2 (Ideal.algebraMap_residueField_eq_zero.mp hs0)
        have hu : IsUnit (algebraMap R I.ResidueField (s : R)) :=
          isUnit_iff_ne_zero.mpr hs0
        have hu' := hu.map (Algebra.lsmul R R I.ResidueField).toRingHom
        have heq :
            (Algebra.lsmul R R I.ResidueField)
                (algebraMap R I.ResidueField (s : R)) =
              algebraMap R (Module.End R I.ResidueField) (s : R) :=
          (Algebra.lsmul R R I.ResidueField).commutes (s : R)
        rw [← heq]
        exact hu'
      let q₂locR : LocalizedModule I.primeCompl (Fin n → R) →ₗ[R] I.ResidueField :=
        LocalizedModule.lift I.primeCompl q₂' hunit
      let q₂loc : LocalizedModule I.primeCompl (Fin n → R) →ₗ[Localization.AtPrime I]
          I.ResidueField :=
        q₂locR.extendScalarsOfIsLocalization I.primeCompl (Localization.AtPrime I)
      have hq₂locR :
          ((q₂loc.comp k').restrictScalars R).comp
              (LocalizedModule.mkLinearMap I.primeCompl (LinearMap.ker f)) = q0 := by
        ext x
        simp [q₂loc, q₂locR, k', q₂']
        exact LinearMap.congr_fun hq₂' x
      have hq₂loc :
          LocalizedModule.lift I.primeCompl q0 hunit =
            (q₂loc.comp k').restrictScalars R :=
        LocalizedModule.lift_unique I.primeCompl q0 hunit _ hq₂locR
      have hqK :
          LocalizedModule.lift I.primeCompl q0 hunit = qK.restrictScalars R := by
        apply LocalizedModule.lift_unique
        ext x
        rfl
      have hq₂locA : q₂loc.comp k' = qK := by
        apply LinearMap.restrictScalars_injective R
        rw [← hq₂loc, hqK]
      let b : I.ResidueField →ₗ[I.ResidueField]
          LocalizedModule I.primeCompl (Fin n → R) →ₗ[Localization.AtPrime I]
            I.ResidueField :=
        { toFun := fun a => a • q₂loc
          map_add' := by
            intro a b
            ext x
            change (a + b) * q₂loc x = a * q₂loc x + b * q₂loc x
            exact add_mul a b (q₂loc x)
          map_smul' := by
            intro a b
            ext x
            change (a * b) * q₂loc x = a * (b * q₂loc x)
            exact mul_assoc a b (q₂loc x) }
      let q₂tensor :
          TensorProduct (Localization.AtPrime I) I.ResidueField
            (LocalizedModule I.primeCompl (Fin n → R)) →ₗ[I.ResidueField]
          I.ResidueField := TensorProduct.AlgebraTensorModule.lift b
      refine ⟨q₂tensor, ?_⟩
      apply TensorProduct.AlgebraTensorModule.ext
      intro a x
      change q₂tensor (l (a ⊗ₜ x)) = q (a ⊗ₜ x)
      rw [TensorProduct.AlgebraTensorModule.map_tmul,
        TensorProduct.AlgebraTensorModule.lift_tmul]
      change a * q₂loc (k' x) = q (a ⊗ₜ x)
      have hax : a ⊗ₜ[Localization.AtPrime I] x =
          a • ((1 : I.ResidueField) ⊗ₜ[Localization.AtPrime I] x) := by
        simpa using (TensorProduct.smul_tmul' a (1 : I.ResidueField) x).symm
      rw [hax, map_smul]
      change a * q₂loc (k' x) = a * qK x
      have hxq := congrArg (fun t => t x) hq₂locA
      change q₂loc (k' x) = qK x at hxq
      exact congrArg (fun y : I.ResidueField => a * y) hxq
    have hll : l = LinearMap.lTensor I.ResidueField k' := by
      apply TensorProduct.AlgebraTensorModule.ext
      intro a x
      rfl
    rw [← hll]
    exact hl
  let _ : Module.Free (Localization.AtPrime I)
      (LocalizedModule I.primeCompl P) := hPfree
  exact Module.Projective.of_free

/-! ## Direct sums and lifting across nilpotent ideals -/

/- The direct-sum assertion is exactly Mathlib's existing instance and theorem
`Module.Projective.directSum`, so no parallel wrapper is introduced. -/

/-- A projective module over `R ⧸ I` lifts to a projective `R`-module when
`I` is nilpotent. -/
theorem exists_projective_lift_of_isNilpotent
    {R : Type u} [CommRing R] (I : Ideal R)
    (hI : IsNilpotent I)
    (Pbar : ModuleCat.{u} (R ⧸ I))
    (hPbar : Module.Projective (R ⧸ I) Pbar)
    : ∃ P : ModuleCat.{u} R,
        Module.Projective R P ∧
          Nonempty ((P ⧸ (I • (⊤ : Submodule R P))) ≃ₗ[R ⧸ I] Pbar) := by
  classical
  let A := R ⧸ I
  let F : Type u := (Pbar : Type u) →₀ R
  let Fbar : Type u := (Pbar : Type u) →₀ A
  let q : F →ₗ[R] Fbar :=
    Finsupp.mapRange.linearMap (I.mkQ : R →ₗ[R] A)
  have hq : Function.Surjective q := by
    intro y
    obtain ⟨x, hx⟩ :=
      (Finsupp.mapRange_surjective (α := (Pbar : Type u))
        (I.mkQ : R → R ⧸ I) (by simp) I.mkQ_surjective) y
    exact ⟨x, by simpa [q, F, Fbar, A] using hx⟩
  have hkerq : LinearMap.ker q = I • (⊤ : Submodule R F) := by
    change LinearMap.ker
        (Finsupp.mapRange.linearMap (α := (Pbar : Type u))
          (I.mkQ : R →ₗ[R] A)) = I • (⊤ : Submodule R F)
    rw [Finsupp.ker_mapRange]
    rw [show LinearMap.ker (I.mkQ : R →ₗ[R] A) = I from Submodule.ker_mkQ I]
    calc
      Finsupp.submodule (fun _ : (Pbar : Type u) => I) =
          Finsupp.submodule (fun _ => I • (⊤ : Submodule R R)) := by simp
      _ = I • Finsupp.submodule (fun _ : (Pbar : Type u) => (⊤ : Submodule R R)) :=
        Finsupp.submodule_smul R (Pbar : Type u)
          (fun _ : (Pbar : Type u) => (⊤ : Submodule R R)) I
      _ = I • (⊤ : Submodule R F) := by rw [Finsupp.submodule_top]
  let sbar : Fbar →ₗ[A] Pbar := Finsupp.linearCombination A id
  have hsbar : Function.Surjective sbar := by
    simpa [sbar] using (Finsupp.linearCombination_id_surjective (R := A) Pbar)
  obtain ⟨ibar, hibar⟩ :=
    (Module.Projective.iff_split_of_projective sbar hsbar).mp hPbar
  let pbar : Module.End A Fbar := ibar.comp sbar
  have hpbar : pbar.comp pbar = pbar := by
    apply LinearMap.ext
    intro x
    change ibar (sbar (ibar (sbar x))) = ibar (sbar x)
    have hx : sbar (ibar (sbar x)) = sbar x := by
      simpa using congrArg (fun f : Pbar →ₗ[A] Pbar => f (sbar x)) hibar
    rw [hx]
  let pbarR : Fbar →ₗ[R] Fbar := pbar.restrictScalars R
  obtain ⟨p, hp⟩ := Module.projective_lifting_property q (pbarR.comp q) hq
  let d : Module.End R F := p * p - p
  have hpbarR : pbarR.comp pbarR = pbarR := by
    simpa [pbarR] using
      congrArg (fun f : Module.End A Fbar => f.restrictScalars R) hpbar
  have hdq : q.comp d = 0 := by
    apply LinearMap.ext
    intro x
    dsimp [d]
    change q (p (p x) - p x) = 0
    rw [map_sub]
    have hx : q (p x) = pbarR (q x) := by
      simpa using congrArg (fun f : F →ₗ[R] Fbar => f x) hp
    have hpx : q (p (p x)) = pbarR (q (p x)) := by
      simpa using congrArg (fun f : F →ₗ[R] Fbar => f (p x)) hp
    rw [hpx, hx]
    apply sub_eq_zero.mpr
    simpa [LinearMap.comp_apply] using congrArg (fun z => z (q x)) hpbarR
  have hdmem (x : F) : d x ∈ I • (⊤ : Submodule R F) := by
    rw [← hkerq, LinearMap.mem_ker]
    exact congrArg (fun f => f x) hdq
  have hdmap (k : ℕ) {x : F} (hx : x ∈ I ^ k • (⊤ : Submodule R F)) :
      d x ∈ I ^ (k + 1) • (⊤ : Submodule R F) := by
    refine Submodule.smul_induction_on hx (fun r hr y _ => ?_) (fun x y hx hy => ?_)
    · rw [map_smul]
      simpa [pow_succ, Submodule.mul_smul] using
        (Submodule.smul_mem_smul hr (hdmem y))
    · rw [map_add]
      exact Submodule.add_mem _ hx hy
  have hdnil : IsNilpotent d := by
    obtain ⟨n, hn⟩ := hI
    refine ⟨n, ?_⟩
    apply LinearMap.ext
    intro x
    have hpow : ∀ k : ℕ, (d ^ k) x ∈ I ^ k • (⊤ : Submodule R F) := by
      intro k
      induction k with
      | zero => simp
      | succ k ih =>
          simpa [pow_succ', Module.End.mul_eq_comp] using hdmap k ih
    have := hpow n
    rw [hn] at this
    simpa using this
  obtain ⟨e, he, s, a, hes⟩ :=
    Formalization.Books.Algebra.Unit32.exists_idempotent_lift_polynomial p hdnil
  have heqred : q.comp e = pbarR.comp q := by
    apply LinearMap.ext
    intro x
    have hxe : e = p + d *
        (∑ ij ∈ s, (a ij : Module.End R F) * p ^ ij.1 * d ^ ij.2) := by
      simpa [d, pow_two, Module.End.mul_eq_comp] using hes
    rw [hxe]
    change q (p x + d
      ((∑ ij ∈ s, (a ij : Module.End R F) * p ^ ij.1 * d ^ ij.2) x)) = _
    rw [map_add]
    have hdx : q (d
        ((∑ ij ∈ s, (a ij : Module.End R F) * p ^ ij.1 * d ^ ij.2) x)) = 0 := by
      simpa using congrArg (fun f => f
        ((∑ ij ∈ s, (a ij : Module.End R F) * p ^ ij.1 * d ^ ij.2) x)) hdq
    rw [hdx]
    simpa using congrArg (fun f => f x) hp
  let Psub : Submodule R F := LinearMap.range e
  letI : AddCommGroup (Psub : Type u) := inferInstance
  letI : Module R (Psub : Type u) := inferInstance
  let P : ModuleCat.{u} R := ModuleCat.of R Psub
  let inc : Psub →ₗ[R] F := Psub.subtype
  let ret : F →ₗ[R] Psub := e.codRestrict Psub
    (fun x => LinearMap.mem_range_self e x)
  have hret : ret.comp inc = LinearMap.id := by
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    have he' : e.comp e = e := by
      change e * e = e
      exact he
    obtain ⟨y, hy⟩ := x.property
    change e (x : F) = (x : F)
    calc
      e (x : F) = e (e y) := by rw [hy]
      _ = e y := by simpa [LinearMap.comp_apply] using congrArg (fun f => f y) he'
      _ = (x : F) := hy
  have hproj : Module.Projective R Psub :=
    Module.Projective.of_split inc ret hret
  have hqPmem : I • (⊤ : Submodule R Psub) ≤
      LinearMap.ker (q.comp inc) := by
    intro x hx
    refine Submodule.smul_induction_on hx (fun r hr y _ => ?_) (fun x y hx hy => ?_)
    · change q (inc (r • y)) = 0
      rw [map_smul, map_smul]
      have hr0 : I.mkQ r = 0 := (Submodule.Quotient.mk_eq_zero I).2 hr
      have hr0' : Ideal.Quotient.mk I r = 0 :=
        Ideal.Quotient.eq_zero_iff_mem.mpr hr
      rw [← IsScalarTower.algebraMap_smul A r, Ideal.Quotient.algebraMap_eq,
        hr0', zero_smul]
    · change q (inc (x + y)) = 0
      rw [map_add, map_add]
      have hx0 : q (inc x) = 0 := LinearMap.mem_ker.mp hx
      have hy0 : q (inc y) = 0 := LinearMap.mem_ker.mp hy
      rw [hx0, hy0, add_zero]
  let qP0 : ((Psub : Type u) ⧸ (I • (⊤ : Submodule R (Psub : Type u)))) →ₗ[R] Fbar :=
    ((⊥ : Submodule R Fbar).quotEquivOfEqBot rfl).toLinearMap.comp
      (Submodule.mapQ (I • (⊤ : Submodule R (Psub : Type u)))
        (⊥ : Submodule R Fbar) (q.comp inc) hqPmem)
  let qP : ((Psub : Type u) ⧸ (I • (⊤ : Submodule R (Psub : Type u)))) →ₗ[A] Fbar :=
    LinearMap.extendScalarsOfSurjective I.mkQ_surjective qP0
  have hqP_mk (x : Psub) :
      qP (Submodule.Quotient.mk x) = q (inc x) := by
    rfl
  have hret_mem (x : F) (hx : x ∈ I • (⊤ : Submodule R F)) :
      ret x ∈ I • (⊤ : Submodule R Psub) := by
    refine Submodule.smul_induction_on hx (fun r hr y _ => ?_) (fun x y hx hy => ?_)
    · rw [map_smul]
      exact Submodule.smul_mem_smul hr Submodule.mem_top
    · rw [map_add]
      exact Submodule.add_mem _ hx hy
  have he_on (x : Psub) : e (inc x) = inc x := by
    have he' : e.comp e = e := by
      change e * e = e
      exact he
    obtain ⟨y, hy⟩ := x.property
    change e (x : F) = (x : F)
    calc
      e (x : F) = e (e y) := by rw [hy]
      _ = e y := by simpa [LinearMap.comp_apply] using congrArg (fun f => f y) he'
      _ = (x : F) := hy
  let φ : ((Psub : Type u) ⧸ (I • (⊤ : Submodule R (Psub : Type u)))) →ₗ[A] Pbar :=
    sbar.comp qP
  have hφ_surj : Function.Surjective φ := by
    intro y
    obtain ⟨x, hx⟩ := hq (ibar y)
    let z : Psub := ⟨e x, LinearMap.mem_range_self e x⟩
    refine ⟨Submodule.Quotient.mk z, ?_⟩
    change sbar (qP (Submodule.Quotient.mk z)) = y
    rw [hqP_mk]
    have hred := congrArg (fun f => f x) heqred
    change sbar (q (e x)) = y
    have hred' : q (e x) = pbarR (q x) := by simpa using hred
    rw [hred', hx]
    have hpibar : pbar (ibar y) = ibar y := by
      change ibar (sbar (ibar y)) = ibar y
      rw [show sbar (ibar y) = y by
        simpa using congrArg (fun f : Pbar →ₗ[A] Pbar => f y) hibar]
    change sbar (pbar (ibar y)) = y
    rw [hpibar]
    simpa using congrArg (fun f : Pbar →ₗ[A] Pbar => f y) hibar
  have hφ_inj : Function.Injective φ := by
    intro x y hxy
    obtain ⟨x, rfl⟩ :=
      (Submodule.Quotient.mk_surjective (I • (⊤ : Submodule R (Psub : Type u)))) x
    obtain ⟨y, rfl⟩ :=
      (Submodule.Quotient.mk_surjective (I • (⊤ : Submodule R (Psub : Type u)))) y
    change sbar (qP (Submodule.Quotient.mk x)) =
      sbar (qP (Submodule.Quotient.mk y)) at hxy
    rw [hqP_mk x, hqP_mk y] at hxy
    have hxy' : sbar (q (inc x)) = sbar (q (inc y)) := hxy
    have hps : pbar (q (inc x)) = pbar (q (inc y)) := by
      simpa [pbar, LinearMap.comp_apply] using congrArg ibar hxy'
    have hqx : q (inc x) = pbarR (q (inc x)) := by
      have hred := congrArg (fun f => f (inc x)) heqred
      have hred' : q (e (inc x)) = pbarR (q (inc x)) := by simpa using hred
      rw [he_on x] at hred'
      exact hred'
    have hqy : q (inc y) = pbarR (q (inc y)) := by
      have hred := congrArg (fun f => f (inc y)) heqred
      have hred' : q (e (inc y)) = pbarR (q (inc y)) := by simpa using hred
      rw [he_on y] at hred'
      exact hred'
    have hqxy : q (inc x - inc y) = 0 := by
      rw [map_sub]
      calc
        q (inc x) - q (inc y) =
            pbarR (q (inc x)) - pbarR (q (inc y)) :=
              congrArg₂ (fun a b : Fbar => a - b) hqx hqy
        _ = 0 := by
          have hpsR : pbarR (q (inc x)) = pbarR (q (inc y)) := by
            change pbar (q (inc x)) = pbar (q (inc y))
            exact hps
          rw [hpsR, sub_self]
    have hmemF : inc x - inc y ∈ I • (⊤ : Submodule R F) := by
      rw [← hkerq, LinearMap.mem_ker]
      exact hqxy
    have hmemP : x - y ∈ I • (⊤ : Submodule R Psub) := by
      have hmem := hret_mem (inc x - inc y) hmemF
      have hmem' : ret (inc (x - y)) ∈ I • (⊤ : Submodule R Psub) := by
        simpa only [map_sub] using hmem
      have hret' : ret (inc (x - y)) = x - y := by
        simpa [LinearMap.comp_apply] using congrArg (fun f => f (x - y)) hret
      rw [hret'] at hmem'
      exact hmem'
    rw [← sub_eq_zero]
    change Submodule.Quotient.mk (x - y) = 0
    exact (Submodule.Quotient.mk_eq_zero _).2 hmemP
  refine ⟨P, ?_, ?_⟩
  · exact hproj
  · exact ⟨LinearEquiv.ofBijective φ ⟨hφ_inj, hφ_surj⟩⟩

private theorem isNilpotent_ideal_span_finset
    {R : Type u} [CommRing R] (s : Finset R)
    (hs : ∀ x ∈ s, IsNilpotent x) :
    IsNilpotent (Ideal.span (s : Set R)) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      refine ⟨1, ?_⟩
      simp
  | @insert a s ha ih =>
      obtain ⟨n, hn⟩ := hs a (Finset.mem_insert_self a s)
      obtain ⟨m, hm⟩ := ih (fun x hx => hs x (Finset.mem_insert_of_mem hx))
      have ha_span : (Ideal.span ({a} : Set R)) ^ n = ⊥ := by
        rw [Ideal.span_singleton_pow, hn]
        simp
      refine ⟨n + m, le_antisymm ?_ bot_le⟩
      rw [Finset.coe_insert, Ideal.span_insert]
      exact (Ideal.sup_pow_add_le_pow_sup_pow.trans (by rw [ha_span, hm]; simp))

/- The source calls an ideal locally nilpotent when each of its elements is
nilpotent; this is the earlier chapter's canonical `locallyNilpotentIdeal`. -/

/-- A finite projective module over `R ⧸ I` lifts to a finite projective
`R`-module when `I` is locally nilpotent. -/
theorem exists_finite_projective_lift_of_locallyNilpotent
    {R : Type u} [CommRing R] (I : Ideal R)
    (hI : Formalization.Books.Algebra.Unit03.locallyNilpotentIdeal I)
    (Pbar : ModuleCat.{u} (R ⧸ I))
    [Module.Finite (R ⧸ I) Pbar]
    (hPbar : Module.Projective (R ⧸ I) Pbar) :
    ∃ P : ModuleCat.{u} R,
        Module.Finite R P ∧ Module.Projective R P ∧
        Nonempty ((P ⧸ (I • (⊤ : Submodule R P))) ≃ₗ[R ⧸ I] Pbar) := by
  classical
  let A := R ⧸ I
  obtain ⟨n, sbar, hsbar⟩ := Module.Finite.exists_fin' A Pbar
  let F : Type u := Fin n → R
  let Fbar : Type u := Fin n → A
  let q : F →ₗ[R] Fbar :=
    LinearMap.piMap (fun _ : Fin n => (I.mkQ : R →ₗ[R] A))
  have hq : Function.Surjective q := by
    intro y
    choose x hx using fun i : Fin n => I.mkQ_surjective (y i)
    refine ⟨x, ?_⟩
    ext i
    change I.mkQ (x i) = y i
    exact hx i
  obtain ⟨ibar, hibar⟩ :=
    (Module.Projective.iff_split_of_projective sbar hsbar).mp hPbar
  let pbar : Module.End A Fbar := ibar.comp sbar
  have hpbar : pbar.comp pbar = pbar := by
    apply LinearMap.ext
    intro x
    change ibar (sbar (ibar (sbar x))) = ibar (sbar x)
    have hx : sbar (ibar (sbar x)) = sbar x := by
      simpa using congrArg (fun f : Pbar →ₗ[A] Pbar => f (sbar x)) hibar
    rw [hx]
  let pbarR : Fbar →ₗ[R] Fbar := pbar.restrictScalars R
  obtain ⟨p, hp⟩ := Module.projective_lifting_property q (pbarR.comp q) hq
  let d : Module.End R F := p * p - p
  have hpbarR : pbarR.comp pbarR = pbarR := by
    simpa [pbarR] using
      congrArg (fun f : Module.End A Fbar => f.restrictScalars R) hpbar
  have hdq : q.comp d = 0 := by
    apply LinearMap.ext
    intro x
    dsimp [d]
    change q (p (p x) - p x) = 0
    rw [map_sub]
    have hx : q (p x) = pbarR (q x) := by
      simpa using congrArg (fun f : F →ₗ[R] Fbar => f x) hp
    have hpx : q (p (p x)) = pbarR (q (p x)) := by
      simpa using congrArg (fun f : F →ₗ[R] Fbar => f (p x)) hp
    rw [hpx, hx]
    apply sub_eq_zero.mpr
    simpa [LinearMap.comp_apply] using congrArg (fun z => z (q x)) hpbarR
  have hcoeff (ij : Fin n × Fin n) :
      (d (Pi.single ij.2 1)) ij.1 ∈ I := by
    have h := congrArg
      (fun f : F →ₗ[R] Fbar => (f (Pi.single ij.2 1)) ij.1) hdq
    change I.mkQ ((d (Pi.single ij.2 1)) ij.1) = 0 at h
    exact (Submodule.Quotient.mk_eq_zero I).mp h
  let t : Finset R :=
    Finset.univ.image (fun ij : Fin n × Fin n => (d (Pi.single ij.2 1)) ij.1)
  let J : Ideal R := Ideal.span (t : Set R)
  have ht : ∀ x ∈ t, IsNilpotent x := by
    intro x hx
    rcases Finset.mem_image.mp hx with ⟨ij, -, rfl⟩
    exact hI _ (hcoeff ij)
  have hvec {v : F} (hv : ∀ i, v i ∈ J) :
      v ∈ J • (⊤ : Submodule R F) := by
    rw [show v = (∑ i : Fin n, v i • Pi.single i 1) by
      ext k
      simp [Finset.sum_apply, Pi.single_apply]]
    apply Submodule.sum_mem
    intro i hi
    exact Submodule.smul_mem_smul (hv i) Submodule.mem_top
  have hdy (x : F) : d x ∈ J • (⊤ : Submodule R F) := by
    have hx : x = (∑ j : Fin n, x j • Pi.single j 1) := by
      ext k
      simp [Finset.sum_apply, Pi.single_apply]
    rw [hx, map_sum]
    apply Submodule.sum_mem
    intro j hj
    rw [map_smul]
    exact (J • (⊤ : Submodule R F)).smul_mem (x j) (hvec (fun i => by
      change (d (Pi.single j 1)) i ∈ J
      apply Ideal.subset_span
      exact Finset.mem_image.mpr ⟨(i, j), Finset.mem_univ _, rfl⟩))
  have hdmap (k : ℕ) {x : F} (hx : x ∈ J ^ k • (⊤ : Submodule R F)) :
      d x ∈ J ^ (k + 1) • (⊤ : Submodule R F) := by
    refine Submodule.smul_induction_on hx (fun r hr y _ => ?_) (fun x y hx hy => ?_)
    · rw [map_smul]
      rw [pow_succ, Submodule.mul_smul]
      exact Submodule.smul_mem_smul hr (hdy y)
    · rw [map_add]
      exact Submodule.add_mem _ hx hy
  have hdnil : IsNilpotent d := by
    obtain ⟨n, hn⟩ := isNilpotent_ideal_span_finset t ht
    refine ⟨n, ?_⟩
    apply LinearMap.ext
    intro x
    have hpow : ∀ k : ℕ, (d ^ k) x ∈ J ^ k • (⊤ : Submodule R F) := by
      intro k
      induction k with
      | zero =>
          have hone : (1 : R) ∈ J ^ 0 := by
            simp only [pow_zero]
            change (1 : R) ∈ (1 : Ideal R)
            simp
          simpa only [pow_zero, Module.End.one_apply, one_smul] using
            (Submodule.smul_mem_smul hone
              (Submodule.mem_top : x ∈ (⊤ : Submodule R F)))
      | succ k ih =>
          simpa [pow_succ', Module.End.mul_eq_comp] using hdmap k ih
    have := hpow n
    rw [hn] at this
    simpa using this
  obtain ⟨e, he, s, a, hes⟩ :=
    Formalization.Books.Algebra.Unit32.exists_idempotent_lift_polynomial p hdnil
  have heqred : q.comp e = pbarR.comp q := by
    apply LinearMap.ext
    intro x
    have hxe : e = p + d *
        (∑ ij ∈ s, (a ij : Module.End R F) * p ^ ij.1 * d ^ ij.2) := by
      simpa [d, pow_two, Module.End.mul_eq_comp] using hes
    rw [hxe]
    change q (p x + d
      ((∑ ij ∈ s, (a ij : Module.End R F) * p ^ ij.1 * d ^ ij.2) x)) = _
    rw [map_add]
    have hdx : q (d
        ((∑ ij ∈ s, (a ij : Module.End R F) * p ^ ij.1 * d ^ ij.2) x)) = 0 := by
      simpa using congrArg (fun f => f
        ((∑ ij ∈ s, (a ij : Module.End R F) * p ^ ij.1 * d ^ ij.2) x)) hdq
    rw [hdx]
    simpa using congrArg (fun f => f x) hp
  let Psub : Submodule R F := LinearMap.range e
  letI : AddCommGroup (Psub : Type u) := inferInstance
  letI : Module R (Psub : Type u) := inferInstance
  let P : ModuleCat.{u} R := ModuleCat.of R Psub
  let inc : Psub →ₗ[R] F := Psub.subtype
  let ret : F →ₗ[R] Psub := e.codRestrict Psub
    (fun x => LinearMap.mem_range_self e x)
  have hret : ret.comp inc = LinearMap.id := by
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    have he' : e.comp e = e := by
      change e * e = e
      exact he
    obtain ⟨y, hy⟩ := x.property
    change e (x : F) = (x : F)
    calc
      e (x : F) = e (e y) := by rw [hy]
      _ = e y := by simpa [LinearMap.comp_apply] using congrArg (fun f => f y) he'
      _ = (x : F) := hy
  have hproj : Module.Projective R Psub :=
    Module.Projective.of_split inc ret hret
  have hqPmem : I • (⊤ : Submodule R Psub) ≤
      LinearMap.ker (q.comp inc) := by
    intro x hx
    refine Submodule.smul_induction_on hx (fun r hr y _ => ?_) (fun x y hx hy => ?_)
    · change q (inc (r • y)) = 0
      rw [map_smul, map_smul]
      have hr0 : I.mkQ r = 0 := (Submodule.Quotient.mk_eq_zero I).2 hr
      have hr0' : Ideal.Quotient.mk I r = 0 :=
        Ideal.Quotient.eq_zero_iff_mem.mpr hr
      rw [← IsScalarTower.algebraMap_smul A r, Ideal.Quotient.algebraMap_eq,
        hr0', zero_smul]
    · change q (inc (x + y)) = 0
      rw [map_add, map_add]
      have hx0 : q (inc x) = 0 := LinearMap.mem_ker.mp hx
      have hy0 : q (inc y) = 0 := LinearMap.mem_ker.mp hy
      rw [hx0, hy0, add_zero]
  have hmem_of_qzero {z : F} (hz : q z = 0) :
      z ∈ I • (⊤ : Submodule R F) := by
    rw [show z = (∑ i : Fin n, z i • Pi.single i 1) by
      ext k
      simp [Finset.sum_apply, Pi.single_apply]]
    apply Submodule.sum_mem
    intro i hi
    have hzi := congrFun hz i
    change I.mkQ (z i) = 0 at hzi
    exact Submodule.smul_mem_smul ((Submodule.Quotient.mk_eq_zero I).mp hzi)
      Submodule.mem_top
  let qP0 : ((Psub : Type u) ⧸ (I • (⊤ : Submodule R (Psub : Type u)))) →ₗ[R] Fbar :=
    ((⊥ : Submodule R Fbar).quotEquivOfEqBot rfl).toLinearMap.comp
      (Submodule.mapQ (I • (⊤ : Submodule R (Psub : Type u)))
        (⊥ : Submodule R Fbar) (q.comp inc) hqPmem)
  let qP : ((Psub : Type u) ⧸ (I • (⊤ : Submodule R (Psub : Type u)))) →ₗ[A] Fbar :=
    LinearMap.extendScalarsOfSurjective I.mkQ_surjective qP0
  have hqP_mk (x : Psub) :
      qP (Submodule.Quotient.mk x) = q (inc x) := by
    rfl
  have hret_mem (x : F) (hx : x ∈ I • (⊤ : Submodule R F)) :
      ret x ∈ I • (⊤ : Submodule R Psub) := by
    refine Submodule.smul_induction_on hx (fun r hr y _ => ?_) (fun x y hx hy => ?_)
    · rw [map_smul]
      exact Submodule.smul_mem_smul hr Submodule.mem_top
    · rw [map_add]
      exact Submodule.add_mem _ hx hy
  have he_on (x : Psub) : e (inc x) = inc x := by
    have he' : e.comp e = e := by
      change e * e = e
      exact he
    obtain ⟨y, hy⟩ := x.property
    change e (x : F) = (x : F)
    calc
      e (x : F) = e (e y) := by rw [hy]
      _ = e y := by simpa [LinearMap.comp_apply] using congrArg (fun f => f y) he'
      _ = (x : F) := hy
  let φ : ((Psub : Type u) ⧸ (I • (⊤ : Submodule R (Psub : Type u)))) →ₗ[A] Pbar :=
    sbar.comp qP
  have hφ_surj : Function.Surjective φ := by
    intro y
    obtain ⟨x, hx⟩ := hq (ibar y)
    let z : Psub := ⟨e x, LinearMap.mem_range_self e x⟩
    refine ⟨Submodule.Quotient.mk z, ?_⟩
    change sbar (qP (Submodule.Quotient.mk z)) = y
    rw [hqP_mk]
    have hred := congrArg (fun f => f x) heqred
    change sbar (q (e x)) = y
    have hred' : q (e x) = pbarR (q x) := by simpa using hred
    rw [hred', hx]
    have hpibar : pbar (ibar y) = ibar y := by
      change ibar (sbar (ibar y)) = ibar y
      rw [show sbar (ibar y) = y by
        simpa using congrArg (fun f : Pbar →ₗ[A] Pbar => f y) hibar]
    change sbar (pbar (ibar y)) = y
    rw [hpibar]
    simpa using congrArg (fun f : Pbar →ₗ[A] Pbar => f y) hibar
  have hφ_inj : Function.Injective φ := by
    intro x y hxy
    obtain ⟨x, rfl⟩ :=
      (Submodule.Quotient.mk_surjective (I • (⊤ : Submodule R (Psub : Type u)))) x
    obtain ⟨y, rfl⟩ :=
      (Submodule.Quotient.mk_surjective (I • (⊤ : Submodule R (Psub : Type u)))) y
    change sbar (qP (Submodule.Quotient.mk x)) =
      sbar (qP (Submodule.Quotient.mk y)) at hxy
    rw [hqP_mk x, hqP_mk y] at hxy
    have hxy' : sbar (q (inc x)) = sbar (q (inc y)) := hxy
    have hps : pbar (q (inc x)) = pbar (q (inc y)) := by
      simpa [pbar, LinearMap.comp_apply] using congrArg ibar hxy'
    have hqx : q (inc x) = pbarR (q (inc x)) := by
      have hred := congrArg (fun f => f (inc x)) heqred
      have hred' : q (e (inc x)) = pbarR (q (inc x)) := by simpa using hred
      rw [he_on x] at hred'
      exact hred'
    have hqy : q (inc y) = pbarR (q (inc y)) := by
      have hred := congrArg (fun f => f (inc y)) heqred
      have hred' : q (e (inc y)) = pbarR (q (inc y)) := by simpa using hred
      rw [he_on y] at hred'
      exact hred'
    have hqxy : q (inc x - inc y) = 0 := by
      rw [map_sub]
      calc
        q (inc x) - q (inc y) =
            pbarR (q (inc x)) - pbarR (q (inc y)) :=
              congrArg₂ (fun a b : Fbar => a - b) hqx hqy
        _ = 0 := by
          have hpsR : pbarR (q (inc x)) = pbarR (q (inc y)) := by
            change pbar (q (inc x)) = pbar (q (inc y))
            exact hps
          rw [hpsR, sub_self]
    have hmemF : inc x - inc y ∈ I • (⊤ : Submodule R F) := by
      exact hmem_of_qzero hqxy
    have hmemP : x - y ∈ I • (⊤ : Submodule R Psub) := by
      have hmem := hret_mem (inc x - inc y) hmemF
      have hmem' : ret (inc (x - y)) ∈ I • (⊤ : Submodule R Psub) := by
        simpa only [map_sub] using hmem
      have hret' : ret (inc (x - y)) = x - y := by
        simpa [LinearMap.comp_apply] using congrArg (fun f => f (x - y)) hret
      rw [hret'] at hmem'
      exact hmem'
    rw [← sub_eq_zero]
    change Submodule.Quotient.mk (x - y) = 0
    exact (Submodule.Quotient.mk_eq_zero _).2 hmemP
  have hret_surj : Function.Surjective ret := by
    intro x
    refine ⟨inc x, ?_⟩
    simpa [LinearMap.comp_apply] using congrArg (fun f => f x) hret
  have hfinite : Module.Finite R Psub :=
    Module.Finite.of_surjective ret hret_surj
  refine ⟨P, hfinite, hproj, ?_⟩
  exact ⟨LinearEquiv.ofBijective φ ⟨hφ_inj, hφ_surj⟩⟩

/-- A flat module whose reduction modulo a nilpotent ideal is projective is
projective. -/
theorem projective_of_flat_of_isNilpotent_of_quotient_projective
    {R : Type u} [CommRing R] (I : Ideal R) (M : ModuleCat.{u} R)
    (hI : IsNilpotent I)
    [Module.Flat R M]
    (hMbar : Module.Projective (R ⧸ I)
      (M ⧸ (I • (⊤ : Submodule R M)))) :
    Module.Projective R M := by
  classical
  let A := R ⧸ I
  let M0 : Type u := M
  let IM : Submodule R M0 := I • (⊤ : Submodule R M0)
  obtain ⟨P, hP, hPE⟩ :=
    exists_projective_lift_of_isNilpotent I hI
      (ModuleCat.of A (M0 ⧸ IM)) hMbar
  obtain ⟨e⟩ := hPE
  let IP : Submodule R (P : Type u) := I • (⊤ : Submodule R (P : Type u))
  let mQ : M0 →ₗ[R] (M0 ⧸ IM) := IM.mkQ
  let g : (P : Type u) →ₗ[R] (M0 ⧸ IM) :=
    e.toLinearMap.restrictScalars R |>.comp IP.mkQ
  obtain ⟨q, hq⟩ :=
    Module.projective_lifting_property mQ g IM.mkQ_surjective
  have hqmem : IP ≤ LinearMap.ker (mQ.comp q) := by
    intro x hx
    refine Submodule.smul_induction_on hx (fun r hr y _ => ?_) (fun x y hx hy => ?_)
    · change mQ (q (r • y)) = 0
      rw [map_smul, map_smul]
      have hr0 : I.mkQ r = 0 := (Submodule.Quotient.mk_eq_zero I).2 hr
      have hr0' : Ideal.Quotient.mk I r = 0 :=
        Ideal.Quotient.eq_zero_iff_mem.mpr hr
      rw [← IsScalarTower.algebraMap_smul A r, Ideal.Quotient.algebraMap_eq,
        hr0', zero_smul]
    · change mQ (q (x + y)) = 0
      rw [map_add, map_add]
      have hx0 : mQ (q x) = 0 := LinearMap.mem_ker.mp hx
      have hy0 : mQ (q y) = 0 := LinearMap.mem_ker.mp hy
      rw [hx0, hy0, add_zero]
  have hIPmap : IP ≤ IM.comap q := by
    intro x hx
    change q x ∈ IM
    exact (Submodule.Quotient.mk_eq_zero IM).mp
      (LinearMap.mem_ker.mp (hqmem hx))
  let qbar0 : (P : Type u) ⧸ IP →ₗ[R] (M0 ⧸ IM) :=
    Submodule.mapQ IP IM q hIPmap
  let qbar : (P : Type u) ⧸ IP →ₗ[A] (M0 ⧸ IM) :=
    LinearMap.extendScalarsOfSurjective I.mkQ_surjective qbar0
  have hqbar_mk (x : P) : qbar (Submodule.Quotient.mk x) = mQ (q x) := by
    rfl
  have hqbar_eq : qbar = e.toLinearMap := by
    apply LinearMap.ext
    intro x
    obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective IP x
    have hqred := congrArg (fun f => f y) hq
    change qbar (Submodule.Quotient.mk y) = e (Submodule.Quotient.mk y)
    rw [hqbar_mk]
    exact hqred
  have hqbar_surj : Function.Surjective qbar := by
    rw [hqbar_eq]
    exact e.surjective
  have hqsurj : Function.Surjective q := by
    apply Formalization.Books.Algebra.Unit20.nakayama_part_eleven I q
    exact hqbar_surj
    exact hI
  have hqbar_inj : Function.Injective qbar := by
    rw [hqbar_eq]
    exact e.injective
  have hqbarR : Function.Injective (qbar.restrictScalars R) := hqbar_inj
  let eP := TensorProduct.quotTensorEquivQuotSMul (P : Type u) I
  let eM := TensorProduct.quotTensorEquivQuotSMul M0 I
  have hcomm : eM.toLinearMap.comp (q.lTensor A) =
      (qbar.restrictScalars R).comp eP.toLinearMap := by
    apply TensorProduct.ext'
    intro a x
    obtain ⟨r, rfl⟩ := I.mkQ_surjective a
    change TensorProduct.quotTensorEquivQuotSMul M0 I
        (Ideal.Quotient.mk I r ⊗ₜ[R] q x) =
      qbar (TensorProduct.quotTensorEquivQuotSMul (P : Type u) I
        (Ideal.Quotient.mk I r ⊗ₜ[R] x))
    rw [TensorProduct.quotTensorEquivQuotSMul_mk_tmul,
      TensorProduct.quotTensorEquivQuotSMul_mk_tmul, hqbar_mk]
    simp
    rfl
  have hlt_inj : Function.Injective (q.lTensor A) := by
    intro x y hxy
    apply eP.injective
    apply hqbarR
    calc
      (qbar.restrictScalars R) (eP x) = eM (q.lTensor A x) := by
        simpa [LinearMap.comp_apply] using congrArg (fun f => f x) hcomm.symm
      _ = eM (q.lTensor A y) := congrArg eM hxy
      _ = (qbar.restrictScalars R) (eP y) := by
        simpa [LinearMap.comp_apply] using congrArg (fun f => f y) hcomm
  have hltker : Subsingleton (LinearMap.ker (q.lTensor A)) := by
    have hbot : LinearMap.ker (q.lTensor A) = ⊥ :=
      LinearMap.ker_eq_bot.mpr hlt_inj
    rw [hbot]
    infer_instance
  have htensorK : Subsingleton
      (TensorProduct R A (LinearMap.ker q)) := by
    let ek := LinearMap.kerLTensorEquivOfSurjective q hqsurj A
    constructor
    intro x y
    apply ek.symm.injective
    exact Subsingleton.elim _ _
  have hKquot : Subsingleton
      (LinearMap.ker q ⧸ (I • (⊤ : Submodule R (LinearMap.ker q)))) := by
    let ek := TensorProduct.quotTensorEquivQuotSMul (LinearMap.ker q) I
    constructor
    intro x y
    apply ek.symm.injective
    exact htensorK.elim _ _
  have hKtop : I • (⊤ : Submodule R (LinearMap.ker q)) = ⊤ :=
    (Submodule.Quotient.subsingleton_iff.mp hKquot)
  have hKsub : Subsingleton (LinearMap.ker q) :=
    Formalization.Books.Algebra.Unit20.nakayama_part_nine I hKtop hI
  have hqinj : Function.Injective q := by
    intro x y hxy
    have hdiff : q (x - y) = 0 := by
      rw [map_sub, hxy, sub_self]
    have hk : (⟨x - y, hdiff⟩ : LinearMap.ker q) = 0 :=
      Subsingleton.elim _ _
    have hzero : x - y = 0 := congrArg Subtype.val hk
    exact sub_eq_zero.mp hzero
  letI : Module.Projective R (P : Type u) := hP
  exact Module.Projective.of_equiv'
    (LinearEquiv.ofBijective q ⟨hqinj, hqsurj⟩)

/-- Projectivity modulo two ideals with zero intersection implies
projectivity over the original ring. -/
theorem projective_of_projective_quotients_of_inf_eq_bot
    {R : Type u} [CommRing R] (I J : Ideal R) (M : ModuleCat.{u} R)
    (hIJ : I ⊓ J = ⊥)
    (hI : Module.Projective (R ⧸ I)
      (M ⧸ (I • (⊤ : Submodule R M))))
    (hJ : Module.Projective (R ⧸ J)
      (M ⧸ (J • (⊤ : Submodule R M)))) :
    Module.Projective R M := by
  sorry

end Formalization.Books.Algebra.Unit77
