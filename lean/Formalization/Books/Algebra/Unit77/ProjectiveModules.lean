import Formalization.Books.Algebra.Unit03.BasicNotions
import Formalization.Books.Algebra.Unit10.InternalHom
import Formalization.Books.Algebra.Unit71.ExtGroups
import Mathlib.Algebra.Module.FinitePresentation
import Mathlib.Algebra.Module.Projective
import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.CategoryTheory.Abelian.Projective.Dimension
import Mathlib.RingTheory.FiniteLength
import Mathlib.RingTheory.Flat.Basic
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
  sorry

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
  sorry

/-- A flat module whose reduction modulo a nilpotent ideal is projective is
projective. -/
theorem projective_of_flat_of_isNilpotent_of_quotient_projective
    {R : Type u} [CommRing R] (I : Ideal R) (M : ModuleCat.{u} R)
    (hI : IsNilpotent I)
    [Module.Flat R M]
    (hMbar : Module.Projective (R ⧸ I)
      (M ⧸ (I • (⊤ : Submodule R M)))) :
    Module.Projective R M := by
  sorry

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
