import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.Algebra.Homology.Homotopy
import Mathlib.Algebra.Homology.HomotopyCategory
import Mathlib.Algebra.Homology.HomotopyCategory.Shift
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.Algebra.Module.LocalizedModule.Basic
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Localization.Basic
import Mathlib.RingTheory.RingHom.Flat

/-!
# More on Algebra, Chapter 96: An operator introduced by Berthelot and Ogus

This file records the definitions and theorem interfaces in the section on
the Berthelot--Ogus `eta` operator.  The powers of `f` are represented by
their canonical images in the localization of a module, and complexes use
Mathlib's `CochainComplex` and homotopy-category constructions.
-/

noncomputable section

open CategoryTheory
open CategoryTheory.Preadditive
open Module
open scoped TensorProduct

universe u v w

namespace Formalization.Books.MoreAlgebra.Unit96

/-! ## `f`-torsion-free modules -/

abbrev ModuleComplex (R : Type u) [CommRing R] :=
  CochainComplex (ModuleCat.{u} R) ℤ

/-- The `f`-torsion submodule of an `R`-module. -/
def fTorsionSubmodule {R M : Type u} [CommRing R]
    [AddCommGroup M] [Module R M] (f : R) : Submodule R M where
  carrier := {x | f • x = 0}
  zero_mem' := by simp
  add_mem' := by
    intro x y hx hy
    simp only [Set.mem_ofPred_eq] at hx hy ⊢
    rw [smul_add, hx, hy, add_zero]
  smul_mem' := by
    intro r x hx
    simp only [Set.mem_ofPred_eq] at hx ⊢
    simpa [smul_smul, mul_comm] using congrArg (fun y => r • y) hx

/-- The submodule killed by a positive power of `f`. -/
def fPowerTorsionSubmodule {R M : Type u} [CommRing R]
    [AddCommGroup M] [Module R M] (f : R) (n : ℕ) : Submodule R M where
  carrier := {x | f ^ n • x = 0}
  zero_mem' := by simp
  add_mem' := by
    intro x y hx hy
    simp only [Set.mem_ofPred_eq] at hx hy ⊢
    rw [smul_add, hx, hy, add_zero]
  smul_mem' := by
    intro r x hx
    simp only [Set.mem_ofPred_eq] at hx ⊢
    simpa [smul_smul, mul_comm] using congrArg (fun y => r • y) hx

/-- The source's notion of an `f`-torsion-free module. -/
def IsFTorsionFree {R : Type u} [CommRing R]
    (f : R) (M : Type u) [AddCommGroup M] [Module R M] : Prop :=
  ∀ ⦃x : M⦄, f • x = 0 → x = 0

theorem mem_fTorsionSubmodule_iff {R M : Type u} [CommRing R]
    [AddCommGroup M] [Module R M] (f : R) (x : M) :
    x ∈ fTorsionSubmodule f ↔ f • x = 0 := by
  rfl

theorem isFTorsionFree_iff_fTorsionSubmodule_eq_bot
    {R M : Type u} [CommRing R] [AddCommGroup M] [Module R M]
    (f : R) :
    IsFTorsionFree f M ↔ fTorsionSubmodule (M := M) f = ⊥ := by
  sorry

theorem f_torsion_free_criteria
    {R M : Type u} [CommRing R] [AddCommGroup M] [Module R M]
    (f : R) (hf : IsRegular f) :
    List.TFAE
      [IsFTorsionFree f M,
       fTorsionSubmodule (M := M) f = ⊥,
       (∀ n : ℕ, 0 < n → fPowerTorsionSubmodule (M := M) f n = ⊥),
       Function.Injective (LocalizedModule.mkLinearMap
         (Submonoid.powers f) M)] := by
  sorry

/-! ## Powers in the localization and the eta complex -/

local notation "S[" f "]" => Submonoid.powers f

/-- The image of `f^i M` in `M[f⁻¹]`, for an integer `i`.

The localization API is only a semiring API, so negative powers are written
using the canonical numerator/denominator presentation rather than `zpow`.
-/
def localizationPower {R : Type u} [CommRing R] (f : R) : ℤ → Localization S[f]
  | Int.ofNat n => algebraMap R (Localization S[f]) (f ^ n)
  | Int.negSucc n =>
      IsLocalization.mk' (Localization S[f]) 1
        ⟨f ^ (n + 1), (Submonoid.mem_powers_iff _ _).2 ⟨n + 1, rfl⟩⟩

def fPowerSubmodule {R : Type u} [CommRing R]
    (f : R) (M : Type u) [AddCommGroup M] [Module R M] (i : ℤ) :
    Submodule R (LocalizedModule S[f] M) := by
  letI : SMul (Localization S[f]) (LocalizedModule S[f] M) :=
    LocalizedModule.smulOfIsLocalization (Localization S[f])
  let a : Localization S[f] := localizationPower f i
  exact Submodule.span R (Set.range fun m : M =>
    a • LocalizedModule.mkLinearMap S[f] M m)

theorem mem_fPowerSubmodule_iff {R M : Type u} [CommRing R]
    [AddCommGroup M] [Module R M] (f : R) (i : ℤ) (x : LocalizedModule S[f] M) :
    x ∈ fPowerSubmodule f M i ↔
      ∃ m : M,
        x = localizationPower f i •
          LocalizedModule.mkLinearMap S[f] M m := by
  sorry

theorem fPowerSubmodule_isomorphic {R M : Type u} [CommRing R]
    [AddCommGroup M] [Module R M] (f : R) (hf : IsRegular f)
    (hM : IsFTorsionFree f M) (i : ℤ) :
    Nonempty ((fPowerSubmodule f M i : Type u) ≃+ M) := by
  sorry

/-- The localization of an `R`-linear map. -/
noncomputable def localizedLinearMap {R M N : Type u} [CommRing R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (f : R) (g : M →ₗ[R] N) :
    LocalizedModule S[f] M →ₗ[R] LocalizedModule S[f] N :=
  IsLocalizedModule.map S[f] (LocalizedModule.mkLinearMap S[f] M)
    (LocalizedModule.mkLinearMap S[f] N) g

@[simp]
theorem localizedLinearMap_mk {R M N : Type u} [CommRing R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (f : R) (g : M →ₗ[R] N) (x : M) :
    localizedLinearMap f g (LocalizedModule.mkLinearMap S[f] M x) =
      LocalizedModule.mkLinearMap S[f] N (g x) := by
  sorry

theorem localizedLinearMap_comp {R M N P : Type u} [CommRing R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    [AddCommGroup P] [Module R P] (f : R)
    (g : M →ₗ[R] N) (h : N →ₗ[R] P) :
    localizedLinearMap f (h.comp g) =
      (localizedLinearMap f h).comp (localizedLinearMap f g) := by
  sorry

/-- The degree-`i` term of `η_f M`, as a submodule of the localized term. -/
def etaSubmodule {R : Type u} [CommRing R]
    (f : R) (M : ModuleComplex R) (i : ℤ) :
    Submodule R (LocalizedModule S[f] (M.X i : Type u)) where
  carrier := {x |
    x ∈ fPowerSubmodule f (M.X i : Type u) i ∧
      localizedLinearMap f (M.d i (i + 1)).hom x ∈
        fPowerSubmodule f (M.X (i + 1) : Type u) (i + 1)}
  zero_mem' := by simp
  add_mem' := by
    intro x y hx hy
    have h₁ := (fPowerSubmodule f (M.X i : Type u) i).add_mem hx.1 hy.1
    have h₂ := (fPowerSubmodule f (M.X (i + 1) : Type u) (i + 1)).add_mem hx.2 hy.2
    exact ⟨h₁, by simpa using h₂⟩
  smul_mem' := by
    intro r x hx
    have h₁ := (fPowerSubmodule f (M.X i : Type u) i).smul_mem r hx.1
    have h₂ := (fPowerSubmodule f (M.X (i + 1) : Type u) (i + 1)).smul_mem r hx.2
    exact ⟨h₁, by simpa using h₂⟩

theorem mem_etaSubmodule_iff {R : Type u} [CommRing R]
    (f : R) (M : ModuleComplex R) (i : ℤ)
    (x : LocalizedModule S[f] (M.X i : Type u)) :
    x ∈ etaSubmodule f M i ↔
      x ∈ fPowerSubmodule f (M.X i : Type u) i ∧
        localizedLinearMap f (M.d i (i + 1)).hom x ∈
          fPowerSubmodule f (M.X (i + 1) : Type u) (i + 1) := by
  rfl

theorem eta_differential_target {R : Type u} [CommRing R]
    (f : R) (M : ModuleComplex R) (i : ℤ)
    (x : etaSubmodule f M i) :
    localizedLinearMap f (M.d (i + 1) ((i + 1) + 1)).hom
        (localizedLinearMap f (M.d i (i + 1)).hom x) ∈
      fPowerSubmodule f (M.X ((i + 1) + 1) : Type u) ((i + 1) + 1) := by
  sorry

noncomputable def etaDifferential {R : Type u} [CommRing R]
    (f : R) (M : ModuleComplex R) (i : ℤ) :
    etaSubmodule f M i →ₗ[R] etaSubmodule f M (i + 1) := by
  let d := localizedLinearMap f (M.d i (i + 1)).hom
  exact
    { toFun := fun x =>
        ⟨d x,
          ⟨((mem_etaSubmodule_iff f M i x.1).mp x.2).2,
            by
              change localizedLinearMap f (M.d (i + 1) ((i + 1) + 1)).hom
                  (localizedLinearMap f (M.d i (i + 1)).hom x) ∈ _
              exact eta_differential_target f M i x⟩⟩
      map_add' := by
        intro x y
        apply Subtype.ext
        simp
      map_smul' := by
        intro r x
        apply Subtype.ext
        simp }

theorem eta_differential_squared {R : Type u} [CommRing R]
    (f : R) (M : ModuleComplex R) (i : ℤ) :
    ModuleCat.ofHom (etaDifferential f M i) ≫
        ModuleCat.ofHom (etaDifferential f M (i + 1)) = 0 := by
  sorry

/-- The Berthelot--Ogus operator on a cochain complex. -/
noncomputable def eta {R : Type u} [CommRing R]
    (f : R) (M : ModuleComplex R) : ModuleComplex R :=
  CochainComplex.of
    (fun i => ModuleCat.of R (etaSubmodule f M i))
    (fun i => ModuleCat.ofHom (etaDifferential f M i))
    (by intro i; exact eta_differential_squared f M i)

theorem eta_X {R : Type u} [CommRing R] (f : R) (M : ModuleComplex R) (i : ℤ) :
    (eta f M).X i = ModuleCat.of R (etaSubmodule f M i) := rfl

theorem eta_d {R : Type u} [CommRing R] (f : R) (M : ModuleComplex R) (i : ℤ) :
    (eta f M).d i (i + 1) = ModuleCat.ofHom (etaDifferential f M i) := by
  simp [eta]

def ComplexIsFTorsionFree {R : Type u} [CommRing R]
    (f : R) (M : ModuleComplex R) : Prop :=
  ∀ i : ℤ, IsFTorsionFree f (M.X i : Type u)

theorem eta_complex_isFTorsionFree {R : Type u} [CommRing R]
    (f : R) (hf : IsRegular f) (M : ModuleComplex R)
    (hM : ComplexIsFTorsionFree f M) :
    ComplexIsFTorsionFree f (eta f M) := by
  sorry

/-! ## Functoriality and the homotopy-category statement -/

theorem eta_on_maps_exists {R : Type u} [CommRing R]
    (f : R) {M N : ModuleComplex R} (a : M ⟶ N) :
    Nonempty (eta f M ⟶ eta f N) := by
  sorry

noncomputable def etaMap {R : Type u} [CommRing R]
    (f : R) {M N : ModuleComplex R} (a : M ⟶ N) :
    eta f M ⟶ eta f N :=
  Classical.choice (eta_on_maps_exists f a)

theorem eta_preserves_homotopies {R : Type u} [CommRing R]
    (f : R) {M N : ModuleComplex R} {a b : M ⟶ N}
    (h : Homotopy a b) :
    Nonempty (Homotopy (etaMap f a) (etaMap f b)) := by
  sorry

theorem eta_homotopy_functor_exists {R : Type u} [CommRing R]
    (f : R) :
    Nonempty (HomotopyCategory (ModuleCat.{u} R) (ComplexShape.up ℤ) ⥤
      HomotopyCategory (ModuleCat.{u} R) (ComplexShape.up ℤ)) := by
  sorry

structure EtaEndofunctorData {R : Type u} [CommRing R] (f : R) where
  functor : ModuleComplex R ⥤ ModuleComplex R
  onObjects : ∀ M : ModuleComplex R, Nonempty (functor.obj M ≅ eta f M)
  onMaps : ∀ {M N : ModuleComplex R} (a : M ⟶ N),
    ∃ eM : functor.obj M ≅ eta f M, ∃ eN : functor.obj N ≅ eta f N,
      eM.hom ≫ etaMap f a = functor.map a ≫ eN.hom

theorem eta_endofunctor_exists {R : Type u} [CommRing R] (f : R) :
    Nonempty (EtaEndofunctorData f) := by
  sorry

/-! ## The source's main properties of `η_f` -/

theorem eta_quasiIso {R : Type u} [CommRing R]
    (f : R) (hf : IsRegular f) {M N : ModuleComplex R}
    (_hM : ComplexIsFTorsionFree f M) (_hN : ComplexIsFTorsionFree f N)
    (a : M ⟶ N) :
    QuasiIso a → ∃ b : eta f M ⟶ eta f N, QuasiIso b := by
  sorry

theorem eta_quasiIso_induced {R : Type u} [CommRing R]
    (f : R) (hf : IsRegular f) {M N : ModuleComplex R}
    (_hM : ComplexIsFTorsionFree f M) (_hN : ComplexIsFTorsionFree f N)
    (a : M ⟶ N) (ha : QuasiIso a) : QuasiIso (etaMap f a) := by
  sorry

/-! The elementary cycle, boundary, and cohomology modules used below. -/

def cycles {R : Type u} [CommRing R] (M : ModuleComplex R) (i : ℤ) :
    Submodule R (M.X i : Type u) :=
  LinearMap.ker (M.d i (i + 1)).hom

def boundaries {R : Type u} [CommRing R] (M : ModuleComplex R) (i : ℤ) :
    Submodule R (M.X i : Type u) :=
  LinearMap.range (M.d (i - 1) i).hom

def boundariesInCycles {R : Type u} [CommRing R] (M : ModuleComplex R) (i : ℤ) :
    Submodule R (cycles M i) :=
  Submodule.comap (cycles M i).subtype (boundaries M i)

/-- Cohomology represented as cycles modulo boundaries. -/
abbrev cohomologyModule {R : Type u} [CommRing R] (M : ModuleComplex R) (i : ℤ) : Type u :=
  cycles M i ⧸ boundariesInCycles M i

theorem boundaries_le_cycles {R : Type u} [CommRing R]
    (M : ModuleComplex R) (i : ℤ) :
    boundaries M i ≤ cycles M i := by
  sorry

theorem eta_first_property {R : Type u} [CommRing R]
    (f : R) (hf : IsRegular f) (M : ModuleComplex R)
    (hM : ComplexIsFTorsionFree f M) (i : ℤ) :
    Nonempty ((cohomologyModule M i ⧸
      fTorsionSubmodule (M := cohomologyModule M i) f) ≃+
      cohomologyModule (eta f M) i) := by
  sorry

noncomputable def etaFirstEquiv {R : Type u} [CommRing R]
    (f : R) (hf : IsRegular f) (M : ModuleComplex R)
    (hM : ComplexIsFTorsionFree f M) (i : ℤ) :
    (cohomologyModule M i ⧸
      fTorsionSubmodule (M := cohomologyModule M i) f) ≃+
      cohomologyModule (eta f M) i :=
  Classical.choice (eta_first_property f hf M hM i)

theorem eta_shift_compatibility {R : Type u} [CommRing R]
    (f : R) (M : ModuleComplex R) :
    Nonempty
      (eta f ((CochainComplex.shiftFunctor (ModuleCat R) 1).obj M) ≅
        (CochainComplex.shiftFunctor (ModuleCat R) 1).obj (eta f M)) := by
  sorry

structure EtaNonDistinguishedWitness {R : Type u} [CommRing R]
    (f : R) where
  regular : IsRegular f
  first : ModuleComplex R
  second : ModuleComplex R
  third : ModuleComplex R
  map : first ⟶ second
  thirdIsCone : Nonempty (third ≅ CochainComplex.mappingCone map)
  thirdAfterEtaAcyclic : ∀ i : ℤ,
    Subsingleton (cohomologyModule (eta f third) i)
  firstAfterEtaNotAnIsomorphism :
    ¬ IsUnit f → ¬ ∃ e : eta f first ≅ eta f second, e.hom = etaMap f map

theorem eta_not_distinguished_example {R : Type u} [CommRing R]
    (f : R) (hf : IsRegular f) (hfu : ¬ IsUnit f) :
    Nonempty (EtaNonDistinguishedWitness f) := by
  sorry

/-! ## The derived operator `Lη_f` -/

abbrev DerivedModule (R : Type u) [CommRing R]
    [HasDerivedCategory (ModuleCat.{u} R)] :=
  DerivedCategory (ModuleCat.{u} R)

noncomputable abbrev derivedQuotient (R : Type u) [CommRing R]
    [HasDerivedCategory (ModuleCat.{u} R)] :
    ModuleComplex R ⥤ DerivedModule R := DerivedCategory.Q

structure LetaFunctorData (R : Type u) [CommRing R]
    [HasDerivedCategory (ModuleCat.{u} R)] (f : R) where
  functor : DerivedModule R ⥤ DerivedModule R
  additive : functor.Additive
  represented : ∀ (M : ModuleComplex R),
    ComplexIsFTorsionFree f M →
      Nonempty (functor.obj ((derivedQuotient R).obj M) ≅
        (derivedQuotient R).obj (eta f M))
  represented_morphism : ∀ {M N : ModuleComplex R}
    (_hM : ComplexIsFTorsionFree f M) (_hN : ComplexIsFTorsionFree f N)
    (a : M ⟶ N),
    ∃ eM : functor.obj ((derivedQuotient R).obj M) ≅
        (derivedQuotient R).obj (eta f M),
      ∃ eN : functor.obj ((derivedQuotient R).obj N) ≅
        (derivedQuotient R).obj (eta f N),
        eM.hom ≫ (derivedQuotient R).map (etaMap f a) =
          functor.map ((derivedQuotient R).map a) ≫ eN.hom

theorem letaFunctorData_exists {R : Type u} [CommRing R]
    [HasDerivedCategory (ModuleCat.{u} R)] (f : R) (hf : IsRegular f) :
    Nonempty (LetaFunctorData R f) := by
  sorry

noncomputable def Leta {R : Type u} [CommRing R]
    [HasDerivedCategory (ModuleCat.{u} R)] (f : R) (hf : IsRegular f) :
    DerivedModule R ⥤ DerivedModule R :=
  (Classical.choice (letaFunctorData_exists f hf)).functor

instance leta_additive {R : Type u} [CommRing R]
    [HasDerivedCategory (ModuleCat.{u} R)] (f : R) (hf : IsRegular f) :
    (Leta f hf).Additive :=
  (Classical.choice (letaFunctorData_exists f hf)).additive

theorem Leta_on_fTorsionFree {R : Type u} [CommRing R]
    [HasDerivedCategory (ModuleCat.{u} R)] (f : R) (hf : IsRegular f)
    (M : ModuleComplex R) (hM : ComplexIsFTorsionFree f M) :
    Nonempty ((Leta f hf).obj ((derivedQuotient R).obj M) ≅
      (derivedQuotient R).obj (eta f M)) := by
  exact (Classical.choice (letaFunctorData_exists f hf)).represented M hM

/-! ## Bockstein operators and reduction modulo `f` -/

abbrev modF (R : Type u) [CommRing R] (f : R) := R ⧸ Ideal.span ({f} : Set R)

def fMultipleSubmodule {R M : Type u} [CommRing R]
    [AddCommGroup M] [Module R M] (f : R) : Submodule R M where
  carrier := {x | ∃ y : M, x = f • y}
  zero_mem' := ⟨0, by simp⟩
  add_mem' := by
    intro x y hx hy
    rcases hx with ⟨x, rfl⟩
    rcases hy with ⟨y, rfl⟩
    exact ⟨x + y, by rw [smul_add]⟩
  smul_mem' := by
    intro r x hx
    rcases hx with ⟨x, rfl⟩
    exact ⟨r • x, by simp [smul_smul, mul_comm]⟩

abbrev fGradedTerm {R : Type u} [CommRing R]
    (f : R) (i : ℤ) : Type u :=
  (fPowerSubmodule f R i) ⧸
    Submodule.comap (fPowerSubmodule f R i).subtype
      (fPowerSubmodule f R (i + 1))

theorem tensorComplex_d_squared {R : Type u} [CommRing R]
    (M : ModuleComplex R) (P : Type u) [AddCommGroup P] [Module R P]
    (i : ℤ) :
    ModuleCat.ofHom ((M.d i (i + 1)).hom.rTensor P) ≫
        ModuleCat.ofHom ((M.d (i + 1) ((i + 1) + 1)).hom.rTensor P) = 0 := by
  sorry

noncomputable def tensorComplex {R : Type u} [CommRing R]
    (M : ModuleComplex R) (P : Type u) [AddCommGroup P] [Module R P] :
    ModuleComplex R :=
  CochainComplex.of
    (fun i => ModuleCat.of R ((M.X i : Type u) ⊗[R] P))
    (fun i => ModuleCat.ofHom ((M.d i (i + 1)).hom.rTensor P))
    (by intro i; exact tensorComplex_d_squared M P i)

abbrev gradedTensorComplex {R : Type u} [CommRing R]
    (f : R) (M : ModuleComplex R) (p : ℤ) : ModuleComplex R :=
  tensorComplex M (fGradedTerm f p : Type u)

abbrev filteredTensorComplex {R : Type u} [CommRing R]
    (f : R) (M : ModuleComplex R) (p : ℤ) : ModuleComplex R :=
  tensorComplex M (fPowerSubmodule f R p : Type u)

abbrev bocksteinTerm {R : Type u} [CommRing R]
    (f : R) (M : ModuleComplex R) (i : ℤ) : Type u :=
  cohomologyModule (gradedTensorComplex f M i) i

abbrev filteredCohomology {R : Type u} [CommRing R]
    (f : R) (M : ModuleComplex R) (p j : ℤ) : Type u :=
  cohomologyModule (filteredTensorComplex f M p) j

abbrev twoStepGradedTerm {R : Type u} [CommRing R]
    (f : R) (p : ℤ) : Type u :=
  (fPowerSubmodule f R p) ⧸
    Submodule.comap (fPowerSubmodule f R p).subtype
      (fPowerSubmodule f R (p + 2))

abbrev twoStepTensorComplex {R : Type u} [CommRing R]
    (f : R) (M : ModuleComplex R) (p : ℤ) : ModuleComplex R :=
  tensorComplex M (twoStepGradedTerm f p : Type u)

structure BocksteinShortExactData {R : Type u} [CommRing R]
    (f : R) (M : ModuleComplex R) (i : ℤ) where
  topLeft : filteredTensorComplex f M (i + 1) ⟶ filteredTensorComplex f M i
  topRight : filteredTensorComplex f M i ⟶ gradedTensorComplex f M i
  bottomLeft : gradedTensorComplex f M (i + 1) ⟶ twoStepTensorComplex f M i
  bottomRight : twoStepTensorComplex f M i ⟶ gradedTensorComplex f M i
  verticalLeft : filteredTensorComplex f M (i + 1) ⟶
    gradedTensorComplex f M (i + 1)
  verticalMiddle : filteredTensorComplex f M i ⟶ twoStepTensorComplex f M i
  verticalRight : gradedTensorComplex f M i ⟶ gradedTensorComplex f M i
  topExact : ∀ j : ℤ, Function.Exact (topLeft.f j).hom (topRight.f j).hom
  bottomExact : ∀ j : ℤ,
    Function.Exact (bottomLeft.f j).hom (bottomRight.f j).hom
  topLeft_injective : ∀ j : ℤ, Function.Injective (topLeft.f j).hom
  topRight_surjective : ∀ j : ℤ, Function.Surjective (topRight.f j).hom
  bottomLeft_injective : ∀ j : ℤ, Function.Injective (bottomLeft.f j).hom
  bottomRight_surjective : ∀ j : ℤ, Function.Surjective (bottomRight.f j).hom
  left_comm : topLeft ≫ verticalMiddle = verticalLeft ≫ bottomLeft
  right_comm : topRight ≫ verticalRight = verticalMiddle ≫ bottomRight

theorem bockstein_short_exact {R : Type u} [CommRing R]
    (f : R) (hf : IsRegular f) (M : ModuleComplex R)
    (hM : ComplexIsFTorsionFree f M) (i : ℤ) :
    Nonempty (BocksteinShortExactData f M i) := by
  sorry

abbrev etaReductionTerm {R : Type u} [CommRing R]
    (f : R) (M : ModuleComplex R) (i : ℤ) : Type u :=
    (etaSubmodule f M i) ⧸ fMultipleSubmodule f
    (M := etaSubmodule f M i)

abbrev reductionTerm {R : Type u} [CommRing R]
    (f : R) (M : ModuleComplex R) (i : ℤ) : Type u :=
  (M.X i : Type u) ⧸ fMultipleSubmodule f
    (M := (M.X i : Type u))

theorem fMultipleSubmodule_d_le {R M N : Type u} [CommRing R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (f : R) (d : M →ₗ[R] N) :
    fMultipleSubmodule (M := M) f ≤
      LinearMap.ker ((fMultipleSubmodule (M := N) f).mkQ.comp d) := by
  sorry

noncomputable def reductionDifferential {R : Type u} [CommRing R]
    (f : R) (M : ModuleComplex R) (i : ℤ) :
    reductionTerm f M i →ₗ[R] reductionTerm f M (i + 1) :=
  (fMultipleSubmodule (M := (M.X i : Type u)) f).liftQ
    ((fMultipleSubmodule (M := (M.X (i + 1) : Type u)) f).mkQ.comp
      (M.d i (i + 1)).hom)
    (fMultipleSubmodule_d_le f (M.d i (i + 1)).hom)

theorem reduction_d_squared {R : Type u} [CommRing R]
    (f : R) (M : ModuleComplex R) (i : ℤ) :
    ModuleCat.ofHom (reductionDifferential f M i) ≫
        ModuleCat.ofHom (reductionDifferential f M (i + 1)) = 0 := by
  sorry

noncomputable def reductionComplex {R : Type u} [CommRing R]
    (f : R) (M : ModuleComplex R) : ModuleComplex R :=
  CochainComplex.of
    (fun i => ModuleCat.of R (reductionTerm f M i))
    (fun i => ModuleCat.ofHom (reductionDifferential f M i))
    (by intro i; exact reduction_d_squared f M i)

abbrev moduleGradedTerm {R : Type u} [CommRing R]
    (f : R) (M : ModuleComplex R) (i : ℤ) : Type u :=
  (fPowerSubmodule f (M.X i : Type u) i) ⧸
    Submodule.comap (fPowerSubmodule f (M.X i : Type u) i).subtype
      (fPowerSubmodule f (M.X i : Type u) (i + 1))

theorem etaReductionMap_exists {R : Type u} [CommRing R]
    (f : R) (hf : IsRegular f) (M : ModuleComplex R)
    (hM : ComplexIsFTorsionFree f M) (i : ℤ) :
    Nonempty (etaReductionTerm f M i →ₗ[R]
      moduleGradedTerm f M i × moduleGradedTerm f M (i + 1)) := by
  sorry

noncomputable def etaReductionMap {R : Type u} [CommRing R]
    (f : R) (hf : IsRegular f) (M : ModuleComplex R)
    (hM : ComplexIsFTorsionFree f M) (i : ℤ) :
    etaReductionTerm f M i →ₗ[R]
      moduleGradedTerm f M i × moduleGradedTerm f M (i + 1) :=
  Classical.choice (etaReductionMap_exists f hf M hM i)

abbrev reducedBoundaries {R : Type u} [CommRing R]
    (f : R) (M : ModuleComplex R) (i : ℤ) :
    Submodule R (reductionTerm f M i) :=
  boundaries (reductionComplex f M) i

abbrev reducedCycles {R : Type u} [CommRing R]
    (f : R) (M : ModuleComplex R) (i : ℤ) :
    Submodule R (reductionTerm f M i) :=
  cycles (reductionComplex f M) i

structure EtaBZData {R : Type u} [CommRing R]
    (f : R) (M : ModuleComplex R) (i : ℤ) where
  topLeft : (reducedBoundaries f M (i + 1) : Type u) →ₗ[R]
    (reducedBoundaries f M (i + 1) : Type u) ×
      (reducedBoundaries f M i : Type u)
  topRight : ((reducedBoundaries f M (i + 1) : Type u) ×
      (reducedBoundaries f M i : Type u)) →ₗ[R]
    (reducedBoundaries f M i : Type u)
  lowerLeft : (reducedBoundaries f M (i + 1) : Type u) →ₗ[R]
    etaReductionTerm f M i
  lowerRight : etaReductionTerm f M i →ₗ[R]
    (reducedCycles f M i : Type u)
  middle : ((reducedBoundaries f M (i + 1) : Type u) ×
      (reducedBoundaries f M i : Type u)) →ₗ[R] etaReductionTerm f M i
  rightDown : (reducedBoundaries f M i : Type u) →ₗ[R]
    (reducedCycles f M i : Type u)
  topExact : Function.Exact topLeft topRight
  topLeft_injective : Function.Injective topLeft
  topRight_surjective : Function.Surjective topRight
  lowerExact : Function.Exact lowerLeft lowerRight
  lowerLeft_injective : Function.Injective lowerLeft
  lowerSurjective : Function.Surjective lowerRight
  left_comm : middle.comp topLeft = lowerLeft
  right_comm : lowerRight.comp middle = rightDown.comp topRight

theorem remark_eta_BZ {R : Type u} [CommRing R]
    (f : R) (hf : IsRegular f) (M : ModuleComplex R)
    (hM : ComplexIsFTorsionFree f M) (i : ℤ) :
    Nonempty (EtaBZData f M i) := by
  sorry

structure BocksteinData {R : Type u} [CommRing R]
    (f : R) (M : ModuleComplex R) where
  beta : ∀ i : ℤ, bocksteinTerm f M i →ₗ[R] bocksteinTerm f M (i + 1)
  beta_squared : ∀ i : ℤ,
    (beta (i + 1)).comp (beta i) = 0

structure BocksteinFactorizationData {R : Type u} [CommRing R]
    (f : R) (M : ModuleComplex R) (i : ℤ) where
  beta : bocksteinTerm f M i →ₗ[R] bocksteinTerm f M (i + 1)
  delta : bocksteinTerm f M i →ₗ[R] filteredCohomology f M (i + 1) (i + 1)
  reduction : filteredCohomology f M (i + 1) (i + 1) →ₗ[R]
    bocksteinTerm f M (i + 1)
  factorization : beta = reduction.comp delta

theorem bockstein_factorization {R : Type u} [CommRing R]
    (f : R) (hf : IsRegular f) (M : ModuleComplex R)
    (hM : ComplexIsFTorsionFree f M) (i : ℤ) :
    Nonempty (BocksteinFactorizationData f M i) := by
  sorry

noncomputable def bocksteinComplex {R : Type u} [CommRing R]
    (f : R) (M : ModuleComplex R) (d : BocksteinData f M) : ModuleComplex R :=
  CochainComplex.of
    (fun i => ModuleCat.of R
      (bocksteinTerm f M i))
    (fun i => ModuleCat.ofHom (d.beta i))
    (by
      intro i
      apply ModuleCat.hom_ext
      exact d.beta_squared i)

structure EtaSecondPropertyData {R : Type u} [CommRing R]
    (f : R) (M : ModuleComplex R) where
  bocksteinData : BocksteinData f M
  source : ModuleComplex R
  sourceTerm : ∀ i : ℤ, Nonempty
    ((source.X i : Type u) ≃+ etaReductionTerm f M i)
  comparison : source ⟶ bocksteinComplex f M bocksteinData
  comparison_quasiIso : QuasiIso comparison

theorem bocksteinData_exists {R : Type u} [CommRing R]
    (f : R) (M : ModuleComplex R) : Nonempty (BocksteinData f M) := by
  sorry

noncomputable def bockstein {R : Type u} [CommRing R]
    (f : R) (M : ModuleComplex R) (i : ℤ) :
    bocksteinTerm f M i →ₗ[R] bocksteinTerm f M (i + 1) :=
  (Classical.choice (bocksteinData_exists f M)).beta i

theorem bockstein_factorization_compat {R : Type u} [CommRing R]
    (f : R) (hf : IsRegular f) (M : ModuleComplex R)
    (hM : ComplexIsFTorsionFree f M) (i : ℤ) :
    ∃ d : BocksteinFactorizationData f M i, d.beta = bockstein f M i := by
  sorry

theorem bockstein_squared {R : Type u} [CommRing R]
    (f : R) (M : ModuleComplex R) (i : ℤ) :
    (bockstein f M (i + 1)).comp (bockstein f M i) = 0 := by
  exact (Classical.choice (bocksteinData_exists f M)).beta_squared i

theorem eta_second_property {R : Type u} [CommRing R]
    (f : R) (hf : IsRegular f) (M : ModuleComplex R)
    (hM : ComplexIsFTorsionFree f M) :
    Nonempty (EtaSecondPropertyData f M) := by
  sorry

def KernelReductionSurjective {R M N : Type u} [CommRing R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (f : R) (d : M →ₗ[R] N) : Prop :=
  ∀ x : M, (∃ y : N, d x = f • y) →
    ∃ z : M, d z = 0 ∧ ∃ y : M, x - z = f • y

theorem vanishing_beta_iff {R : Type u} [CommRing R]
    (f : R) (hf : IsRegular f) (M : ModuleComplex R)
    (_hM : ComplexIsFTorsionFree f M) (i : ℤ) :
    KernelReductionSurjective f (M.d i (i + 1)).hom ↔
      bockstein f M i = 0 := by
  sorry

theorem vanishing_beta_of_cohomology_torsion_free {R : Type u} [CommRing R]
    (f : R) (hf : IsRegular f) (M : ModuleComplex R)
    (_hM : ComplexIsFTorsionFree f M) (i : ℤ)
    (h : IsFTorsionFree f (cohomologyModule M (i + 1))) :
    bockstein f M i = 0 := by
  sorry

def directSumSubmodule {R Y Z : Type u} [CommRing R]
    [AddCommGroup Y] [Module R Y] [AddCommGroup Z] [Module R Z]
    (P : Submodule R Y) (Q : Submodule R Z) :
    Submodule R (Y × Z) where
  carrier := {x | x.1 ∈ P ∧ x.2 ∈ Q}
  zero_mem' := by simp
  add_mem' := by
    intro x y hx hy
    exact ⟨P.add_mem hx.1 hy.1, Q.add_mem hx.2 hy.2⟩
  smul_mem' := by
    intro r x hx
    exact ⟨P.smul_mem r hx.1, Q.smul_mem r hx.2⟩

def IsDirectSumImage {R X Y Z : Type u} [CommRing R]
    [AddCommGroup X] [Module R X] [AddCommGroup Y] [Module R Y]
    [AddCommGroup Z] [Module R Z] (s : X →ₗ[R] Y × Z) : Prop :=
  ∃ (P : Submodule R Y) (Q : Submodule R Z)
    (e : X ≃ₗ[R] directSumSubmodule P Q),
    ∀ x : X, s x = (directSumSubmodule P Q).subtype (e x)

theorem eta_vanishing_beta {R : Type u} [CommRing R]
    (f : R) (hf : IsRegular f) (M : ModuleComplex R) (i : ℤ)
    (hM : ComplexIsFTorsionFree f M)
    (h : KernelReductionSurjective f (M.d i (i + 1)).hom) :
    IsDirectSumImage (etaReductionMap f hf M hM i) := by
  sorry

theorem eta_third_property {R : Type u} [CommRing R]
    (f g : R) (hf : IsRegular f) (hg : IsRegular g) (M : ModuleComplex R)
    (hfg : ∀ i : ℤ, IsFTorsionFree (f * g) (M.X i : Type u)) :
    Nonempty (eta f (eta g M) ≅ eta (f * g) M) := by
  sorry

noncomputable abbrev scalarExtensionComplex {R S : Type u} [CommRing R] [CommRing S]
    (φ : R →+* S) (M : ModuleComplex R) : ModuleComplex S :=
  ((ModuleCat.extendScalars φ).mapHomologicalComplex (ComplexShape.up ℤ)).obj M

structure EtaFlatBaseChangeData {R S : Type u} [CommRing R] [CommRing S]
    [Algebra R S] (φ : R →+* S) (f : R) (g : S)
    (M : ModuleComplex R) where
  complex : ModuleComplex S
  complex_is_base_change : Nonempty (complex ≅ scalarExtensionComplex φ M)
  image_eq : g = φ f
  torsionFree : ComplexIsFTorsionFree g complex
  etaComplex : Nonempty
    (eta g complex ≅ scalarExtensionComplex φ (eta f M))
  etaTerm : ∀ i : ℤ, Nonempty
    (((eta g complex).X i : Type u) ≃+
      ((eta f M).X i : Type u) ⊗[R] S)

theorem eta_flat_base_change {R S : Type u} [CommRing R] [CommRing S]
    (f : R) (hf : IsRegular f) (φ : R →+* S) (g : S)
    (hφ : g = φ f) (hflat : RingHom.Flat φ) (hg : IsRegular g)
    (M : ModuleComplex R) (hM : ComplexIsFTorsionFree f M) :
    letI : Algebra R S := φ.toAlgebra
    Nonempty (EtaFlatBaseChangeData φ f g M) := by
  sorry

/-! Source-label aliases.  These keep the textbook references available to
downstream chapters while the declarations above expose the underlying data. -/

theorem lemma_eta_first_property {R : Type u} [CommRing R]
    (f : R) (hf : IsRegular f) (M : ModuleComplex R)
    (hM : ComplexIsFTorsionFree f M) (i : ℤ) :
    Nonempty ((cohomologyModule M i ⧸
      fTorsionSubmodule (M := cohomologyModule M i) f) ≃+
      cohomologyModule (eta f M) i) :=
  eta_first_property f hf M hM i

theorem lemma_eta_qis {R : Type u} [CommRing R]
    (f : R) (hf : IsRegular f) {M N : ModuleComplex R}
    (hM : ComplexIsFTorsionFree f M) (hN : ComplexIsFTorsionFree f N)
    (a : M ⟶ N) (ha : QuasiIso a) : QuasiIso (etaMap f a) :=
  eta_quasiIso_induced f hf hM hN a ha

theorem lemma_Leta {R : Type u} [CommRing R]
    [HasDerivedCategory (ModuleCat.{u} R)] (f : R) (hf : IsRegular f) :
    Nonempty (LetaFunctorData R f) :=
  letaFunctorData_exists f hf

theorem lemma_eta_second_property {R : Type u} [CommRing R]
    (f : R) (hf : IsRegular f) (M : ModuleComplex R)
    (hM : ComplexIsFTorsionFree f M) :
    Nonempty (EtaSecondPropertyData f M) :=
  eta_second_property f hf M hM

theorem lemma_vanishing_beta {R : Type u} [CommRing R]
    (f : R) (hf : IsRegular f) (M : ModuleComplex R)
    (hM : ComplexIsFTorsionFree f M) (i : ℤ) :
    KernelReductionSurjective f (M.d i (i + 1)).hom ↔
      bockstein f M i = 0 :=
  vanishing_beta_iff f hf M hM i

theorem lemma_eta_vanishing_beta {R : Type u} [CommRing R]
    (f : R) (hf : IsRegular f) (M : ModuleComplex R) (i : ℤ)
    (hM : ComplexIsFTorsionFree f M)
    (h : KernelReductionSurjective f (M.d i (i + 1)).hom) :
    IsDirectSumImage (etaReductionMap f hf M hM i) :=
  eta_vanishing_beta f hf M i hM h

theorem lemma_eta_third_property {R : Type u} [CommRing R]
    (f g : R) (hf : IsRegular f) (hg : IsRegular g) (M : ModuleComplex R)
    (hfg : ∀ i : ℤ, IsFTorsionFree (f * g) (M.X i : Type u)) :
    Nonempty (eta f (eta g M) ≅ eta (f * g) M) :=
  eta_third_property f g hf hg M hfg

theorem lemma_eta_flat_base_change {R S : Type u} [CommRing R] [CommRing S]
    (f : R) (hf : IsRegular f) (φ : R →+* S) (g : S)
    (hφ : g = φ f) (hflat : RingHom.Flat φ) (hg : IsRegular g)
    (M : ModuleComplex R) (hM : ComplexIsFTorsionFree f M) :
    letI : Algebra R S := φ.toAlgebra
    Nonempty (EtaFlatBaseChangeData φ f g M) :=
  eta_flat_base_change f hf φ g hφ hflat hg M hM

end Formalization.Books.MoreAlgebra.Unit96
