import Mathlib.Algebra.Category.ModuleCat.Products
import Mathlib.Algebra.Homology.Homotopy
import Mathlib.Algebra.Module.CharacterModule
import Mathlib.Algebra.Module.FinitePresentation
import Formalization.Books.MoreAlgebra.Unit72.HomComplexes

/-!
# Adequate Modules, Chapter 8: Pure extensions

This file records the definitions and theorem interfaces in the chapter's
section on pure extensions. The tensor criteria use Mathlib's canonical
`LinearMap.lTensor` and `LinearMap.rTensor`, and pure characters use
`CharacterModule`, whose codomain is the rational circle model of `ℚ ⧸ ℤ`.
-/

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open Formalization.Books.MoreAlgebra.Unit72

universe u

namespace Formalization.Books.Adequate.Unit08

variable {A : Type u} [CommRing A]

/-! ## Universal exactness and purity -/

/-- A short exact sequence of functions, including its two endpoint conditions. -/
def ExactShortSequence {X Y Z : Type u} [Zero Z]
    (f : X → Y) (g : Y → Z) : Prop :=
  Function.Injective f ∧ Function.Exact f g ∧ Function.Surjective g

/-- Tensoring a short sequence with every module preserves short exactness. -/
def UniversallyExactShort {K M N : Type u}
    [AddCommGroup K] [AddCommGroup M] [AddCommGroup N]
    [Module A K] [Module A M] [Module A N]
    (f : K →ₗ[A] M) (g : M →ₗ[A] N) : Prop :=
  ∀ (T : Type u) [AddCommGroup T] [Module A T],
    ExactShortSequence (f.lTensor T) (g.lTensor T)

/-- A map remains injective after tensoring with every module. -/
def UniversallyInjective {M N : Type u}
    [AddCommGroup M] [AddCommGroup N] [Module A M] [Module A N]
    (f : M →ₗ[A] N) : Prop :=
  ∀ (T : Type u) [AddCommGroup T] [Module A T],
    Function.Injective (f.lTensor T)

/-- The maps induced on `Hom(P, -)` by postcomposition. -/
abbrev homPostcompose {P X Y : Type u}
    [AddCommGroup P] [AddCommGroup X] [AddCommGroup Y]
    [Module A P] [Module A X] [Module A Y]
    (f : X →ₗ[A] Y) :
    (P →ₗ[A] X) →ₗ[A] (P →ₗ[A] Y) :=
  LinearMap.llcomp A P X Y f

/-- The maps induced on `Hom(-, I)` by precomposition. -/
abbrev homPrecompose {X Y I : Type u}
    [AddCommGroup X] [AddCommGroup Y] [AddCommGroup I]
    [Module A X] [Module A Y] [Module A I]
    (f : X →ₗ[A] Y) :
    (Y →ₗ[A] I) →ₗ[A] (X →ₗ[A] I) :=
  LinearMap.lcomp A I f

/-- Pure projectivity, expressed by exactness of `Hom(P, -)` on universally
exact short sequences. -/
def PureProjective (P : ModuleCat.{u} A) : Prop :=
  ∀ {K M N : Type u} [AddCommGroup K] [AddCommGroup M] [AddCommGroup N]
    [Module A K] [Module A M] [Module A N]
    (f : K →ₗ[A] M) (g : M →ₗ[A] N),
    UniversallyExactShort f g →
      ExactShortSequence
        (homPostcompose (A := A) (P := (P : Type u)) f)
        (homPostcompose (A := A) (P := (P : Type u)) g)

/-- Pure injectivity, expressed by exactness of `Hom(-, I)` on universally
exact short sequences. -/
def PureInjective (I : ModuleCat.{u} A) : Prop :=
  ∀ {K M N : Type u} [AddCommGroup K] [AddCommGroup M] [AddCommGroup N]
    [Module A K] [Module A M] [Module A N]
    (f : K →ₗ[A] M) (g : M →ₗ[A] N),
    UniversallyExactShort f g →
      ExactShortSequence
        (homPrecompose (A := A) (I := (I : Type u)) g)
        (homPrecompose (A := A) (I := (I : Type u)) f)

/-! ## Pure projectives -/

/-- A module is a direct summand of `Q` when the inclusion has a retraction. -/
def IsDirectSummand (P Q : ModuleCat.{u} A) : Prop :=
  ∃ (i : P ⟶ Q) (r : Q ⟶ P), i ≫ r = 𝟙 P

/-- The direct-summand condition appearing in the characterization of pure
projectives. The coproduct is Mathlib's canonical module-category direct sum.
-/
def IsSummandOfDirectSumOfFinitelyPresented (P : ModuleCat.{u} A) : Prop :=
  ∃ (ι : Type u) (F : ι → ModuleCat.{u} A),
    (∀ i, Module.FinitePresentation A (F i)) ∧
      IsDirectSummand P (∐ F)

theorem pureProjective_iff_summand_of_direct_sum_finitely_presented
    (P : ModuleCat.{u} A) :
    PureProjective P ↔ IsSummandOfDirectSumOfFinitelyPresented P := by
  sorry

theorem exists_pureProjective_cover (M : ModuleCat.{u} A) :
    ∃ (N P : ModuleCat.{u} A) (f : N ⟶ P) (g : P ⟶ M),
      UniversallyExactShort f.hom g.hom ∧ PureProjective P := by
  sorry

/-! ## Pure injectives and the character module -/

/-- Mathlib's character module, packaged as an object of `ModuleCat A`. -/
abbrev characterModule (M : ModuleCat.{u} A) : ModuleCat.{u} A :=
  ModuleCat.of A (CharacterModule (M : Type u))

/-- The evaluation map into the double character module. -/
def characterEvaluation (M : ModuleCat.{u} A) :
    (M : Type u) →ₗ[A] CharacterModule (CharacterModule (M : Type u)) :=
  { toFun := fun m =>
      { toFun := fun φ => φ m
        map_zero' := by
          change (0 : CharacterModule (M : Type u)) m = 0
          rfl
        map_add' := by
          intro φ ψ
          change φ m + ψ m = φ m + ψ m
          rfl }
    map_add' := by
      intro x y
      ext φ
      exact map_add φ x y
    map_smul' := by
      intro a x
      ext φ
      rfl }

/-- A linear map splits when it has a left inverse. -/
def SplitsLinearMap {X Y : Type u}
    [AddCommGroup X] [AddCommGroup Y] [Module A X] [Module A Y]
    (f : X →ₗ[A] Y) : Prop :=
  ∃ r : Y →ₗ[A] X, r.comp f = LinearMap.id

theorem pureInjective_characterModule (M : ModuleCat.{u} A) :
    PureInjective (characterModule M) := by
  sorry

theorem pureInjective_iff_characterEvaluation_splits (I : ModuleCat.{u} A) :
    PureInjective I ↔ SplitsLinearMap (characterEvaluation I) := by
  sorry

theorem exists_pureInjective_envelope (M : ModuleCat.{u} A) :
    ∃ (I N : ModuleCat.{u} A) (f : M ⟶ I) (g : I ⟶ N),
      UniversallyExactShort f.hom g.hom ∧ PureInjective I := by
  sorry

/-! ## Universal resolutions -/

/-- Universal exactness for an augmented cochain complex. The negative terms
are required to vanish so that the integer-indexed complex is the usual
nonnegative resolution from the source. -/
def UniversallyExactAugmentedCochain
    (M : ModuleCat.{u} A)
    (I : CochainComplex (ModuleCat.{u} A) ℤ)
    (ι : ModuleCat.of A M ⟶ I.X 0) : Prop :=
  (∀ n : ℤ, n < 0 → IsZero (I.X n)) ∧
  ∀ (T : Type u) [AddCommGroup T] [Module A T],
    Function.Injective (ι.hom.lTensor T) ∧
    Function.Exact (ι.hom.lTensor T) ((I.d 0 1).hom.lTensor T) ∧
    ∀ n : ℕ,
      Function.Exact ((I.d (n : ℤ) ((n + 1 : ℕ) : ℤ)).hom.lTensor T)
        ((I.d ((n + 1 : ℕ) : ℤ) ((n + 2 : ℕ) : ℤ)).hom.lTensor T)

/-- Universal exactness for an augmented chain complex. -/
def UniversallyExactAugmentedChain
    (M : ModuleCat.{u} A)
    (P : CochainComplex (ModuleCat.{u} A) ℤ)
    (ε : P.X 0 ⟶ ModuleCat.of A M) : Prop :=
  (∀ n : ℤ, 0 < n → IsZero (P.X n)) ∧
  ∀ (T : Type u) [AddCommGroup T] [Module A T],
    Function.Surjective (ε.hom.rTensor T) ∧
    Function.Exact ((P.d (-1) 0).hom.rTensor T) (ε.hom.rTensor T) ∧
    ∀ n : ℕ,
      Function.Exact
        ((P.d (-((n + 2 : ℕ) : ℤ)) (-((n + 1 : ℕ) : ℤ))).hom.rTensor T)
        ((P.d (-((n + 1 : ℕ) : ℤ)) (-((n : ℕ) : ℤ))).hom.rTensor T)

/-- A universally exact cochain resolution of a module. -/
structure UniversalCochainResolution (M : ModuleCat.{u} A) where
  complex : CochainComplex (ModuleCat.{u} A) ℤ
  augmentation : ModuleCat.of A M ⟶ complex.X 0
  exact : UniversallyExactAugmentedCochain M complex augmentation

/-- A universally exact chain resolution of a module. -/
structure UniversalChainResolution (M : ModuleCat.{u} A) where
  complex : CochainComplex (ModuleCat.{u} A) ℤ
  augmentation : complex.X 0 ⟶ ModuleCat.of A M
  exact : UniversallyExactAugmentedChain M complex augmentation

/-- A pure projective resolution `… → P₁ → P₀ → M → 0`. -/
structure PureProjectiveResolution (M : ModuleCat.{u} A)
    extends UniversalChainResolution M where
  pure_projective : ∀ n : ℕ, PureProjective (complex.X (-((n : ℕ) : ℤ)))

/-- A pure injective resolution `0 → M → I⁰ → I¹ → …`. -/
structure PureInjectiveResolution (M : ModuleCat.{u} A)
    extends UniversalCochainResolution M where
  pure_injective : ∀ n : ℕ, PureInjective (complex.X (n : ℤ))

/-! ## The splitting observation -/

/-- The source's kernel term for a differential in a module-valued complex. -/
abbrev differentialKernel (C : CochainComplex (ModuleCat.{u} A) ℤ) (n : ℤ) :
    ModuleCat.{u} A :=
  ModuleCat.of A (LinearMap.ker (C.d n (n + 1)).hom)

theorem universallyExact_image_map_universallyInjective
    {K M N : Type u} [AddCommGroup K] [AddCommGroup M] [AddCommGroup N]
    [Module A K] [Module A M] [Module A N]
    (f : K →ₗ[A] M) (g : M →ₗ[A] N)
    (h : UniversallyExactShort f g) :
    UniversallyInjective (Submodule.subtype (LinearMap.range g)) := by
  sorry

/-- A universally exact complex decomposes into the universally exact short
sequences formed by the kernels of its differentials. -/
theorem universallyExact_cochain_splits_into_short_sequences
    (C : CochainComplex (ModuleCat.{u} A) ℤ)
    (hC : ∀ (T : Type u) [AddCommGroup T] [Module A T] (n : ℤ),
      Function.Exact ((C.d (n - 1) n).hom.lTensor T)
        ((C.d n (n + 1)).hom.lTensor T)) :
    ∀ n : ℤ,
      ∃ (K : ModuleCat.{u} A)
        (ι : K ⟶ C.X n) (π : C.X n ⟶ differentialKernel C (n + 1)),
        Nonempty (K ≅ differentialKernel C n) ∧
          UniversallyExactShort ι.hom π.hom := by
  sorry

/-! ## Comparison and uniqueness of resolutions -/

theorem pureProjectiveResolution_exists (M : ModuleCat.{u} A) :
    Nonempty (PureProjectiveResolution M) := by
  sorry

theorem pureProjectiveResolution_lift
    {M N : ModuleCat.{u} A} (f : M ⟶ N)
    (P : PureProjectiveResolution M)
    (Q : UniversalChainResolution N) :
    ∃ α : P.complex ⟶ Q.complex,
      P.augmentation ≫ f = α.f 0 ≫ Q.augmentation := by
  sorry

theorem pureProjectiveResolution_lift_unique_up_to_homotopy
    {M N : ModuleCat.{u} A} (f : M ⟶ N)
    (P : PureProjectiveResolution M)
    (Q : UniversalChainResolution N)
    {α β : P.complex ⟶ Q.complex}
    (hα : P.augmentation ≫ f = α.f 0 ≫ Q.augmentation)
    (hβ : P.augmentation ≫ f = β.f 0 ≫ Q.augmentation) :
    Nonempty (Homotopy α β) := by
  sorry

theorem pureInjectiveResolution_exists (M : ModuleCat.{u} A) :
    Nonempty (PureInjectiveResolution M) := by
  sorry

theorem universalCochainResolution_lift_to_pureInjective
    {M N : ModuleCat.{u} A} (f : M ⟶ N)
    (P : UniversalCochainResolution M)
    (Q : PureInjectiveResolution N) :
    ∃ α : P.complex ⟶ Q.complex,
      P.augmentation ≫ α.f 0 = f ≫ Q.augmentation := by
  sorry

theorem universalCochainResolution_lift_unique_up_to_homotopy
    {M N : ModuleCat.{u} A} (f : M ⟶ N)
    (P : UniversalCochainResolution M)
    (Q : PureInjectiveResolution N)
    {α β : P.complex ⟶ Q.complex}
    (hα : P.augmentation ≫ α.f 0 = f ≫ Q.augmentation)
    (hβ : P.augmentation ≫ β.f 0 = f ≫ Q.augmentation) :
    Nonempty (Homotopy α β) := by
  sorry

/-! ## Pure extension modules -/

noncomputable def chosenPureInjectiveResolution (N : ModuleCat.{u} A) :
    PureInjectiveResolution N :=
  Classical.choice (pureInjectiveResolution_exists N)

/-- The pure extension module, computed from a chosen pure injective
resolution using the canonical module-valued Hom complex. -/
noncomputable abbrev PureExt
    (M N : ModuleCat.{u} A) (i : ℕ) : ModuleCat.{u} A :=
  (homComplex
      ((CochainComplex.singleFunctor (ModuleCat.{u} A) 0).obj M)
      (chosenPureInjectiveResolution N).complex).homology (i : ℤ)

theorem pureExt_independent_of_pureInjectiveResolution
    (M N : ModuleCat.{u} A) (R S : PureInjectiveResolution N) (i : ℕ) :
    Nonempty (
      (homComplex
          ((CochainComplex.singleFunctor (ModuleCat.{u} A) 0).obj M)
          R.complex).homology (i : ℤ) ≅
        (homComplex
          ((CochainComplex.singleFunctor (ModuleCat.{u} A) 0).obj M)
          S.complex).homology (i : ℤ)) := by
  sorry

/- The source warning is recorded here explicitly: ordinary exact sequences do
not supply the long pure-extension sequence; the tensor-universal hypothesis
in `UniversallyExactShort` is the required replacement. -/

theorem pureExt_zero_of_pureInjective
    (M N : ModuleCat.{u} A) (hN : PureInjective N) {i : ℕ} (hi : 0 < i) :
    IsZero (PureExt M N i) := by
  sorry

theorem pureExt_zero_of_pureProjective
    (M N : ModuleCat.{u} A) (hM : PureProjective M) {i : ℕ} (hi : 0 < i) :
    IsZero (PureExt M N i) := by
  sorry

theorem pureExt_zero_of_finitePresentation
    (M N : ModuleCat.{u} A)
    (hM : Module.FinitePresentation A (M : Type u)) {i : ℕ} (hi : 0 < i) :
    IsZero (PureExt M N i) := by
  sorry

/-- Pure extension computed from a pure projective resolution. -/
noncomputable abbrev PureExtViaProjective
    {M : ModuleCat.{u} A}
    (P : PureProjectiveResolution M) (N : ModuleCat.{u} A) (i : ℕ) :
    ModuleCat.{u} A :=
  (homComplex P.complex
    ((CochainComplex.singleFunctor (ModuleCat.{u} A) 0).obj N)).homology (i : ℤ)

theorem pureExt_iso_via_pureProjectiveResolution
    (M N : ModuleCat.{u} A) (P : PureProjectiveResolution M) (i : ℕ) :
    Nonempty (PureExt M N i ≅ PureExtViaProjective P N i) := by
  sorry

end Formalization.Books.Adequate.Unit08
