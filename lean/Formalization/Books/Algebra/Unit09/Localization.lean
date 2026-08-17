import Mathlib.Algebra.Category.ModuleCat.Localization
import Mathlib.Algebra.Colimit.Module
import Mathlib.Algebra.Group.Submonoid.Pointwise
import Mathlib.Algebra.Module.LocalizedModule.AtPrime
import Mathlib.Algebra.Module.LocalizedModule.Submodule
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import Mathlib.RingTheory.Localization.LocalizationLocalization
import Mathlib.RingTheory.Localization.Submodule

/-!
# Commutative Algebra, Chapter 9: Localization

This file formalizes the precise definitions and theorem interfaces in the
`Localization` section of `books/algebra.tex`.  The canonical Mathlib
localization constructions are used throughout: a multiplicative subset is a
`Submonoid`, ring localization is `Localization`, and module localization is
`LocalizedModule`.
-/

namespace Formalization.Books.Algebra.Unit09

open CategoryTheory
open CategoryTheory.Limits

universe u v

noncomputable section

/-! ## Multiplicative subsets and ring localizations -/

/-- A multiplicative subset, represented by Mathlib's canonical submonoid. -/
abbrev MultiplicativeSubset (R : Type u) [CommRing R] := Submonoid R

theorem multiplicativeSubset_one_mem {R : Type u} [CommRing R]
    (S : MultiplicativeSubset R) : (1 : R) ∈ S :=
  S.one_mem

theorem multiplicativeSubset_mul_mem {R : Type u} [CommRing R]
    (S : MultiplicativeSubset R) {s t : R} (hs : s ∈ S) (ht : t ∈ S) : s * t ∈ S :=
  S.mul_mem hs ht

/-- The equivalence relation on numerator-denominator pairs used by `Localization`. -/
abbrev localizationRelation {A : Type u} [CommRing A] (S : Submonoid A) :=
  Localization.r S

theorem localizationRelation_is_equivalence {A : Type u} [CommRing A]
    (S : Submonoid A) : IsEquiv _ (localizationRelation S) := by
  sorry

/- The source's cross-multiplication presentation of the canonical relation. -/
theorem localizationRelation_cross_multiplication {A : Type u} [CommRing A]
    (S : Submonoid A) (x y : A) (s t : S) :
    localizationRelation S (x, s) (y, t) ↔
      ∃ u : S, (x * (t : A) - y * (s : A)) * (u : A) = 0 := by
  sorry

/-- The localization of a commutative ring at a multiplicative subset. -/
abbrev localization {A : Type u} [CommRing A] (S : Submonoid A) := Localization S

/-- The fraction represented by a numerator and a denominator. -/
def localizationFraction {A : Type u} [CommRing A] (S : Submonoid A)
    (x : A) (s : S) : localization S :=
  Localization.mk x s

theorem localizationFraction_add {A : Type u} [CommRing A] (S : Submonoid A)
    (x y : A) (s t : S) :
    localizationFraction S x s + localizationFraction S y t =
      localizationFraction S (x * (t : A) + y * (s : A)) (s * t) := by
  sorry

theorem localizationFraction_mul {A : Type u} [CommRing A] (S : Submonoid A)
    (x y : A) (s t : S) :
    localizationFraction S x s * localizationFraction S y t =
      localizationFraction S (x * y) (s * t) := by
  sorry

/-- The canonical map from a ring to its localization. -/
def localizationMap {A : Type u} [CommRing A] (S : Submonoid A) :
    A →+* localization S :=
  algebraMap A (localization S)

theorem localizationMap_eq_fraction_one {A : Type u} [CommRing A] (S : Submonoid A)
    (x : A) : localizationMap S x = localizationFraction S x 1 := by
  rfl

theorem localizationMap_eq_zero_iff {A : Type u} [CommRing A] (S : Submonoid A)
    (x : A) : localizationMap S x = 0 ↔ ∃ s : S, (s : A) * x = 0 := by
  sorry

theorem localizationMap_injective_of_no_zero_divisors
    {A : Type u} [CommRing A] (S : Submonoid A)
    (hS : ∀ s : S, ∀ x : A, (s : A) * x = 0 → x = 0) :
    Function.Injective (localizationMap S) := by
  sorry

/-- The universal property of the localization, in the source's ring-hom form. -/
theorem localization_universal_property {A : Type u} [CommRing A]
    (S : Submonoid A) {B : Type v} [CommRing B] (f : A →+* B)
    (hf : ∀ s : S, IsUnit (f s)) :
    ∃! g : localization S →+* B, g.comp (localizationMap S) = f := by
  sorry

theorem localization_subsingleton_iff {A : Type u} [CommRing A] (S : Submonoid A) :
    Subsingleton (localization S) ↔ (0 : A) ∈ S := by
  sorry

/-! ## Modules localized at a multiplicative subset -/

/-- The canonical localization of an `R`-module. -/
abbrev localizedModule {R : Type u} [CommRing R] (S : Submonoid R)
    (M : Type v) [AddCommGroup M] [Module R M] := LocalizedModule S M

/-- The equivalence relation on module numerator-denominator pairs. -/
abbrev localizedModuleRelation {R : Type u} [CommRing R] (S : Submonoid R)
    (M : Type v) [AddCommGroup M] [Module R M] := LocalizedModule.r S M

theorem localizedModuleRelation_is_equivalence {R : Type u} [CommRing R]
    (S : Submonoid R) (M : Type v) [AddCommGroup M] [Module R M] :
    IsEquiv _ (localizedModuleRelation S M) := by
  sorry

/- The source's relation written with module scalar multiplication. -/
theorem localizedModuleRelation_cross_multiplication {R : Type u} [CommRing R]
    (S : Submonoid R) (M : Type v) [AddCommGroup M] [Module R M]
    (m n : M) (s t : S) :
    localizedModuleRelation S M (m, s) (n, t) ↔
      ∃ u : S, (u : R) • ((t : R) • m - (s : R) • n) = 0 := by
  sorry

/-- A module fraction, using the canonical `LocalizedModule.mk`. -/
def localizedModuleFraction {R : Type u} [CommRing R] (S : Submonoid R)
    {M : Type v} [AddCommGroup M] [Module R M] (m : M) (s : S) : localizedModule S M :=
  LocalizedModule.mk m s

theorem localizedModuleFraction_add {R : Type u} [CommRing R] (S : Submonoid R)
    {M : Type v} [AddCommGroup M] [Module R M] (m n : M) (s t : S) :
    localizedModuleFraction S m s + localizedModuleFraction S n t =
      localizedModuleFraction S ((t : R) • m + (s : R) • n) (s * t) := by
  sorry

/- The textbook's module multiplication display is corrected to scalar action. -/
theorem localizedModuleFraction_smul {R : Type u} [CommRing R] (S : Submonoid R)
    {M : Type v} [AddCommGroup M] [Module R M] (a : R) (m : M) (s t : S) :
    (localizationFraction S a s : localization S) • localizedModuleFraction S m t =
      localizedModuleFraction S (a • m) (s * t) := by
  sorry

/-- The map from a module to its localization. -/
def localizedModuleMap {R : Type u} [CommRing R] (S : Submonoid R)
    (M : Type v) [AddCommGroup M] [Module R M] :
    M →ₗ[R] localizedModule S M :=
  LocalizedModule.mkLinearMap S M

theorem localizedModuleMap_apply {R : Type u} [CommRing R] (S : Submonoid R)
    (M : Type v) [AddCommGroup M] [Module R M] (m : M) :
    localizedModuleMap S M m = localizedModuleFraction S m 1 := by
  rfl

/-- Restriction along the localization map on `R`-linear homomorphisms. -/
def localizedModuleHomRestriction {R : Type u} [CommRing R] (S : Submonoid R)
    {M : Type v} [AddCommGroup M] [Module R M]
    {N : Type v} [AddCommGroup N] [Module R N] :
    (localizedModule S M →ₗ[R] N) →ₗ[R] (M →ₗ[R] N) :=
  { toFun := fun f => f.comp (localizedModuleMap S M)
    map_add' := by
      intro f g
      ext m
      simp
    map_smul' := by
      intro a f
      ext m
      simp }

theorem localizedModuleHomRestriction_bijective {R : Type u} [CommRing R]
    (S : Submonoid R) {M : Type v} [AddCommGroup M] [Module R M]
    {N : Type v} [AddCommGroup N] [Module R N]
    (hN : ∀ s : S, Function.Bijective (fun n : N => (s : R) • n)) :
    Function.Bijective (localizedModuleHomRestriction S :
      (localizedModule S M →ₗ[R] N) → (M →ₗ[R] N)) := by
  sorry

noncomputable def localizedModuleHomEquiv {R : Type u} [CommRing R]
    (S : Submonoid R) {M : Type v} [AddCommGroup M] [Module R M]
    {N : Type v} [AddCommGroup N] [Module R N]
    (hN : ∀ s : S, Function.Bijective (fun n : N => (s : R) • n)) :
    (localizedModule S M →ₗ[R] N) ≃ₗ[R] (M →ₗ[R] N) :=
  LinearEquiv.ofBijective (localizedModuleHomRestriction S)
    (localizedModuleHomRestriction_bijective S hN)

/-! ## The module-category equivalence -/

/-- The property that every element of `S` acts bijectively on a module. -/
def localizationModuleProperty {R : Type u} [CommRing R] (S : Submonoid R) :
    ObjectProperty (ModuleCat.{u} R) :=
  fun N => ∀ s : S, Function.Bijective (fun n : (N : Type u) => (s : R) • n)

/-- The full subcategory of `R`-modules on which every element of `S` acts by an automorphism. -/
abbrev localizationModuleCategory {R : Type u} [CommRing R] (S : Submonoid R) :=
  (localizationModuleProperty S).FullSubcategory

theorem localization_module_category_equivalence {R : Type u} [CommRing R]
    (S : Submonoid R) :
    Nonempty (ModuleCat.{u} (localization S) ≌ localizationModuleCategory S) := by
  sorry

/-! ## Standard examples -/

abbrev localizationAtPrime {R : Type u} [CommRing R] (p : Ideal R) [p.IsPrime] :=
  Localization.AtPrime p

abbrev localizedModuleAtPrime {R : Type u} [CommRing R] (p : Ideal R) [p.IsPrime]
    (M : Type v) [AddCommGroup M] [Module R M] :=
  LocalizedModule.AtPrime p M

abbrev localizationAway {R : Type u} [CommRing R] (f : R) :=
  Localization.Away f

abbrev localizedModuleAway {R : Type u} [CommRing R] (f : R)
    (M : Type v) [AddCommGroup M] [Module R M] :=
  LocalizedModule.Away f M

theorem localizationAway_subsingleton_iff {R : Type u} [CommRing R] (f : R) :
    Subsingleton (localizationAway f) ↔ IsNilpotent f := by
  sorry

/-- The total quotient ring, localized at all non-zero-divisors. -/
abbrev totalQuotientRing (R : Type u) [CommRing R] := FractionRing R

theorem totalQuotient_is_fraction_ring {R : Type u} [CommRing R] :
    IsFractionRing R (totalQuotientRing R) := by
  infer_instance

/-! ## The filtered-colimit description -/

/-- The divisibility index used for the stages `M_f`. -/
structure LocalizationIndex {R : Type u} [CommRing R] (S : Submonoid R) where
  denominator : S

instance {R : Type u} [CommRing R] (S : Submonoid R) :
    LE (LocalizationIndex S) where
  le f g := ∃ c : R, (g.denominator : R) = (f.denominator : R) * c

instance {R : Type u} [CommRing R] (S : Submonoid R) :
    Preorder (LocalizationIndex S) where
  le := (· ≤ ·)
  le_refl f := ⟨1, by simp⟩
  le_trans f g h hfg hgh := by
    obtain ⟨c, hc⟩ := hfg
    obtain ⟨d, hd⟩ := hgh
    refine ⟨c * d, ?_⟩
    calc
      (h.denominator : R) = (g.denominator : R) * d := hd
      _ = ((f.denominator : R) * c) * d := by rw [hc]
      _ = (f.denominator : R) * (c * d) := by rw [mul_assoc]

theorem localizationIndex_le_iff {R : Type u} [CommRing R] (S : Submonoid R)
    (f g : LocalizationIndex S) :
    f ≤ g ↔ ∃ c : R, (g.denominator : R) = (f.denominator : R) * c :=
  Iff.rfl

abbrev localizationStage {R : Type u} [CommRing R] (S : Submonoid R)
    (M : Type v) [AddCommGroup M] [Module R M] (f : LocalizationIndex S) :=
  localizedModule (Submonoid.powers (f.denominator : R)) M

def localizationStageFraction {R : Type u} [CommRing R] (S : Submonoid R)
    {M : Type v} [AddCommGroup M] [Module R M] (f : LocalizationIndex S)
    (m : M) (e : ℕ) : localizationStage S M f :=
  localizedModuleFraction (Submonoid.powers (f.denominator : R)) m
    ⟨(f.denominator : R) ^ e, (Submonoid.mem_powers_iff _ _).2 ⟨e, rfl⟩⟩

theorem localizationStage_transition_formula {R : Type u} [CommRing R]
    (S : Submonoid R) {M : Type v} [AddCommGroup M] [Module R M]
    (f g : LocalizationIndex S) (hfg : f ≤ g) :
    ∃ c : R, (g.denominator : R) = (f.denominator : R) * c ∧
      ∃ φ : localizationStage S M f →ₗ[R] localizationStage S M g,
        ∀ (m : M) (e : ℕ),
          φ (localizationStageFraction S f m e) =
            localizationStageFraction S g ((c ^ e) • m) e := by
  sorry

noncomputable def localizationStageTransitionCoefficient {R : Type u} [CommRing R]
    (S : Submonoid R) {M : Type v} [AddCommGroup M] [Module R M]
    (f g : LocalizationIndex S) (hfg : f ≤ g) : R :=
  (localizationStage_transition_formula (M := M) S f g hfg).choose

noncomputable def localizationStageTransitionMap {R : Type u} [CommRing R]
    (S : Submonoid R) {M : Type v} [AddCommGroup M] [Module R M]
    (f g : LocalizationIndex S) (hfg : f ≤ g) :
    localizationStage S M f →ₗ[R] localizationStage S M g :=
  (localizationStage_transition_formula (M := M) S f g hfg).choose_spec.2.choose

theorem localizationStageTransitionMap_formula {R : Type u} [CommRing R]
    (S : Submonoid R) {M : Type v} [AddCommGroup M] [Module R M]
    (f g : LocalizationIndex S) (hfg : f ≤ g) (m : M) (e : ℕ) :
    localizationStageTransitionMap S f g hfg (localizationStageFraction S f m e) =
      localizationStageFraction S g
        ((localizationStageTransitionCoefficient (M := M) S f g hfg ^ e) • m) e := by
  exact (localizationStage_transition_formula (M := M) S f g hfg).choose_spec.2.choose_spec m e

noncomputable def localizationStageFunctor {R : Type u} [CommRing R]
    (S : Submonoid R) (M : Type v) [AddCommGroup M] [Module R M] :
    LocalizationIndex S ⥤ ModuleCat.{max u v} R where
  obj f := ModuleCat.of R (localizationStage S M f)
  map := fun {f g} h =>
    ModuleCat.ofHom (localizationStageTransitionMap S f g (leOfHom h))
  map_id := by
    sorry
  map_comp := by
    sorry

theorem localizedModule_is_colimit_of_stages {R : Type u} [CommRing R]
    (S : Submonoid R) (M : Type v) [AddCommGroup M] [Module R M] :
    Nonempty (colimit (localizationStageFunctor S M) ≅
      ModuleCat.of R (localizedModule S M)) := by
  sorry

/-! ## Products and iterated localization -/

/-- The product multiplicative subset, represented canonically by the sup of submonoids. -/
def localizationProduct {R : Type u} [CommRing R]
    (S S' : Submonoid R) : Submonoid R :=
  S ⊔ S'

theorem localizationProduct_mem_iff {R : Type u} [CommRing R]
    (S S' : Submonoid R) (x : R) :
    x ∈ localizationProduct S S' ↔
      ∃ s : S, ∃ s' : S', (s : R) * (s' : R) = x := by
  sorry

def localizationProductElement {R : Type u} [CommRing R]
    (S S' : Submonoid R) (s : S) (s' : S') : localizationProduct S S' :=
  ⟨(s : R) * (s' : R), Submonoid.mul_mem_sup s.property s'.property⟩

def localizationImage {R : Type u} [CommRing R]
    (S S' : Submonoid R) : Submonoid (localization S') :=
  S.map (algebraMap R (localization S')).toMonoidHom

def localizationImageElement {R : Type u} [CommRing R]
    (S S' : Submonoid R) (s : S) : localizationImage S S' :=
  ⟨algebraMap R (localization S') (s : R),
    Submonoid.mem_map_of_mem (algebraMap R (localization S')).toMonoidHom s.property⟩

theorem localization_iterated_ring_equiv {R : Type u} [CommRing R]
    (S S' : Submonoid R) :
    Nonempty (localization (localizationImage S S') ≃+*
      localization (localizationProduct S S')) := by
  sorry

theorem localization_iterated_ring_equiv_formula {R : Type u} [CommRing R]
    (S S' : Submonoid R) :
    ∃ e : localization (localizationImage S S') ≃+*
        localization (localizationProduct S S'),
      (∀ (x : R) (s : S) (s' : S'),
        e (localizationFraction (localizationImage S S')
            (localizationFraction S' x s') (localizationImageElement S S' s)) =
          localizationFraction (localizationProduct S S') x
            (localizationProductElement S S' s s')) ∧
      (∀ (x : R) (s : S) (s' : S'),
        e.symm (localizationFraction (localizationProduct S S') x
            (localizationProductElement S S' s s')) =
          localizationFraction (localizationImage S S')
            (localizationFraction S' x s') (localizationImageElement S S' s)) := by
  sorry

theorem localizedModule_iterated_equiv {R : Type u} [CommRing R]
    (S S' : Submonoid R) {M : Type v} [AddCommGroup M] [Module R M] :
    Nonempty (localizedModule S (localizedModule S' M) ≃ₗ[R]
      localizedModule (localizationProduct S S') M) := by
  sorry

theorem localizedModule_iterated_equiv_formula {R : Type u} [CommRing R]
    (S S' : Submonoid R) {M : Type v} [AddCommGroup M] [Module R M] :
    ∃ e : localizedModule S (localizedModule S' M) ≃ₗ[R]
        localizedModule (localizationProduct S S') M,
      (∀ (m : M) (s : S) (s' : S'),
        e (localizedModuleFraction S
            (localizedModuleFraction S' m s') s) =
          localizedModuleFraction (localizationProduct S S') m
            (localizationProductElement S S' s s')) ∧
      (∀ (m : M) (s : S) (s' : S'),
        e.symm (localizedModuleFraction (localizationProduct S S') m
            (localizationProductElement S S' s s')) =
          localizedModuleFraction S
            (localizedModuleFraction S' m s') s) := by
  sorry

/-! ## Functoriality and exactness -/

/-- The localized map induced by an `R`-linear map. -/
noncomputable def localizedLinearMap {R : Type u} [CommRing R]
    (S : Submonoid R) {M N : Type v} [AddCommGroup M] [AddCommGroup N]
    [Module R M] [Module R N] (u : M →ₗ[R] N) :
    localizedModule S M →ₗ[localization S] localizedModule S N :=
  LocalizedModule.map S u

theorem localizedLinearMap_mk {R : Type u} [CommRing R] (S : Submonoid R)
    {M N : Type v} [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N]
    (u : M →ₗ[R] N) (m : M) (s : S) :
    localizedLinearMap S u (localizedModuleFraction S m s) =
      localizedModuleFraction S (u m) s := by
  sorry

theorem localizedLinearMap_id {R : Type u} [CommRing R] (S : Submonoid R)
    {M : Type v} [AddCommGroup M] [Module R M] :
    localizedLinearMap S (LinearMap.id : M →ₗ[R] M) = LinearMap.id := by
  sorry

theorem localizedLinearMap_comp {R : Type u} [CommRing R]
    (S : Submonoid R) {L M N : Type v} [AddCommGroup L] [AddCommGroup M]
    [AddCommGroup N] [Module R L] [Module R M] [Module R N]
    (u : L →ₗ[R] M) (v : M →ₗ[R] N) :
    localizedLinearMap S (v.comp u) =
      (localizedLinearMap S v).comp (localizedLinearMap S u) := by
  sorry

abbrev localizationModuleFunctor {R : Type u} [CommRing R]
    (S : Submonoid R) [Small.{v} R] :
    ModuleCat.{v} R ⥤ ModuleCat.{v} (localization S) :=
  ModuleCat.localizedModuleFunctor S

theorem localizationModuleFunctor_exact {R : Type u} [CommRing R]
    (S : Submonoid R) [Small.{v} R] (T : ShortComplex (ModuleCat.{v} R))
    (hT : T.Exact) :
    (T.map (localizationModuleFunctor S)).Exact := by
  exact ModuleCat.localizedModuleFunctor_map_exact S T hT

theorem localization_maps_exact {R : Type u} [CommRing R] (S : Submonoid R)
    {L M N : Type v} [AddCommGroup L] [AddCommGroup M] [AddCommGroup N]
    [Module R L] [Module R M] [Module R N]
    (u : L →ₗ[R] M) (w : M →ₗ[R] N) (h : Function.Exact u w) :
    Function.Exact (localizedLinearMap S u) (localizedLinearMap S w) := by
  sorry

/-! ## Quotient modules -/

noncomputable abbrev localizedSubmodule {R : Type u} [CommRing R]
    (S : Submonoid R) {M : Type v} [AddCommGroup M] [Module R M]
    (N : Submodule R M) : Submodule (localization S) (localizedModule S M) :=
  N.localized S

theorem localizedQuotientModuleEquiv_exists {R : Type u} [CommRing R]
    (S : Submonoid R) {M : Type v} [AddCommGroup M] [Module R M]
    (N : Submodule R M) :
    Nonempty (localizedModule S (M ⧸ N) ≃ₗ[localization S]
      localizedModule S M ⧸ localizedSubmodule S N) := by
  sorry

theorem localizedQuotientModule_equiv_formula {R : Type u} [CommRing R]
    (S : Submonoid R) {M : Type v} [AddCommGroup M] [Module R M]
    (N : Submodule R M) :
    ∃ e : localizedModule S (M ⧸ N) ≃ₗ[localization S]
        localizedModule S M ⧸ localizedSubmodule S N,
      ∀ (m : M) (s : S),
        e (localizedModuleFraction S (Submodule.Quotient.mk m) s) =
          Submodule.Quotient.mk (localizedModuleFraction S m s) := by
  sorry

/-! ## Ideals and quotient rings -/

def localizedIdeal {A : Type u} [CommRing A] (S : Submonoid A) (I : Ideal A) :
    Ideal (localization S) :=
  I.map (algebraMap A (localization S))

def idealLocalizationPreimage {A : Type u} [CommRing A] (S : Submonoid A)
    (J : Ideal (localization S)) : Ideal A :=
  J.under A

theorem localizedIdeal_under {A : Type u} [CommRing A] (S : Submonoid A)
    (J : Ideal (localization S)) :
    localizedIdeal S (idealLocalizationPreimage S J) = J := by
  exact IsLocalization.map_under S (localization S) J

def quotientLocalizationSubmonoid {A : Type u} [CommRing A]
    (I : Ideal A) (S : Submonoid A) : Submonoid (A ⧸ I) :=
  S.map (Ideal.Quotient.mk I).toMonoidHom

def quotientLocalizationElement {A : Type u} [CommRing A]
    (I : Ideal A) (S : Submonoid A) (s : S) : quotientLocalizationSubmonoid I S :=
  ⟨Ideal.Quotient.mk I (s : A),
    Submonoid.mem_map_of_mem (Ideal.Quotient.mk I).toMonoidHom s.property⟩

theorem localized_quotient_ring_equiv {A : Type u} [CommRing A]
    (I : Ideal A) (S : Submonoid A) :
    Nonempty (localization (quotientLocalizationSubmonoid I S) ≃+*
      localization S ⧸ localizedIdeal S I) := by
  sorry

theorem localized_quotient_ring_equiv_formula {A : Type u} [CommRing A]
    (I : Ideal A) (S : Submonoid A) :
    ∃ e : localization (quotientLocalizationSubmonoid I S) ≃+*
        localization S ⧸ localizedIdeal S I,
      (∀ (x : A) (s : S),
        e (localizationFraction (quotientLocalizationSubmonoid I S)
            (Ideal.Quotient.mk I x) (quotientLocalizationElement I S s)) =
          Ideal.Quotient.mk (localizedIdeal S I) (localizationFraction S x s)) ∧
      (∀ (x : A) (s : S),
        e.symm (Ideal.Quotient.mk (localizedIdeal S I)
            (localizationFraction S x s)) =
          localizationFraction (quotientLocalizationSubmonoid I S)
            (Ideal.Quotient.mk I x) (quotientLocalizationElement I S s)) := by
  sorry

/-! ## Submodules and ideals of a localization -/

def submoduleLocalizationPreimage {R : Type u} [CommRing R]
    (S : Submonoid R) {M : Type v} [AddCommGroup M] [Module R M]
    (N' : Submodule (localization S) (localizedModule S M)) : Submodule R M :=
  (N'.restrictScalars R).comap (localizedModuleMap S M)

theorem submodule_localization_eq {R : Type u} [CommRing R]
    (S : Submonoid R) {M : Type v} [AddCommGroup M] [Module R M]
    (N' : Submodule (localization S) (localizedModule S M)) :
    localizedSubmodule S (submoduleLocalizationPreimage S N') = N' := by
  sorry

theorem ideal_localization_eq {A : Type u} [CommRing A] (S : Submonoid A)
    (J : Ideal (localization S)) :
    localizedIdeal S (idealLocalizationPreimage S J) = J :=
  localizedIdeal_under S J

end

end Formalization.Books.Algebra.Unit09
