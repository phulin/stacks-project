import Mathlib.Algebra.Category.ModuleCat.Localization
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
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
  exact (Localization.r S).iseqv.isEquiv

/- The source's cross-multiplication presentation of the canonical relation. -/
theorem localizationRelation_cross_multiplication {A : Type u} [CommRing A]
    (S : Submonoid A) (x y : A) (s t : S) :
    localizationRelation S (x, s) (y, t) ↔
      ∃ u : S, (x * (t : A) - y * (s : A)) * (u : A) = 0 := by
  rw [localizationRelation, Localization.r_iff_exists]
  constructor
  · rintro ⟨u, hu⟩
    refine ⟨u, ?_⟩
    dsimp at hu ⊢
    calc
      (x * (t : A) - y * (s : A)) * (u : A) =
          (u : A) * ((t : A) * x) - (u : A) * ((s : A) * y) := by ring
      _ = 0 := sub_eq_zero.mpr hu
  · rintro ⟨u, hu⟩
    refine ⟨u, ?_⟩
    dsimp at hu ⊢
    have hu' : (u : A) * ((t : A) * x) - (u : A) * ((s : A) * y) = 0 := by
      calc
        (u : A) * ((t : A) * x) - (u : A) * ((s : A) * y) =
            (x * (t : A) - y * (s : A)) * (u : A) := by ring
        _ = 0 := hu
    exact sub_eq_zero.mp hu'

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
  simpa [localizationFraction, add_comm, mul_comm] using Localization.add_mk x s y t

theorem localizationFraction_mul {A : Type u} [CommRing A] (S : Submonoid A)
    (x y : A) (s t : S) :
    localizationFraction S x s * localizationFraction S y t =
      localizationFraction S (x * y) (s * t) := by
  simpa [localizationFraction] using Localization.mk_mul x y s t

/-- The canonical map from a ring to its localization. -/
def localizationMap {A : Type u} [CommRing A] (S : Submonoid A) :
    A →+* localization S :=
  algebraMap A (localization S)

theorem localizationMap_eq_fraction_one {A : Type u} [CommRing A] (S : Submonoid A)
    (x : A) : localizationMap S x = localizationFraction S x 1 := by
  rfl

theorem localizationMap_eq_zero_iff {A : Type u} [CommRing A] (S : Submonoid A)
    (x : A) : localizationMap S x = 0 ↔ ∃ s : S, (s : A) * x = 0 := by
  exact IsLocalization.map_eq_zero_iff S (localization S) x

theorem localizationMap_injective_of_no_zero_divisors
    {A : Type u} [CommRing A] (S : Submonoid A)
    (hS : ∀ s : S, ∀ x : A, (s : A) * x = 0 → x = 0) :
    Function.Injective (localizationMap S) := by
  intro x y hxy
  apply sub_eq_zero.mp
  have hzero : localizationMap S (x - y) = 0 := by
    rw [map_sub, hxy, sub_self]
  obtain ⟨s, hs⟩ := (localizationMap_eq_zero_iff S (x - y)).mp hzero
  exact hS s (x - y) hs

/-- The universal property of the localization, in the source's ring-hom form. -/
theorem localization_universal_property {A : Type u} [CommRing A]
    (S : Submonoid A) {B : Type v} [CommRing B] (f : A →+* B)
    (hf : ∀ s : S, IsUnit (f s)) :
    ∃! g : localization S →+* B, g.comp (localizationMap S) = f := by
  refine ⟨IsLocalization.lift hf, IsLocalization.lift_comp hf, ?_⟩
  intro g hg
  exact (IsLocalization.lift_unique (M := S) (S := localization S) hf
    (fun x => RingHom.congr_fun hg x)).symm

theorem localization_subsingleton_iff {A : Type u} [CommRing A] (S : Submonoid A) :
    Subsingleton (localization S) ↔ (0 : A) ∈ S := by
  exact IsLocalization.subsingleton_iff (M := S) (S := localization S)

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
  exact LocalizedModule.r.isEquiv S M

/- The source's relation written with module scalar multiplication. -/
theorem localizedModuleRelation_cross_multiplication {R : Type u} [CommRing R]
    (S : Submonoid R) (M : Type v) [AddCommGroup M] [Module R M]
    (m n : M) (s t : S) :
    localizedModuleRelation S M (m, s) (n, t) ↔
      ∃ u : S, (u : R) • ((t : R) • m - (s : R) • n) = 0 := by
  rw [localizedModuleRelation, LocalizedModule.r]
  constructor
  · rintro ⟨u, hu⟩
    refine ⟨u, ?_⟩
    rw [smul_sub, sub_eq_zero]
    exact hu
  · rintro ⟨u, hu⟩
    refine ⟨u, ?_⟩
    rw [smul_sub] at hu
    exact sub_eq_zero.mp hu

/-- A module fraction, using the canonical `LocalizedModule.mk`. -/
def localizedModuleFraction {R : Type u} [CommRing R] (S : Submonoid R)
    {M : Type v} [AddCommGroup M] [Module R M] (m : M) (s : S) : localizedModule S M :=
  LocalizedModule.mk m s

theorem localizedModuleFraction_add {R : Type u} [CommRing R] (S : Submonoid R)
    {M : Type v} [AddCommGroup M] [Module R M] (m n : M) (s t : S) :
    localizedModuleFraction S m s + localizedModuleFraction S n t =
      localizedModuleFraction S ((t : R) • m + (s : R) • n) (s * t) := by
  change LocalizedModule.mk m s + LocalizedModule.mk n t =
    LocalizedModule.mk ((t : R) • m + (s : R) • n) (s * t)
  simpa [Submonoid.smul_def] using
    (LocalizedModule.mk_add_mk (S := S) (m1 := m) (m2 := n) (s1 := s) (s2 := t))

/- The textbook's module multiplication display is corrected to scalar action. -/
theorem localizedModuleFraction_smul {R : Type u} [CommRing R] (S : Submonoid R)
    {M : Type v} [AddCommGroup M] [Module R M] (a : R) (m : M) (s t : S) :
    (localizationFraction S a s : localization S) • localizedModuleFraction S m t =
      localizedModuleFraction S (a • m) (s * t) := by
  change Localization.mk a s • LocalizedModule.mk m t =
    LocalizedModule.mk (a • m) (s * t)
  exact LocalizedModule.mk_smul_mk (S := S) a m s t

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
  have hEnd : ∀ s : S, IsUnit (algebraMap R (Module.End R N) (s : R)) := by
    intro s
    rw [Module.End.isUnit_iff]
    constructor
    · intro a b hab
      apply (hN s).1
      simpa only [Module.algebraMap_end_apply] using hab
    · intro a
      obtain ⟨b, hb⟩ := (hN s).2 a
      refine ⟨b, ?_⟩
      simpa only [Module.algebraMap_end_apply] using hb
  refine Function.bijective_iff_has_inverse.mpr ⟨
    (fun f => LocalizedModule.lift S f hEnd), ?_, ?_⟩
  · intro f
    exact LocalizedModule.lift_unique S (f.comp (localizedModuleMap S M)) hEnd f rfl
  · intro f
    change (LocalizedModule.lift S f hEnd).comp (localizedModuleMap S M) = f
    exact LocalizedModule.lift_comp S f hEnd

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
  have restricted_property :
      ∀ N : ModuleCat.{u} (localization S),
        localizationModuleProperty S
          ((ModuleCat.restrictScalars (algebraMap R (localization S))).obj N) := by
    intro N s
    let : Module R (N : Type u) :=
      Module.compHom (N : Type u) (algebraMap R (localization S))
    let : IsScalarTower R (localization S) (N : Type u) :=
      IsScalarTower.of_compHom R (localization S) (N : Type u)
    let hloc : IsLocalizedModule S
        (LinearMap.id : (N : Type u) →ₗ[R] (N : Type u)) :=
      isLocalizedModule_id S (N : Type u) (localization S)
    exact (Module.End.isUnit_iff _).mp (hloc.map_units s)
  have localized_id (X : localizationModuleCategory S) :
      IsLocalizedModule S
        (LinearMap.id : (X.obj : Type u) →ₗ[R] (X.obj : Type u)) := by
    refine { map_units := ?_, surj := ?_, exists_of_eq := ?_ }
    · intro s
      exact (Module.End.isUnit_iff _).mpr (X.property s)
    · intro x
      exact ⟨(x, 1), by simp⟩
    · intro x y hxy
      exact ⟨1, by simpa using hxy⟩
  let F₀ : ModuleCat.{u} (localization S) ⥤ ModuleCat.{u} R :=
    ModuleCat.restrictScalars (algebraMap R (localization S))
  let F : ModuleCat.{u} (localization S) ⥤ localizationModuleCategory S :=
    (localizationModuleProperty S).lift F₀ restricted_property
  let G : localizationModuleCategory S ⥤ ModuleCat.{u} (localization S) :=
    { obj := fun X => ModuleCat.of (localization S) (localizedModule S (X.obj : Type u))
      map := fun f => ModuleCat.ofHom (LocalizedModule.map S f.hom.hom)
      map_id := by
        intro X
        apply ModuleCat.hom_ext
        simp
      map_comp := by
        intro X Y Z f g
        apply ModuleCat.hom_ext
        ext x
        induction x using LocalizedModule.induction_on with
        | _ m s => simp }
  let unitComponent (N : ModuleCat.{u} (localization S)) :
      N ≅ (G.obj (F.obj N)) := by
    letI : Module R (N : Type u) :=
      Module.compHom (N : Type u) (algebraMap R (localization S))
    letI : IsScalarTower R (localization S) (N : Type u) :=
      IsScalarTower.of_compHom R (localization S) (N : Type u)
    letI : IsLocalizedModule S
        (LinearMap.id : (N : Type u) →ₗ[R] (N : Type u)) :=
      isLocalizedModule_id S (N : Type u) (localization S)
    exact LinearEquiv.toModuleIso
      ((IsLocalizedModule.iso S
        (LinearMap.id : (N : Type u) →ₗ[R] (N : Type u))).extendScalarsOfIsLocalization
          S (localization S)).symm
  let counitComponent (X : localizationModuleCategory S) :
      (G ⋙ F).obj X ≅ X := by
    dsimp [F, G, F₀]
    letI : IsLocalizedModule S
        (LinearMap.id : (X.obj : Type u) →ₗ[R] (X.obj : Type u)) :=
      localized_id X
    let e0 := IsLocalizedModule.iso S
      (LinearMap.id : (X.obj : Type u) →ₗ[R] (X.obj : Type u))
    let eMap : ((G ⋙ F).obj X).obj →ₗ[R] X.obj :=
      { toFun := e0
        map_add' := by
          intro x y
          exact e0.map_add x y
        map_smul' := by
          intro r x
          induction x using LocalizedModule.induction_on with
          | _ m s =>
            change e0 ((Localization.mk (S := S) r (1 : S) : localization S) •
              LocalizedModule.mk m s) = r • e0 (LocalizedModule.mk m s)
            rw [LocalizedModule.mk_smul_mk (S := S) r m 1 s]
            simp [← LocalizedModule.smul'_mk] }
    apply (localizationModuleProperty S).isoMk
    exact LinearEquiv.toModuleIso (LinearEquiv.ofBijective eMap e0.bijective)
  let unit : 𝟭 (ModuleCat.{u} (localization S)) ≅ F ⋙ G :=
    NatIso.ofComponents unitComponent (by
      intro X Y f
      have h :
          (unitComponent X).inv ≫ (𝟭 (ModuleCat.{u} (localization S))).map f =
            (F ⋙ G).map f ≫ (unitComponent Y).inv := by
        let : IsLocalizedModule S
            (LinearMap.id : (F.obj X).obj →ₗ[R] (F.obj X).obj) :=
          localized_id (F.obj X)
        let : IsLocalizedModule S
            (LinearMap.id : (F.obj Y).obj →ₗ[R] (F.obj Y).obj) :=
          localized_id (F.obj Y)
        apply ModuleCat.hom_ext
        ext x
        dsimp [unitComponent, F, G, F₀]
        have hmapid :
            IsLocalizedModule.map S
                (LinearMap.id : (F.obj X).obj →ₗ[R] (F.obj X).obj)
                (LinearMap.id : (F.obj Y).obj →ₗ[R] (F.obj Y).obj)
                (F.map f).hom.hom = (F.map f).hom.hom := by
          apply IsLocalizedModule.linearMap_ext S
            (f := (LinearMap.id : (F.obj X).obj →ₗ[R] (F.obj X).obj))
            (f' := (LinearMap.id : (F.obj Y).obj →ₗ[R] (F.obj Y).obj))
          simpa using
            (IsLocalizedModule.map_comp (S := S)
              (f := (LinearMap.id : (F.obj X).obj →ₗ[R] (F.obj X).obj))
              (g := (LinearMap.id : (F.obj Y).obj →ₗ[R] (F.obj Y).obj))
              (F.map f).hom.hom)
        have hmap :=
          congrArg (fun k => k x)
            (IsLocalizedModule.map_iso_commute (S := S)
            (f₀ := (LinearMap.id : (F.obj X).obj →ₗ[R] (F.obj X).obj))
            (f₁ := (LinearMap.id : (F.obj Y).obj →ₗ[R] (F.obj Y).obj))
              (F.map f).hom.hom)
        rw [hmapid] at hmap
        simp only [LinearMap.comp_apply] at hmap
        have hmapcanon (z : LocalizedModule S (F.obj X).obj) :
            IsLocalizedModule.map S
                (LocalizedModule.mkLinearMap S (F.obj X).obj)
                (LocalizedModule.mkLinearMap S (F.obj Y).obj)
                (F.map f).hom.hom z =
              LocalizedModule.map S (F.map f).hom.hom z := by
          induction z using LocalizedModule.induction_on with
          | _ m s =>
            simpa using
              (IsLocalizedModule.map_LocalizedModules (S := S)
                (g := (F.map f).hom.hom) m s)
        rw [hmapcanon] at hmap
        change (F.map f).hom.hom
            ((IsLocalizedModule.iso S
              (LinearMap.id : (F.obj X).obj →ₗ[R] (F.obj X).obj)) x) =
          IsLocalizedModule.iso S
            (LinearMap.id : (F.obj Y).obj →ₗ[R] (F.obj Y).obj)
            ((LocalizedModule.map S (F.map f).hom.hom) x)
        exact hmap
      apply (cancel_mono (unitComponent Y).inv).1
      simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
      simpa only [Category.assoc, Iso.hom_inv_id_assoc] using
        (congrArg (fun k => (unitComponent X).hom ≫ k) h))
  let counit : G ⋙ F ≅ 𝟭 (localizationModuleCategory S) :=
    NatIso.ofComponents counitComponent (by
      intro X Y f
      apply (localizationModuleProperty S).hom_ext
      ext x
      change localizedModule S (X.obj : Type u) at x
      dsimp [counitComponent, F, G, F₀]
      let : IsLocalizedModule S
          (LinearMap.id : (X.obj : Type u) →ₗ[R] (X.obj : Type u)) :=
        localized_id X
      let : IsLocalizedModule S
          (LinearMap.id : (Y.obj : Type u) →ₗ[R] (Y.obj : Type u)) :=
        localized_id Y
      have hmapid :
          IsLocalizedModule.map S
              (LinearMap.id : (X.obj : Type u) →ₗ[R] (X.obj : Type u))
              (LinearMap.id : (Y.obj : Type u) →ₗ[R] (Y.obj : Type u))
              f.hom.hom = f.hom.hom := by
        apply IsLocalizedModule.linearMap_ext S
          (f := (LinearMap.id : (X.obj : Type u) →ₗ[R] (X.obj : Type u)))
          (f' := (LinearMap.id : (Y.obj : Type u) →ₗ[R] (Y.obj : Type u)))
        simpa using
          (IsLocalizedModule.map_comp (S := S)
            (f := (LinearMap.id : (X.obj : Type u) →ₗ[R] (X.obj : Type u)))
            (g := (LinearMap.id : (Y.obj : Type u) →ₗ[R] (Y.obj : Type u)))
            f.hom.hom)
      have hmap :=
        congrArg (fun k => k x)
          (IsLocalizedModule.map_iso_commute (S := S)
            (f₀ := (LinearMap.id : (X.obj : Type u) →ₗ[R] (X.obj : Type u)))
            (f₁ := (LinearMap.id : (Y.obj : Type u) →ₗ[R] (Y.obj : Type u)))
            f.hom.hom)
      rw [hmapid] at hmap
      change (f.hom.hom)
          ((IsLocalizedModule.iso S
            (LinearMap.id : (X.obj : Type u) →ₗ[R] (X.obj : Type u))) x) =
        IsLocalizedModule.iso S
          (LinearMap.id : (Y.obj : Type u) →ₗ[R] (Y.obj : Type u))
          ((IsLocalizedModule.map S
            (LocalizedModule.mkLinearMap S (X.obj : Type u))
            (LocalizedModule.mkLinearMap S (Y.obj : Type u)) f.hom.hom) x) at hmap
      have hmapcanon (z : LocalizedModule S (X.obj : Type u)) :
          IsLocalizedModule.map S
              (LocalizedModule.mkLinearMap S (X.obj : Type u))
              (LocalizedModule.mkLinearMap S (Y.obj : Type u))
              f.hom.hom z = LocalizedModule.map S f.hom.hom z := by
        induction z using LocalizedModule.induction_on with
        | _ m s =>
          simpa using
            (IsLocalizedModule.map_LocalizedModules (S := S) (g := f.hom.hom) m s)
      rw [hmapcanon] at hmap
      change (IsLocalizedModule.iso S
          (LinearMap.id : (Y.obj : Type u) →ₗ[R] (Y.obj : Type u)))
          ((LocalizedModule.map S f.hom.hom) x) =
        f.hom.hom ((IsLocalizedModule.iso S
          (LinearMap.id : (X.obj : Type u) →ₗ[R] (X.obj : Type u))) x)
      exact hmap.symm)
  exact ⟨CategoryTheory.Equivalence.mk F G unit counit⟩

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
  simpa [localizationAway, localization, IsNilpotent, Submonoid.mem_powers_iff] using
    (IsLocalization.subsingleton_iff (M := Submonoid.powers f)
      (S := localizationAway f))

/-- The total quotient ring, localized at all non-zero-divisors. -/
abbrev totalQuotientRing (R : Type u) [CommRing R] := FractionRing R

theorem totalQuotient_is_fraction_ring {R : Type u} [CommRing R] :
    IsFractionRing R (totalQuotientRing R) := by
  infer_instance

theorem totalQuotient_isField {R : Type u} [CommRing R] [IsDomain R] :
    IsField (totalQuotientRing R) :=
  Field.toIsField _

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

instance {R : Type u} [CommRing R] (S : Submonoid R) :
    Nonempty (LocalizationIndex S) :=
  ⟨⟨1⟩⟩

instance {R : Type u} [CommRing R] (S : Submonoid R) :
    IsDirectedOrder (LocalizationIndex S) where
  directed f g := by
    refine ⟨⟨f.denominator * g.denominator⟩, ?_, ?_⟩
    · exact ⟨(g.denominator : R), by simp⟩
    · exact ⟨(f.denominator : R), by simp [mul_comm]⟩

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
  obtain ⟨c, hc⟩ := hfg
  refine ⟨c, hc, ?_⟩
  let Sf := Submonoid.powers (f.denominator : R)
  let Sg := Submonoid.powers (g.denominator : R)
  let N := localizedModule Sg M
  have hEnd : ∀ p : Sf, IsUnit (algebraMap R (Module.End R N) (p : R)) := by
    intro p
    rcases (Submonoid.mem_powers_iff _ _).mp p.property with ⟨n, hn⟩
    rw [← hn]
    have hg : Function.Bijective
        (fun x : N => ((g.denominator : R) ^ n) • x) := by
      have h := (Module.End.isUnit_iff _).mp
        (IsLocalizedModule.map_units (LocalizedModule.mkLinearMap Sg M)
          ⟨(g.denominator : R) ^ n,
            (Submonoid.mem_powers_iff _ _).2 ⟨n, rfl⟩⟩)
      have hfun :
          (algebraMap R (Module.End R N) ((g.denominator : R) ^ n) : N → N) =
            (fun x : N => ((g.denominator : R) ^ n) • x) := by
        funext x
        rw [Module.algebraMap_end_apply]
      rw [hfun] at h
      exact h
    have hprod_fun :
        (fun x : N => ((f.denominator : R) ^ n) •
          ((c ^ n) • x)) =
          (fun x : N => ((g.denominator : R) ^ n) • x) := by
      funext x
      rw [smul_smul, ← mul_pow, ← hc]
    have hprod : Function.Bijective
        (fun x : N => ((f.denominator : R) ^ n) •
          ((c ^ n) • x)) := by
      rw [hprod_fun]
      exact hg
    apply (Module.End.isUnit_iff _).mpr
    have hscalar :
        (algebraMap R (Module.End R N) ((f.denominator : R) ^ n) : N → N) =
          (fun x : N => ((f.denominator : R) ^ n) • x) := by
      funext x
      rw [Module.algebraMap_end_apply]
    rw [hscalar]
    constructor
    · intro x y hxy
      apply hprod.1
      simpa [smul_smul, mul_comm] using
        congrArg (fun z : N => (c ^ n) • z) hxy
    · intro y
      obtain ⟨z, hz⟩ := hprod.2 y
      exact ⟨(c ^ n) • z, hz⟩
  let φ : localizationStage S M f →ₗ[R] localizationStage S M g :=
    LocalizedModule.lift Sf (LocalizedModule.mkLinearMap Sg M) hEnd
  refine ⟨φ, ?_⟩
  intro m e
  let sf : Sf :=
    ⟨(f.denominator : R) ^ e,
      (Submonoid.mem_powers_iff _ _).2 ⟨e, rfl⟩⟩
  let sg : Sg :=
    ⟨(g.denominator : R) ^ e,
      (Submonoid.mem_powers_iff _ _).2 ⟨e, rfl⟩⟩
  change φ (LocalizedModule.mk m sf) =
    LocalizedModule.mk ((c ^ e) • m) sg
  have hinj : Function.Injective
      (fun x : N => ((f.denominator : R) ^ e) • x) :=
    (Module.End.isUnit_iff _).mp (hEnd sf) |>.1
  apply hinj
  calc
    ((f.denominator : R) ^ e) • φ (LocalizedModule.mk m sf) =
        φ (((f.denominator : R) ^ e) • LocalizedModule.mk m sf) := by
          rw [φ.map_smul]
    _ = φ (LocalizedModule.mk m 1) := by
      congr 1
      rw [LocalizedModule.smul'_mk]
      exact LocalizedModule.mk_cancel sf m
    _ = LocalizedModule.mk m 1 := by
      simp [φ]
    _ = ((f.denominator : R) ^ e) •
        LocalizedModule.mk ((c ^ e) • m) sg := by
      symm
      calc
        ((f.denominator : R) ^ e) •
            LocalizedModule.mk ((c ^ e) • m) sg =
            LocalizedModule.mk
              (((f.denominator : R) ^ e) • ((c ^ e) • m)) sg := by
                rw [LocalizedModule.smul'_mk]
        _ = LocalizedModule.mk (((g.denominator : R) ^ e) • m) sg := by
          congr 1
          rw [smul_smul, ← mul_pow, ← hc]
        _ = ((g.denominator : R) ^ e) • LocalizedModule.mk m sg := by
          rw [LocalizedModule.smul'_mk]
        _ = LocalizedModule.mk m 1 := by
          rw [LocalizedModule.smul'_mk]
          exact LocalizedModule.mk_cancel sg m

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
    intro X
    apply ModuleCat.hom_ext
    ext x
    induction x using LocalizedModule.induction_on with
    | _ m s =>
      rcases (Submonoid.mem_powers_iff _ _).mp s.property with ⟨e, he⟩
      have hs : s = ⟨(X.denominator : R) ^ e,
          (Submonoid.mem_powers_iff _ _).2 ⟨e, rfl⟩⟩ := Subtype.ext he.symm
      rw [hs]
      change localizationStageTransitionMap S X X le_rfl
          (localizationStageFraction S X m e) =
        localizationStageFraction S X m e
      rw [localizationStageTransitionMap_formula
        (S := S) (f := X) (g := X) (hfg := le_rfl)]
      have hc :=
        (localizationStage_transition_formula (M := M) S X X le_rfl).choose_spec.1
      have hc' :
          (X.denominator : R) *
              localizationStageTransitionCoefficient (M := M) S X X le_rfl =
            (X.denominator : R) := hc.symm
      apply LocalizedModule.mk_eq.mpr
      refine ⟨1, ?_⟩
      simp only [one_smul, Submonoid.smul_def]
      rw [smul_smul, ← mul_pow, hc']
  map_comp := by
    intro X Y Z f g
    apply ModuleCat.hom_ext
    ext x
    induction x using LocalizedModule.induction_on with
    | _ m s =>
      rcases (Submonoid.mem_powers_iff _ _).mp s.property with ⟨e, he⟩
      have hs : s = ⟨(X.denominator : R) ^ e,
          (Submonoid.mem_powers_iff _ _).2 ⟨e, rfl⟩⟩ := Subtype.ext he.symm
      rw [hs]
      change localizationStageTransitionMap S X Z (leOfHom (f ≫ g))
          (localizationStageFraction S X m e) =
        localizationStageTransitionMap S Y Z (leOfHom g)
          (localizationStageTransitionMap S X Y (leOfHom f)
            (localizationStageFraction S X m e))
      rw [localizationStageTransitionMap_formula
          (S := S) (f := X) (g := Z) (hfg := leOfHom (f ≫ g)),
        localizationStageTransitionMap_formula
          (S := S) (f := X) (g := Y) (hfg := leOfHom f),
        localizationStageTransitionMap_formula
          (S := S) (f := Y) (g := Z) (hfg := leOfHom g)]
      let a : R := localizationStageTransitionCoefficient (M := M) S X Y (leOfHom f)
      let b : R := localizationStageTransitionCoefficient (M := M) S Y Z (leOfHom g)
      let c : R := localizationStageTransitionCoefficient (M := M) S X Z (leOfHom (f ≫ g))
      change localizationStageFraction S Z (c ^ e • m) e =
        localizationStageFraction S Z (b ^ e • a ^ e • m) e
      have hcXY : (Y.denominator : R) = (X.denominator : R) * a := by
        dsimp [a]
        exact (localizationStage_transition_formula (M := M) S X Y
          (leOfHom f)).choose_spec.1
      have hcYZ : (Z.denominator : R) = (Y.denominator : R) * b := by
        dsimp [b]
        exact (localizationStage_transition_formula (M := M) S Y Z
          (leOfHom g)).choose_spec.1
      have hcXZ : (Z.denominator : R) = (X.denominator : R) * c := by
        dsimp [c]
        exact (localizationStage_transition_formula (M := M) S X Z
          (leOfHom (f ≫ g))).choose_spec.1
      have hbase : (X.denominator : R) * c = (X.denominator : R) * (a * b) := by
        calc
          (X.denominator : R) * c = (Z.denominator : R) := hcXZ.symm
          _ = (Y.denominator : R) * b := hcYZ
          _ = ((X.denominator : R) * a) * b := by rw [hcXY]
          _ = (X.denominator : R) * (a * b) := by rw [mul_assoc]
      have hrel : (Z.denominator : R) * c = (Z.denominator : R) * (a * b) := by
        calc
          (Z.denominator : R) * c = ((X.denominator : R) * c) * c := by rw [hcXZ]
          _ = ((X.denominator : R) * (a * b)) * c := by rw [hbase]
          _ = ((X.denominator : R) * c) * (a * b) := by ac_rfl
          _ = (Z.denominator : R) * (a * b) := by rw [hcXZ.symm]
      have hpow : (Z.denominator : R) ^ e * c ^ e =
          (Z.denominator : R) ^ e * (a * b) ^ e := by
        calc
          (Z.denominator : R) ^ e * c ^ e =
              ((Z.denominator : R) * c) ^ e := by rw [mul_pow]
          _ = ((Z.denominator : R) * (a * b)) ^ e := by rw [hrel]
          _ = (Z.denominator : R) ^ e * (a * b) ^ e := by rw [mul_pow]
      have hscalar : (Z.denominator : R) ^ e * c ^ e =
          ((Z.denominator : R) ^ e * b ^ e) * a ^ e := by
        calc
          (Z.denominator : R) ^ e * c ^ e =
              (Z.denominator : R) ^ e * (a * b) ^ e := hpow
          _ = (Z.denominator : R) ^ e * (a ^ e * b ^ e) := by rw [mul_pow]
          _ = ((Z.denominator : R) ^ e * b ^ e) * a ^ e := by ac_rfl
      apply LocalizedModule.mk_eq.mpr
      refine ⟨1, ?_⟩
      simp only [one_smul, Submonoid.smul_def]
      simp only [smul_smul]
      rw [hscalar, mul_assoc]

theorem localizedModule_is_colimit_of_stages {R : Type u} [CommRing R]
    (S : Submonoid R) (M : Type v) [AddCommGroup M] [Module R M] :
    Nonempty (colimit (localizationStageFunctor S M) ≅
      ModuleCat.of R (localizedModule S M)) := by
  have power_le (f : LocalizationIndex S) :
      Submonoid.powers (f.denominator : R) ≤ S := by
    intro x hx
    rcases (Submonoid.mem_powers_iff _ _).mp hx with ⟨e, rfl⟩
    exact S.pow_mem f.denominator.property e
  let stageMap (f : LocalizationIndex S) :
      localizationStage S M f →ₗ[R] localizedModule S M :=
    LocalizedModule.liftOfLE (Submonoid.powers (f.denominator : R)) S
      (power_le f)
  have stageMap_fraction (f : LocalizationIndex S) (m : M) (e : ℕ) :
      stageMap f (localizationStageFraction S f m e) =
        localizedModuleFraction S m
          ⟨(f.denominator : R) ^ e, S.pow_mem f.denominator.property e⟩ := by
    let sf : Submonoid.powers (f.denominator : R) :=
      ⟨(f.denominator : R) ^ e,
        (Submonoid.mem_powers_iff _ _).2 ⟨e, rfl⟩⟩
    change stageMap f (LocalizedModule.mk m sf) = _
    rw [IsLocalizedModule.mk_eq_mk']
    simp [stageMap, IsLocalizedModule.liftOfLE_mk']
    rw [← IsLocalizedModule.mk_eq_mk' (S := S)]
    rfl
  let stageCocone : Cocone (localizationStageFunctor S M) :=
    { pt := ModuleCat.of R (localizedModule S M)
      ι :=
        { app := fun f => ModuleCat.ofHom (stageMap f)
          naturality := by
            intro f g h
            apply ModuleCat.hom_ext
            ext x
            induction x using LocalizedModule.induction_on with
            | _ m s =>
              rcases (Submonoid.mem_powers_iff _ _).mp s.property with ⟨e, he⟩
              have hs : s = ⟨(f.denominator : R) ^ e,
                  (Submonoid.mem_powers_iff _ _).2 ⟨e, rfl⟩⟩ :=
                Subtype.ext he.symm
              rw [hs]
              change stageMap g
                  (localizationStageTransitionMap S f g (leOfHom h)
                    (localizationStageFraction S f m e)) =
                stageMap f (localizationStageFraction S f m e)
              rw [localizationStageTransitionMap_formula
                    (S := S) (f := f) (g := g) (hfg := leOfHom h),
                  stageMap_fraction, stageMap_fraction]
              let c : R := localizationStageTransitionCoefficient
                (M := M) S f g (leOfHom h)
              have hc : (g.denominator : R) = (f.denominator : R) * c := by
                dsimp [c]
                exact (localizationStage_transition_formula (M := M) S f g
                  (leOfHom h)).choose_spec.1
              apply LocalizedModule.mk_eq.mpr
              refine ⟨1, ?_⟩
              simp only [one_smul, Submonoid.smul_def]
              rw [smul_smul, ← mul_pow, hc, mul_pow]
              } }
  classical
  let transition (f g : LocalizationIndex S) (hfg : f ≤ g) :
      localizationStage S M f →ₗ[R] localizationStage S M g :=
    localizationStageTransitionMap S f g hfg
  let G : LocalizationIndex S → Type (max u v) :=
    fun f => localizationStage S M f
  let stageMap' : (f : LocalizationIndex S) → G f →ₗ[R] localizedModule S M :=
    fun f => stageMap f
  let directLimit : Type (max u v) :=
    Module.DirectLimit G transition
  let stageCompat (f g : LocalizationIndex S) (hfg : f ≤ g)
      (x : G f) :
      stageMap' g (transition f g hfg x) = stageMap' f x := by
    have hn := congrArg (fun k => k.hom x)
      (stageCocone.ι.naturality (homOfLE hfg))
    change stageMap' g (transition f g hfg x) = stageMap' f x at hn
    exact hn
  let directLimitMap : directLimit →ₗ[R] localizedModule S M :=
    Module.DirectLimit.lift R (LocalizationIndex S) G transition
      (fun f => stageMap' f) (by
        intro f g hfg x
        exact stageCompat f g hfg x)
  have directLimitMap_of (f : LocalizationIndex S)
      (x : G f) :
      directLimitMap (Module.DirectLimit.of R (LocalizationIndex S) G transition f x) =
        stageMap' f x := by
      simp only [directLimitMap, directLimit, G, transition,
      Module.DirectLimit.lift_of]
  let sourceEq (f : LocalizationIndex S) :
      ModuleCat.of R (localizationStage S M f) =
        (localizationStageFunctor S M).obj f := by
    rfl
  have sourceEq_hom (f : LocalizationIndex S) :
      (eqToHom (sourceEq f)).hom = LinearMap.id := by
    dsimp [sourceEq]
    rfl
  have sourceEq_symm_hom (f : LocalizationIndex S) :
      (eqToHom (sourceEq f).symm).hom = LinearMap.id := by
    dsimp [sourceEq]
    rfl
  let directLimitCocone : Cocone (localizationStageFunctor S M) :=
    { pt := ModuleCat.of R directLimit
      ι :=
        { app := fun f =>
            eqToHom (sourceEq f).symm ≫
              ModuleCat.ofHom
                (Module.DirectLimit.of R (LocalizationIndex S) G transition f)
          naturality := by
            intro f g h
            apply ModuleCat.hom_ext
            ext x
            have htrans :
                (eqToHom (sourceEq g).symm).hom
                    (((localizationStageFunctor S M).map h).hom x) =
                  transition f g (leOfHom h)
                    ((eqToHom (sourceEq f).symm).hom x) := by
              dsimp [sourceEq, transition, localizationStageFunctor]
              rfl
            change Module.DirectLimit.of R (LocalizationIndex S) G transition g
                  ((eqToHom (sourceEq g).symm).hom
                    (((localizationStageFunctor S M).map h).hom x)) =
              Module.DirectLimit.of R (LocalizationIndex S) G transition f
                ((eqToHom (sourceEq f).symm).hom x)
            rw [htrans]
            exact Module.DirectLimit.of_f } }
  let directLimitDesc (t : Cocone (localizationStageFunctor S M)) :
      ModuleCat.of R directLimit ⟶ t.pt :=
      ModuleCat.ofHom
      (Module.DirectLimit.lift R (LocalizationIndex S) G transition
        (fun f =>
          (eqToHom (sourceEq f) ≫ t.ι.app f).hom) (by
          intro f g hfg x
          have hn := congrArg
              (fun k => k.hom ((eqToHom (sourceEq f)).hom x))
            (t.ι.naturality (homOfLE hfg))
          change (t.ι.app g).hom
              ((eqToHom (sourceEq g)).hom (transition f g hfg x)) =
            (t.ι.app f).hom ((eqToHom (sourceEq f)).hom x)
          have htrans :
              (eqToHom (sourceEq g)).hom (transition f g hfg x) =
                ((localizationStageFunctor S M).map (homOfLE hfg)).hom
                  ((eqToHom (sourceEq f)).hom x) := by
            dsimp [sourceEq, transition, localizationStageFunctor]
            rfl
          rw [htrans]
          rw [ModuleCat.comp_apply, ModuleCat.comp_apply] at hn
          change (t.ι.app g).hom
              ((localizationStageTransitionMap S f g hfg)
                ((eqToHom (sourceEq f)).hom x)) =
            (t.ι.app f).hom ((eqToHom (sourceEq f)).hom x) at hn
          exact hn))
  have directLimitIsColimit : IsColimit directLimitCocone := by
    refine
      { desc := fun t => directLimitDesc t
        fac := by
          intro t f
          apply ModuleCat.hom_ext
          ext x
          dsimp [directLimitDesc, directLimitCocone]
          rw [Module.DirectLimit.lift_of]
          simp only [sourceEq_hom, sourceEq_symm_hom]
          change (t.ι.app f).hom x = (t.ι.app f).hom x
          rfl
        uniq := by
          intro t g hg
          apply ModuleCat.hom_ext
          apply Module.DirectLimit.hom_ext
          intro f
          apply LinearMap.ext
          intro x
          have hn := congrArg (fun k => k.hom x) (hg f)
          dsimp [directLimitDesc, directLimitCocone] at hn ⊢
          rw [Module.DirectLimit.lift_of]
          change g.hom
              ((Module.DirectLimit.of R (LocalizationIndex S) G transition f) x) =
            (t.ι.app f).hom x at hn
          change g.hom
              ((Module.DirectLimit.of R (LocalizationIndex S) G transition f) x) =
            (t.ι.app f).hom x
          exact hn }
  have kernel_eventual (f : LocalizationIndex S)
      (z : localizationStage S M f) (hz : stageMap f z = 0) :
      ∃ (g : LocalizationIndex S) (hfg : f ≤ g),
        localizationStageTransitionMap S f g hfg z = 0 := by
    induction z using LocalizedModule.induction_on with
    | _ m s =>
      rcases (Submonoid.mem_powers_iff _ _).mp s.property with ⟨e, he⟩
      have hs : s = ⟨(f.denominator : R) ^ e,
          (Submonoid.mem_powers_iff _ _).2 ⟨e, rfl⟩⟩ :=
        Subtype.ext he.symm
      rw [hs] at hz
      change stageMap f (localizationStageFraction S f m e) = 0 at hz
      rw [stageMap_fraction] at hz
      change LocalizedModule.mk m
          ⟨(f.denominator : R) ^ e,
            S.pow_mem f.denominator.property e⟩ = 0 at hz
      have hzero_mk : (0 : localizedModule S M) =
          LocalizedModule.mk 0 (1 : S) :=
        (LocalizedModule.zero_mk (S := S) (1 : S)).symm
      rw [hzero_mk] at hz
      rcases LocalizedModule.mk_eq.mp hz with ⟨u, hu⟩
      let g : LocalizationIndex S :=
        ⟨(f.denominator : R) * (u : R),
          S.mul_mem f.denominator.property u.property⟩
      have hfg : f ≤ g := by
        refine ⟨(u : R), ?_⟩
        rfl
      refine ⟨g, hfg, ?_⟩
      rw [hs]
      change localizationStageTransitionMap S f g hfg
          (localizationStageFraction S f m e) = 0
      rw [localizationStageTransitionMap_formula]
      let c : R := localizationStageTransitionCoefficient
        (M := M) S f g hfg
      have hc : (g.denominator : R) = (f.denominator : R) * c := by
        dsimp [c]
        exact (localizationStage_transition_formula (M := M) S f g hfg).choose_spec.1
      change LocalizedModule.mk (c ^ e • m)
          ⟨(g.denominator : R) ^ e,
            (Submonoid.mem_powers_iff _ _).2 ⟨e, rfl⟩⟩ = 0
      calc
        LocalizedModule.mk (c ^ e • m)
              ⟨(g.denominator : R) ^ e,
                (Submonoid.mem_powers_iff _ _).2 ⟨e, rfl⟩⟩ =
            LocalizedModule.mk
                (S := Submonoid.powers (g.denominator : R)) (M := M) 0
                (1 : Submonoid.powers (g.denominator : R)) := by
          apply LocalizedModule.mk_eq.mpr
          refine ⟨⟨(g.denominator : R),
            (Submonoid.mem_powers_iff _ _).2 ⟨1, by simp⟩⟩, ?_⟩
          simp only [one_smul, Submonoid.smul_def]
          have hu' : (u : R) • m = 0 := by
            simpa only [Submonoid.smul_def, one_smul, smul_zero] using hu
          simpa [g, smul_smul, mul_assoc, mul_comm, mul_left_comm] using
            congrArg (fun z : M => ((f.denominator : R) * c ^ e) • z) hu'
        _ = 0 := LocalizedModule.zero_mk
          (S := Submonoid.powers (g.denominator : R))
          (M := M) (1 : Submonoid.powers (g.denominator : R))
  have directLimitMap_surj : Function.Surjective directLimitMap := by
    intro x
    induction x using LocalizedModule.induction_on with
    | _ m s =>
      let f : LocalizationIndex S := ⟨s⟩
      refine ⟨Module.DirectLimit.of R (LocalizationIndex S) G transition f
          (localizationStageFraction S f m 1), ?_⟩
      rw [directLimitMap_of]
      rw [stageMap_fraction]
      change LocalizedModule.mk m _ = LocalizedModule.mk m s
      congr 1
      apply Subtype.ext
      simp [f]
  have directLimitMap_inj : Function.Injective directLimitMap := by
    intro x y hxy
    obtain ⟨f, z, w, rfl, rfl⟩ :=
      Module.DirectLimit.exists_of₂ (G := G) (f := transition) x y
    have hzw : stageMap f z = stageMap f w := by
      simpa [directLimitMap_of, stageMap'] using hxy
    have hzero : stageMap f (z - w) = 0 := by
      rw [map_sub, sub_eq_zero]
      exact hzw
    obtain ⟨g, hfg, hzero⟩ := kernel_eventual f (z - w) hzero
    have hzw' : transition f g hfg z = transition f g hfg w := by
      apply sub_eq_zero.mp
      simpa [map_sub, transition] using hzero
    calc
      Module.DirectLimit.of R (LocalizationIndex S) G transition f z =
          Module.DirectLimit.of R (LocalizationIndex S) G transition g
            (transition f g hfg z) := by
              symm
              apply Module.DirectLimit.of_f
      _ = Module.DirectLimit.of R (LocalizationIndex S) G transition g
            (transition f g hfg w) := congrArg _ hzw'
      _ = Module.DirectLimit.of R (LocalizationIndex S) G transition f w := by
            apply Module.DirectLimit.of_f
  let directLimitEquiv : directLimit ≃ₗ[R] localizedModule S M :=
    LinearEquiv.ofBijective directLimitMap
      ⟨directLimitMap_inj, directLimitMap_surj⟩
  let directLimitModuleIso : ModuleCat.of R directLimit ≅
      ModuleCat.of R (localizedModule S M) :=
    LinearEquiv.toModuleIso directLimitEquiv
  let colimitModuleIso : colimit (localizationStageFunctor S M) ≅
      ModuleCat.of R directLimit :=
    colimit.isoColimitCocone ⟨directLimitCocone, directLimitIsColimit⟩
  exact ⟨colimitModuleIso ≪≫ directLimitModuleIso⟩

/-! ## Products and iterated localization -/

/-- The product multiplicative subset, represented canonically by the sup of submonoids. -/
def localizationProduct {R : Type u} [CommRing R]
    (S S' : Submonoid R) : Submonoid R :=
  S ⊔ S'

theorem localizationProduct_mem_iff {R : Type u} [CommRing R]
    (S S' : Submonoid R) (x : R) :
    x ∈ localizationProduct S S' ↔
      ∃ s : S, ∃ s' : S', (s : R) * (s' : R) = x := by
  simpa [localizationProduct] using
    (Submonoid.mem_sup (s := S) (t := S') (x := x))

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
  let algA : Algebra R (localization (localizationImage S S')) :=
    RingHom.toAlgebra
      ((algebraMap (localization S') (localization (localizationImage S S'))).comp
        (algebraMap R (localization S')))
  let : Algebra R (localization (localizationImage S S')) := algA
  let : SMul R (localization (localizationImage S S')) := algA.toSMul
  let : IsScalarTower R (localization S') (localization (localizationImage S S')) :=
    IsScalarTower.of_algebraMap_eq' rfl
  let : Algebra (localization S') (localization (localizationProduct S S')) :=
    IsLocalization.localizationAlgebraOfSubmonoidLe
      (localization S') (localization (localizationProduct S S')) S'
        (localizationProduct S S') le_sup_right
  let : IsScalarTower R (localization S') (localization (localizationProduct S S')) :=
    IsLocalization.localization_isScalarTower_of_submonoid_le
      (localization S') (localization (localizationProduct S S')) S'
        (localizationProduct S S') le_sup_right
  let L : Submonoid R :=
    IsLocalization.localizationLocalizationSubmodule S' (localizationImage S S')
  have hA : IsLocalization L (localization (localizationImage S S')) := by
    exact IsLocalization.localization_localization_isLocalization S'
      (localizationImage S S') (localization (localizationImage S S'))
  have hPL : localizationProduct S S' ≤ L := by
    intro x hx
    change x ∈ IsLocalization.localizationLocalizationSubmodule S'
      (localizationImage S S')
    rcases (Submonoid.mem_sup.mp hx) with ⟨s, hs, t, ht, rfl⟩
    rw [IsLocalization.mem_localizationLocalizationSubmodule]
    refine ⟨localizationImageElement S S' ⟨s, hs⟩, ⟨t, ht⟩, ?_⟩
    simp [localizationImageElement, map_mul]
  have hdiv : ∀ x ∈ L, ∃ p ∈ localizationProduct S S', x ∣ p := by
    intro x hx
    change x ∈ IsLocalization.localizationLocalizationSubmodule S'
      (localizationImage S S') at hx
    rcases IsLocalization.mem_localizationLocalizationSubmodule.mp hx with
      ⟨y, z, hyz⟩
    rcases Submonoid.mem_map.mp y.property with ⟨s, hs, hsy⟩
    have heq : algebraMap R (localization S') x =
        algebraMap R (localization S') ((s : R) * (z : R)) := by
      rw [← hsy] at hyz
      simpa [map_mul] using hyz
    obtain ⟨c, hc⟩ := (IsLocalization.eq_iff_exists S' (localization S')).mp heq
    refine ⟨(s : R) * ((z : R) * (c : R)), ?_, ?_⟩
    · exact Submonoid.mul_mem_sup hs (S'.mul_mem z.property c.property)
    · refine ⟨c, ?_⟩
      calc
        (s : R) * ((z : R) * (c : R)) = (c : R) * ((s : R) * (z : R)) := by ring
        _ = (c : R) * x := by rw [hc]
        _ = x * (c : R) := by ring
  have hB : IsLocalization L (localization (localizationProduct S S')) := by
    exact (IsLocalization.iff_of_le_of_exists_dvd
      (M := localizationProduct S S')
      (S := localization (localizationProduct S S')) L hPL hdiv).mp
      (inferInstance : IsLocalization (localizationProduct S S')
        (localization (localizationProduct S S')))
  exact ⟨(IsLocalization.algEquiv L (localization (localizationImage S S'))
    (localization (localizationProduct S S'))).toRingEquiv⟩

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
  let : Algebra (localization S') (localization (localizationProduct S S')) :=
    IsLocalization.localizationAlgebraOfSubmonoidLe
      (localization S') (localization (localizationProduct S S')) S'
        (localizationProduct S S') le_sup_right
  let : IsScalarTower R (localization S') (localization (localizationProduct S S')) :=
    IsLocalization.localization_isScalarTower_of_submonoid_le
      (localization S') (localization (localizationProduct S S')) S'
        (localizationProduct S S') le_sup_right
  let Pmap : Submonoid (localization S') :=
    (localizationProduct S S').map (algebraMap R (localization S')).toMonoidHom
  have hPmap : IsLocalization Pmap (localization (localizationProduct S S')) := by
    exact IsLocalization.isLocalization_of_submonoid_le
      (localization S') (localization (localizationProduct S S')) S'
      (localizationProduct S S') le_sup_right
  have hNP : localizationImage S S' ≤ Pmap := by
    intro y hy
    rcases Submonoid.mem_map.mp hy with ⟨s, hs, rfl⟩
    exact Submonoid.mem_map_of_mem _ (Submonoid.mem_sup_left hs)
  have hdiv : ∀ y ∈ Pmap, ∃ x ∈ localizationImage S S', y ∣ x := by
    intro y hy
    rcases Submonoid.mem_map.mp hy with ⟨r, hr, rfl⟩
    rcases Submonoid.mem_sup.mp hr with ⟨s, hs, t, ht, rfl⟩
    refine ⟨algebraMap R (localization S') s,
      Submonoid.mem_map_of_mem _ hs, ?_⟩
    let ut : (localization S')ˣ :=
      (IsLocalization.map_units (localization S') ⟨t, ht⟩).unit
    let utInv : localization S' := (ut⁻¹).val
    refine ⟨utInv, ?_⟩
    change algebraMap R (localization S') s =
      algebraMap R (localization S') (s * t) * utInv
    rw [map_mul]
    change algebraMap R (localization S') s =
      algebraMap R (localization S') s * (ut : localization S') * utInv
    have hut : (ut : localization S') * utInv = 1 := by
      dsimp [utInv]
      simp
    rw [mul_assoc, hut, mul_one]
  have hN : IsLocalization (localizationImage S S')
      (localization (localizationProduct S S')) := by
    exact (IsLocalization.iff_of_le_of_exists_dvd
      (M := localizationImage S S') (S := localization (localizationProduct S S'))
        Pmap hNP hdiv).mpr hPmap
  let e : localization (localizationImage S S') ≃+*
      localization (localizationProduct S S') :=
    (IsLocalization.algEquiv (localizationImage S S')
      (localization (localizationImage S S'))
      (localization (localizationProduct S S'))).toRingEquiv
  have hforward : ∀ (x : R) (s : S) (s' : S'),
      e (localizationFraction (localizationImage S S')
          (localizationFraction S' x s') (localizationImageElement S S' s)) =
        localizationFraction (localizationProduct S S') x
          (localizationProductElement S S' s s') := by
    intro x s s'
    change e (Localization.mk (Localization.mk x s') (localizationImageElement S S' s)) =
      Localization.mk x (localizationProductElement S S' s s')
    dsimp [e]
    rw [Localization.mk_eq_mk', IsLocalization.algEquiv_mk']
    rw [Localization.mk_eq_mk', IsLocalization.mk'_eq_iff_eq_mul]
    rw [Localization.mk_eq_mk'_apply]
    apply (IsLocalization.map_units (M := localizationProduct S S')
      (localization (localizationProduct S S'))
      ⟨(s' : R), Submonoid.mem_sup_right s'.property⟩).mul_right_cancel
    calc
      (algebraMap (localization S') (localization (localizationProduct S S')))
          (IsLocalization.mk' (localization S') x s') *
          (algebraMap R (localization (localizationProduct S S'))) (s' : R) =
        (algebraMap (localization S') (localization (localizationProduct S S')))
          (IsLocalization.mk' (localization S') x s' *
            (algebraMap R (localization S')) (s' : R)) := by
          rw [map_mul, IsScalarTower.algebraMap_apply R (localization S')
            (localization (localizationProduct S S'))]
      _ = (algebraMap (localization S') (localization (localizationProduct S S')))
          ((algebraMap R (localization S')) x) := by
          rw [IsLocalization.mk'_spec]
      _ = (algebraMap R (localization (localizationProduct S S'))) x := by
          rw [IsScalarTower.algebraMap_apply R (localization S')
            (localization (localizationProduct S S'))]
      _ = IsLocalization.mk' (localization (localizationProduct S S')) x
            (localizationProductElement S S' s s') *
          (algebraMap R (localization (localizationProduct S S')))
            (localizationProductElement S S' s s' : R) := by
          symm
          exact IsLocalization.mk'_spec _ _ _
      _ = IsLocalization.mk' (localization (localizationProduct S S')) x
            (localizationProductElement S S' s s') *
          (algebraMap (localization S') (localization (localizationProduct S S')))
            (localizationImageElement S S' s : localization S') *
          (algebraMap R (localization (localizationProduct S S'))) (s' : R) := by
          rw [mul_assoc]
          congr 1
          change (algebraMap R (localization (localizationProduct S S')))
              ((s : R) * (s' : R)) =
            (algebraMap (localization S') (localization (localizationProduct S S')))
                ((algebraMap R (localization S')) (s : R)) *
              (algebraMap R (localization (localizationProduct S S'))) (s' : R)
          rw [map_mul, IsScalarTower.algebraMap_apply R (localization S')
            (localization (localizationProduct S S'))]
  refine ⟨e, hforward, ?_⟩
  intro x s s'
  apply e.injective
  rw [e.apply_symm_apply]
  exact (hforward x s s').symm

theorem localizedModule_iterated_equiv {R : Type u} [CommRing R]
    (S S' : Submonoid R) {M : Type v} [AddCommGroup M] [Module R M] :
    Nonempty (localizedModule S (localizedModule S' M) ≃ₗ[R]
      localizedModule (localizationProduct S S') M) := by
  let inner := localizedModule S' M
  let outer := localizedModule S inner
  let P := localizationProduct S S'
  let f : M →ₗ[R] outer :=
    (localizedModuleMap S inner).comp (localizedModuleMap S' M)
  have hS' : ∀ s' : S', Function.Bijective
      (fun x : outer => (s' : R) • x) := by
    intro s'
    let q : inner →ₗ[R] inner :=
      algebraMap R (Module.End R inner) (s' : R)
    have hq : Function.Bijective q := by
      exact (Module.End.isUnit_iff _).mp
        (IsLocalizedModule.map_units (LocalizedModule.mkLinearMap S' M) s')
    have hmap_eq :
        (LocalizedModule.map S q).restrictScalars R =
          algebraMap R (Module.End R outer) (s' : R) := by
      ext z
      induction z using LocalizedModule.induction_on with
      | _ m s =>
        change (LocalizedModule.map S q) (LocalizedModule.mk m s) =
          (algebraMap R (Module.End R outer) (s' : R))
            (LocalizedModule.mk m s)
        rw [LocalizedModule.map_mk]
        change LocalizedModule.mk ((s' : R) • m) s =
          (s' : R) • LocalizedModule.mk m s
        rw [LocalizedModule.smul'_mk]
    have hmap_bij : Function.Bijective
        ((LocalizedModule.map S q).restrictScalars R) := by
      exact ⟨LocalizedModule.map_injective S q hq.1,
        LocalizedModule.map_surjective S q hq.2⟩
    rw [hmap_eq] at hmap_bij
    have hscalar :
        (fun x : outer => (s' : R) • x) =
          (algebraMap R (Module.End R outer) (s' : R)) := by
      funext x
      simp [Module.algebraMap_end_apply]
    rw [hscalar]
    exact hmap_bij
  have hEnd : ∀ p : P, IsUnit (algebraMap R (Module.End R outer) (p : R)) := by
    intro p
    rcases Submonoid.mem_sup.mp p.property with ⟨s, hs, s', hs', hp⟩
    rw [← hp]
    apply (Module.End.isUnit_iff _).mpr
    have hs_bij : Function.Bijective (fun x : outer => (s : R) • x) := by
      have hs_bij' := (Module.End.isUnit_iff _).mp
        (IsLocalizedModule.map_units (LocalizedModule.mkLinearMap S inner) ⟨s, hs⟩)
      have hs_fun :
          (algebraMap R (Module.End R outer) (s : R) : outer → outer) =
            (fun x : outer => (s : R) • x) := by
        funext x
        simp [outer, Module.algebraMap_end_apply]
      rw [hs_fun] at hs_bij'
      exact hs_bij'
    have hs'_bij : Function.Bijective (fun x : outer => (s' : R) • x) :=
      hS' ⟨s', hs'⟩
    have hfun :
        (algebraMap R (Module.End R outer) (s * s') : outer → outer) =
          (fun x : outer => (s : R) • ((s' : R) • x)) := by
      funext x
      simp [Module.algebraMap_end_apply, smul_smul, mul_comm]
    rw [hfun]
    exact hs_bij.comp hs'_bij
  have hSource : IsLocalizedModule P f := by
    refine { map_units := hEnd, surj := ?_, exists_of_eq := ?_ }
    · intro y
      induction y using LocalizedModule.induction_on with
      | _ z s =>
        induction z using LocalizedModule.induction_on with
        | _ m s' =>
          refine ⟨⟨m, localizationProductElement S S' s s'⟩, ?_⟩
          change ((s : R) * (s' : R)) •
              LocalizedModule.mk (LocalizedModule.mk m s') s =
            LocalizedModule.mk (LocalizedModule.mk m 1) 1
          calc
            ((s : R) * (s' : R)) •
                LocalizedModule.mk (LocalizedModule.mk m s') s =
                LocalizedModule.mk
                  (((s : R) * (s' : R)) • LocalizedModule.mk m s') s := by
              rw [LocalizedModule.smul'_mk]
            _ =
                LocalizedModule.mk
                  ((s : R) • ((s' : R) • LocalizedModule.mk m s')) s := by
              congr 1
              rw [mul_smul]
            _ = LocalizedModule.mk ((s' : R) • LocalizedModule.mk m s') 1 := by
              exact LocalizedModule.mk_cancel s ((s' : R) • LocalizedModule.mk m s')
            _ = LocalizedModule.mk (LocalizedModule.mk m 1) 1 := by
              rw [LocalizedModule.smul'_mk (S := S')]
              congr 1
              exact LocalizedModule.mk_cancel s' m
    · intro m₁ m₂ h
      change LocalizedModule.mk (LocalizedModule.mk m₁ 1) 1 =
        LocalizedModule.mk (LocalizedModule.mk m₂ 1) 1 at h
      obtain ⟨s, hs⟩ := LocalizedModule.mk_eq.mp h
      have hinner : LocalizedModule.mk (S := S') ((s : R) • m₁) (1 : S') =
          LocalizedModule.mk (S := S') ((s : R) • m₂) (1 : S') := by
        simpa [Submonoid.smul_def, ← LocalizedModule.smul'_mk] using hs
      obtain ⟨s', hs'⟩ := LocalizedModule.mk_eq.mp hinner
      refine ⟨localizationProductElement S S' s s', ?_⟩
      simpa [localizationProductElement, Submonoid.smul_def, smul_smul,
        mul_comm, mul_left_comm, mul_assoc] using hs'
  let : IsLocalizedModule P f := hSource
  exact ⟨IsLocalizedModule.linearEquiv P f (LocalizedModule.mkLinearMap P M)⟩

private theorem localizedModule_iterated_isLocalized {R : Type u} [CommRing R]
    (S S' : Submonoid R) {M : Type v} [AddCommGroup M] [Module R M] :
    IsLocalizedModule (localizationProduct S S')
      ((localizedModuleMap S (localizedModule S' M)).comp
        (localizedModuleMap S' M)) := by
  let inner := localizedModule S' M
  let outer := localizedModule S inner
  let P := localizationProduct S S'
  let f : M →ₗ[R] outer :=
    (localizedModuleMap S inner).comp (localizedModuleMap S' M)
  have hS' : ∀ s' : S', Function.Bijective
      (fun x : outer => (s' : R) • x) := by
    intro s'
    let q : inner →ₗ[R] inner :=
      algebraMap R (Module.End R inner) (s' : R)
    have hq : Function.Bijective q := by
      exact (Module.End.isUnit_iff _).mp
        (IsLocalizedModule.map_units (LocalizedModule.mkLinearMap S' M) s')
    have hmap_eq :
        (LocalizedModule.map S q).restrictScalars R =
          algebraMap R (Module.End R outer) (s' : R) := by
      ext z
      induction z using LocalizedModule.induction_on with
      | _ m s =>
        change (LocalizedModule.map S q) (LocalizedModule.mk m s) =
          (algebraMap R (Module.End R outer) (s' : R))
            (LocalizedModule.mk m s)
        rw [LocalizedModule.map_mk]
        change LocalizedModule.mk ((s' : R) • m) s =
          (s' : R) • LocalizedModule.mk m s
        rw [LocalizedModule.smul'_mk]
    have hmap_bij : Function.Bijective
        ((LocalizedModule.map S q).restrictScalars R) := by
      exact ⟨LocalizedModule.map_injective S q hq.1,
        LocalizedModule.map_surjective S q hq.2⟩
    rw [hmap_eq] at hmap_bij
    have hscalar :
        (fun x : outer => (s' : R) • x) =
          (algebraMap R (Module.End R outer) (s' : R)) := by
      funext x
      simp [Module.algebraMap_end_apply]
    rw [hscalar]
    exact hmap_bij
  have hEnd : ∀ p : P, IsUnit (algebraMap R (Module.End R outer) (p : R)) := by
    intro p
    rcases Submonoid.mem_sup.mp p.property with ⟨s, hs, s', hs', hp⟩
    rw [← hp]
    apply (Module.End.isUnit_iff _).mpr
    have hs_bij : Function.Bijective (fun x : outer => (s : R) • x) := by
      have hs_bij' := (Module.End.isUnit_iff _).mp
        (IsLocalizedModule.map_units (LocalizedModule.mkLinearMap S inner) ⟨s, hs⟩)
      have hs_fun :
          (algebraMap R (Module.End R outer) (s : R) : outer → outer) =
            (fun x : outer => (s : R) • x) := by
        funext x
        simp [outer, Module.algebraMap_end_apply]
      rw [hs_fun] at hs_bij'
      exact hs_bij'
    have hs'_bij : Function.Bijective (fun x : outer => (s' : R) • x) :=
      hS' ⟨s', hs'⟩
    have hfun :
        (algebraMap R (Module.End R outer) (s * s') : outer → outer) =
          (fun x : outer => (s : R) • ((s' : R) • x)) := by
      funext x
      simp [Module.algebraMap_end_apply, smul_smul, mul_comm]
    rw [hfun]
    exact hs_bij.comp hs'_bij
  have hSource : IsLocalizedModule P f := by
    refine { map_units := hEnd, surj := ?_, exists_of_eq := ?_ }
    · intro y
      induction y using LocalizedModule.induction_on with
      | _ z s =>
        induction z using LocalizedModule.induction_on with
        | _ m s' =>
          refine ⟨⟨m, localizationProductElement S S' s s'⟩, ?_⟩
          change ((s : R) * (s' : R)) •
              LocalizedModule.mk (LocalizedModule.mk m s') s =
            LocalizedModule.mk (LocalizedModule.mk m 1) 1
          calc
            ((s : R) * (s' : R)) •
                LocalizedModule.mk (LocalizedModule.mk m s') s =
                LocalizedModule.mk
                  (((s : R) * (s' : R)) • LocalizedModule.mk m s') s := by
              rw [LocalizedModule.smul'_mk]
            _ =
                LocalizedModule.mk
                  ((s : R) • ((s' : R) • LocalizedModule.mk m s')) s := by
              congr 1
              rw [mul_smul]
            _ = LocalizedModule.mk ((s' : R) • LocalizedModule.mk m s') 1 := by
              exact LocalizedModule.mk_cancel s ((s' : R) • LocalizedModule.mk m s')
            _ = LocalizedModule.mk (LocalizedModule.mk m 1) 1 := by
              rw [LocalizedModule.smul'_mk (S := S')]
              congr 1
              exact LocalizedModule.mk_cancel s' m
    · intro m₁ m₂ h
      change LocalizedModule.mk (LocalizedModule.mk m₁ 1) 1 =
        LocalizedModule.mk (LocalizedModule.mk m₂ 1) 1 at h
      obtain ⟨s, hs⟩ := LocalizedModule.mk_eq.mp h
      have hinner : LocalizedModule.mk (S := S') ((s : R) • m₁) (1 : S') =
          LocalizedModule.mk (S := S') ((s : R) • m₂) (1 : S') := by
        simpa [Submonoid.smul_def, ← LocalizedModule.smul'_mk] using hs
      obtain ⟨s', hs'⟩ := LocalizedModule.mk_eq.mp hinner
      refine ⟨localizationProductElement S S' s s', ?_⟩
      simpa [localizationProductElement, Submonoid.smul_def, smul_smul,
        mul_comm, mul_left_comm, mul_assoc] using hs'
  exact hSource

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
  let P := localizationProduct S S'
  let f : M →ₗ[R] localizedModule S (localizedModule S' M) :=
    (localizedModuleMap S (localizedModule S' M)).comp
      (localizedModuleMap S' M)
  let g : M →ₗ[R] localizedModule P M := LocalizedModule.mkLinearMap P M
  let : IsLocalizedModule P f := localizedModule_iterated_isLocalized S S'
  let e : localizedModule S (localizedModule S' M) ≃ₗ[R]
      localizedModule P M := IsLocalizedModule.linearEquiv P f g
  have he_mk : ∀ (m : M) (p : P),
      e (IsLocalizedModule.mk' f m p) =
        IsLocalizedModule.mk' g m p := by
    intro m p
    symm
    apply (IsLocalizedModule.mk'_eq_iff (f := g)).mpr
    have hsource : f m = (p : R) • IsLocalizedModule.mk' f m p :=
      (IsLocalizedModule.mk'_eq_iff (f := f)).mp rfl
    rw [← IsLocalizedModule.linearEquiv_apply P f g m]
    change e (f m) = (p : R) • e (IsLocalizedModule.mk' f m p)
    rw [← e.map_smul, hsource]
  have hfrac : ∀ (m : M) (s : S) (s' : S'),
      localizedModuleFraction S (localizedModuleFraction S' m s') s =
        IsLocalizedModule.mk' f m (localizationProductElement S S' s s') := by
    intro m s s'
    symm
    apply (IsLocalizedModule.mk'_eq_iff (f := f)).mpr
    change LocalizedModule.mk (LocalizedModule.mk m 1) 1 =
      ((s : R) * (s' : R)) •
        LocalizedModule.mk (LocalizedModule.mk m s') s
    symm
    calc
      ((s : R) * (s' : R)) •
          LocalizedModule.mk (LocalizedModule.mk m s') s =
          LocalizedModule.mk
            (((s : R) * (s' : R)) • LocalizedModule.mk m s') s := by
        rw [LocalizedModule.smul'_mk]
      _ = LocalizedModule.mk
          ((s : R) • ((s' : R) • LocalizedModule.mk m s')) s := by
        congr 1
        rw [mul_smul]
      _ = LocalizedModule.mk ((s' : R) • LocalizedModule.mk m s') 1 := by
        exact LocalizedModule.mk_cancel s ((s' : R) • LocalizedModule.mk m s')
      _ = LocalizedModule.mk (LocalizedModule.mk m 1) 1 := by
        rw [LocalizedModule.smul'_mk (S := S')]
        congr 1
        exact LocalizedModule.mk_cancel s' m
  have hforward : ∀ (m : M) (s : S) (s' : S'),
      e (localizedModuleFraction S
          (localizedModuleFraction S' m s') s) =
        localizedModuleFraction P m (localizationProductElement S S' s s') := by
    intro m s s'
    rw [hfrac, he_mk]
    exact (IsLocalizedModule.mk_eq_mk' (S := P)
      (localizationProductElement S S' s s') m).symm
  refine ⟨e, hforward, ?_⟩
  intro m s s'
  apply e.injective
  rw [e.apply_symm_apply]
  exact (hforward m s s').symm

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
  simp [localizedLinearMap, localizedModuleFraction]

theorem localizedLinearMap_id {R : Type u} [CommRing R] (S : Submonoid R)
    {M : Type v} [AddCommGroup M] [Module R M] :
    localizedLinearMap S (LinearMap.id : M →ₗ[R] M) = LinearMap.id := by
  unfold localizedLinearMap
  exact LocalizedModule.map_id S

theorem localizedLinearMap_comp {R : Type u} [CommRing R]
    (S : Submonoid R) {L M N : Type v} [AddCommGroup L] [AddCommGroup M]
    [AddCommGroup N] [Module R L] [Module R M] [Module R N]
    (u : L →ₗ[R] M) (v : M →ₗ[R] N) :
    localizedLinearMap S (v.comp u) =
      (localizedLinearMap S v).comp (localizedLinearMap S u) := by
  ext x
  induction x using LocalizedModule.induction_on with
  | _ m s => simp [localizedLinearMap]

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
  exact LocalizedModule.map_exact S u w h

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
  exact ⟨(localizedQuotientEquiv S N).symm⟩

theorem localizedQuotientModule_equiv_formula {R : Type u} [CommRing R]
    (S : Submonoid R) {M : Type v} [AddCommGroup M] [Module R M]
    (N : Submodule R M) :
    ∃ e : localizedModule S (M ⧸ N) ≃ₗ[localization S]
        localizedModule S M ⧸ localizedSubmodule S N,
      ∀ (m : M) (s : S),
        e (localizedModuleFraction S (Submodule.Quotient.mk m) s) =
          Submodule.Quotient.mk (localizedModuleFraction S m s) := by
  refine ⟨(localizedQuotientEquiv S N).symm, ?_⟩
  intro m s
  have hfracM : localizedModuleFraction S m s =
      (localizationFraction S (1 : R) s) • localizedModuleFraction S m 1 := by
    simpa [localizedModuleFraction, localizationFraction] using
      (LocalizedModule.mk_smul_mk (S := S) (r := 1) (m := m) s 1).symm
  have hfracQ : localizedModuleFraction S (Submodule.Quotient.mk (p := N) m) s =
      (localizationFraction S (1 : R) s) •
        localizedModuleFraction S (Submodule.Quotient.mk (p := N) m) 1 := by
    simpa [localizedModuleFraction, localizationFraction] using
      (LocalizedModule.mk_smul_mk (S := S) (r := 1)
        (m := Submodule.Quotient.mk (p := N) m) s 1).symm
  apply (localizedQuotientEquiv S N).injective
  rw [(localizedQuotientEquiv S N).apply_symm_apply, hfracQ, hfracM,
    Submodule.Quotient.mk_smul, map_smul]
  congr 1
  change LocalizedModule.mk (Submodule.Quotient.mk (p := N) m) 1 =
    (IsLocalizedModule.linearEquiv S (Submodule.toLocalizedQuotient S N)
      (LocalizedModule.mkLinearMap S (M ⧸ N)))
      (Submodule.Quotient.mk (LocalizedModule.mk m 1))
  exact (IsLocalizedModule.linearEquiv_apply S
    (Submodule.toLocalizedQuotient S N)
    (LocalizedModule.mkLinearMap S (M ⧸ N)) (Submodule.Quotient.mk m)).symm

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
  let : Algebra (A ⧸ I) (localization S ⧸ localizedIdeal S I) :=
    Ideal.Quotient.algebraQuotientOfLEComap Ideal.le_comap_map
  let : IsLocalization (quotientLocalizationSubmonoid I S)
      (localization S ⧸ localizedIdeal S I) := by
    change IsLocalization (Algebra.algebraMapSubmonoid (A ⧸ I) S)
      (localization S ⧸ localizedIdeal S I)
    exact IsLocalization.of_surjective S (localization S)
      (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
      (Ideal.Quotient.mk (localizedIdeal S I)) Ideal.Quotient.mk_surjective rfl (by
        rw [Ideal.mk_ker, Ideal.mk_ker]
        exact le_rfl)
  exact ⟨(IsLocalization.algEquiv
    (quotientLocalizationSubmonoid I S)
    (localization (quotientLocalizationSubmonoid I S))
    (localization S ⧸ localizedIdeal S I)).toRingEquiv⟩

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
  let : Algebra (A ⧸ I) (localization S ⧸ localizedIdeal S I) :=
    Ideal.Quotient.algebraQuotientOfLEComap Ideal.le_comap_map
  let : IsLocalization (quotientLocalizationSubmonoid I S)
      (localization S ⧸ localizedIdeal S I) := by
    change IsLocalization (Algebra.algebraMapSubmonoid (A ⧸ I) S)
      (localization S ⧸ localizedIdeal S I)
    exact IsLocalization.of_surjective S (localization S)
      (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
      (Ideal.Quotient.mk (localizedIdeal S I)) Ideal.Quotient.mk_surjective rfl (by
        rw [Ideal.mk_ker, Ideal.mk_ker]
        exact le_rfl)
  have hS : S ≤ (quotientLocalizationSubmonoid I S).comap
      (Ideal.Quotient.mk I) := by
    intro s hs
    exact Submonoid.mem_map_of_mem (Ideal.Quotient.mk I).toMonoidHom hs
  have hmap : IsLocalization.map (localization S ⧸ localizedIdeal S I)
      (Ideal.Quotient.mk I) hS = Ideal.Quotient.mk (localizedIdeal S I) := by
    apply IsLocalization.map_unique
    intro x
    change (Ideal.Quotient.mk (Ideal.map (algebraMap A (localization S)) I))
        (algebraMap A (localization S) x) =
      algebraMap (A ⧸ I)
        (localization S ⧸ Ideal.map (algebraMap A (localization S)) I)
        (Ideal.Quotient.mk I x)
    rw [Ideal.Quotient.algebraMap_quotient_map_quotient]
  let e : localization (quotientLocalizationSubmonoid I S) ≃+*
      localization S ⧸ localizedIdeal S I :=
    (Localization.algEquiv (quotientLocalizationSubmonoid I S)
      (localization S ⧸ localizedIdeal S I)).toRingEquiv
  have hforward : ∀ (x : A) (s : S),
      e (localizationFraction (quotientLocalizationSubmonoid I S)
          (Ideal.Quotient.mk I x) (quotientLocalizationElement I S s)) =
        Ideal.Quotient.mk (localizedIdeal S I) (localizationFraction S x s) := by
    intro x s
    change (Localization.algEquiv (quotientLocalizationSubmonoid I S)
        (localization S ⧸ localizedIdeal S I))
        (Localization.mk (Ideal.Quotient.mk I x)
          (quotientLocalizationElement I S s)) = _
    rw [Localization.algEquiv_mk]
    have hmk := IsLocalization.map_mk'
      (M := S) (S := localization S)
      (T := quotientLocalizationSubmonoid I S)
      (Q := localization S ⧸ localizedIdeal S I)
      (g := Ideal.Quotient.mk I) hS x s
    calc
      IsLocalization.mk' (localization S ⧸ localizedIdeal S I)
          (Ideal.Quotient.mk I x) (quotientLocalizationElement I S s) =
          IsLocalization.map (localization S ⧸ localizedIdeal S I)
            (Ideal.Quotient.mk I) hS
            (IsLocalization.mk' (localization S) x s) := by
        symm
        simpa [quotientLocalizationElement] using hmk
      _ = Ideal.Quotient.mk (localizedIdeal S I) (localizationFraction S x s) := by
        rw [hmap]
        exact congrArg (Ideal.Quotient.mk (localizedIdeal S I))
          (Localization.mk_eq_mk'_apply x s).symm
  refine ⟨e, hforward, ?_⟩
  intro x s
  apply e.injective
  rw [e.apply_symm_apply]
  exact (hforward x s).symm

/-! ## Submodules and ideals of a localization -/

def submoduleLocalizationPreimage {R : Type u} [CommRing R]
    (S : Submonoid R) {M : Type v} [AddCommGroup M] [Module R M]
    (N' : Submodule (localization S) (localizedModule S M)) : Submodule R M :=
  (N'.restrictScalars R).comap (localizedModuleMap S M)

theorem submodule_localization_eq {R : Type u} [CommRing R]
    (S : Submonoid R) {M : Type v} [AddCommGroup M] [Module R M]
    (N' : Submodule (localization S) (localizedModule S M)) :
    localizedSubmodule S (submoduleLocalizationPreimage S N') = N' := by
  dsimp only [localizedSubmodule, submoduleLocalizationPreimage, Submodule.localized,
    localizedModuleMap]
  apply le_antisymm
  · exact ((Submodule.localized'gi (Localization S) S (LocalizedModule.mkLinearMap S M)).gc
      _ _).mpr le_rfl
  · exact (Submodule.localized'gi (Localization S) S (LocalizedModule.mkLinearMap S M)).le_l_u N'

theorem ideal_localization_eq {A : Type u} [CommRing A] (S : Submonoid A)
    (J : Ideal (localization S)) :
    localizedIdeal S (idealLocalizationPreimage S J) = J :=
  localizedIdeal_under S J

end

end Formalization.Books.Algebra.Unit09
