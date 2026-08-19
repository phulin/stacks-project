import Formalization.Books.MoreAlgebra.Unit89
import Formalization.Books.MoreAlgebra.Unit74.DerivedHom
import Formalization.Books.MoreAlgebra.Unit65.PseudoCoherentModules
import Formalization.Books.Derived.Unit34.DerivedLimits
import Formalization.Books.Derived.Unit06.Quotients
import Formalization.Books.Homology.Unit24.FilteredComplexes
import Formalization.Books.Algebra.Unit71.ExtGroups
import Mathlib.RingTheory.AdicCompletion.Basic
import Mathlib.Algebra.Module.LocalizedModule.Basic

/-!
# More on Algebra, Chapter 92: Derived completion

This file records the definitions and theorem interfaces in the section on
derived completion.  The derived-category operations are the canonical ones
from the preceding chapters.  A few constructions used by the source (the
scalar-action inverse system, the alternating Cech complex, and restriction
of derived categories) are packaged as small data structures because the
current project API does not yet expose those constructions directly.
-/

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Preadditive
open CategoryTheory.Pretriangulated
open CategoryTheory.Triangulated
open Formalization.Books.MoreAlgebra.Unit67
open Formalization.Books.MoreAlgebra.Unit74
open Formalization.Books.MoreAlgebra.Unit89
open Formalization.Books.Derived.Unit06
open Formalization.Books.Derived.Unit34
open Formalization.Books.Homology.Unit24
open scoped BigOperators CategoryTheory.Pretriangulated.Opposite ZeroObject

universe u v w

namespace Formalization.Books.MoreAlgebra.Unit92

abbrev Mod (A : Type u) [CommRing A] := ModuleCat.{u} A

abbrev Comp (A : Type u) [CommRing A] := CochainComplex (Mod A) ℤ

abbrev D (A : Type u) [CommRing A]
    [HasDerivedCategory.{w} (Mod A)] := DerivedCategory (Mod A)

/-! ## The scalar inverse system and `T(K, f)` -/

def HomVanishes {C : Type v} [Category.{u, v} C] [Preadditive C] (X Y : C) : Prop :=
  ∀ g : X ⟶ Y, g = 0

def localizedModule (A : Type u) [CommRing A] (f : A) : Mod A :=
  ModuleCat.of A (Localization.Away f)

noncomputable abbrev derivedExt {A : Type u} [CommRing A]
    [HasDerivedCategory.{w} (Mod A)] (f : A) (K : D A) (n : ℤ) : Mod A :=
  (derivedCohomology A n).obj
    (RHom (moduleInDerived A (localizedModule A f)) K)

def homModule {A : Type u} [CommRing A] (M N : Mod A) : Mod A :=
  ModuleCat.of A (M ⟶ N)

noncomputable def derivedExtE₂Page {A : Type u} [CommRing A]
    [HasDerivedCategory.{w} (Mod A)]
    (f : A) (K : D A) (p q : ℤ) : Mod A :=
  Formalization.Books.Algebra.Unit71.ExtModuleZ (localizedModule A f)
    ((derivedCohomology A q).obj K) p

/- The degeneration of the two-column Ext spectral sequence gives the short
   exact sequence displayed in the source.  The morphisms are kept as fields
   so this interface does not assume a comparison-map name absent from the
   preceding Ext API. -/
structure DerivedExtShortExactData {A : Type u} [CommRing A]
    [HasDerivedCategory.{w} (Mod A)] (f : A) (K : D A) (p : ℤ) where
  left : Formalization.Books.Algebra.Unit71.ExtModule
      (localizedModule A f) ((derivedCohomology A (p - 1)).obj K) 1 ⟶
    derivedExt f K p
  right : derivedExt f K p ⟶
    homModule (localizedModule A f) ((derivedCohomology A p).obj K)
  zero : left ≫ right = 0
  exact : CategoryTheory.ShortComplex.ShortExact
    { f := left, g := right, zero := zero }

theorem exists_derivedExt_shortExactData {A : Type u} [CommRing A]
    [HasDerivedCategory.{w} (Mod A)] (f : A) (K : D A) (p : ℤ) :
    Nonempty (DerivedExtShortExactData f K p) := by
  sorry

/- The scalar action on an arbitrary object of the derived category is
   mathematically canonical, but a natural-transformation API for this action
   is not currently available in the project. -/
structure DerivedScalarActionData (A : Type u) [CommRing A]
    [HasDerivedCategory.{w} (Mod A)] where
  map : ∀ (f : A) (K : D A), K ⟶ K
  map_one : ∀ K, map 1 K = 𝟙 K
  map_mul : ∀ f g K, map (f * g) K = map f K ≫ map g K
  map_zero : ∀ K, map 0 K = 0
  map_add : ∀ f g K, map (f + g) K = map f K + map g K

theorem exists_derivedScalarActionData (A : Type u) [CommRing A]
    [HasDerivedCategory.{w} (Mod A)] : Nonempty (DerivedScalarActionData A) := by
  sorry

noncomputable def derivedScalarMap {A : Type u} [CommRing A]
    [HasDerivedCategory.{w} (Mod A)] (f : A) (K : D A) : K ⟶ K :=
  (Classical.choice (exists_derivedScalarActionData A)).map f K

structure DerivedScalarSystemData (A : Type u) [CommRing A]
    [HasDerivedCategory.{w} (Mod A)] (f : A) (K : D A) where
  system : DerivedInverseSystem (D A)
  object_eq : ∀ n : ℕ, system.obj (Opposite.op n) = K
  transition_eq : ∀ n : ℕ,
    system.map (opHomOfLE (Nat.le_succ n)) =
      eqToHom (object_eq (n + 1)) ≫ derivedScalarMap f K ≫
        eqToHom (object_eq n).symm
  hasProduct : HasProduct (fun n : ℕ => system.obj (Opposite.op n))

theorem exists_derivedScalarSystemData (A : Type u) [CommRing A]
    [HasDerivedCategory.{w} (Mod A)] (f : A) (K : D A) :
    Nonempty (DerivedScalarSystemData A f K) := by
  sorry

noncomputable def derivedScalarSystemData {A : Type u} [CommRing A]
    [HasDerivedCategory.{w} (Mod A)] (f : A) (K : D A) :
    DerivedScalarSystemData A f K :=
  Classical.choice (exists_derivedScalarSystemData A f K)

noncomputable abbrev derivedScalarSystem {A : Type u} [CommRing A]
    [HasDerivedCategory.{w} (Mod A)] (f : A) (K : D A) :
    DerivedInverseSystem (D A) :=
  (derivedScalarSystemData f K).system

noncomputable def derivedLimitWithProduct {A : Type u} [CommRing A]
    [HasDerivedCategory.{w} (Mod A)] (F : DerivedInverseSystem (D A))
    (hF : HasProduct (fun n : ℕ => F.obj (Opposite.op n))) : D A :=
  letI := hF
  derivedLimit F (exists_isDerivedLimit F)

noncomputable def derivedScalarLimit {A : Type u} [CommRing A]
    [HasDerivedCategory.{w} (Mod A)] (f : A) (K : D A) : D A :=
  let S := derivedScalarSystemData f K
  derivedLimitWithProduct S.system S.hasProduct

/- The source's `T(K, f)`. -/
noncomputable abbrev T {A : Type u} [CommRing A]
    [HasDerivedCategory.{w} (Mod A)] (K : D A) (f : A) : D A :=
  derivedScalarLimit f K

noncomputable def scalarProductDifferenceMap {A : Type u} [CommRing A]
    [HasDerivedCategory.{w} (Mod A)] (f : A) (K : D A) :
    (∏ᶜ fun n : ℕ => (derivedScalarSystem f K).obj (Opposite.op n)) ⟶
      (∏ᶜ fun n : ℕ => (derivedScalarSystem f K).obj (Opposite.op n)) :=
  let S := derivedScalarSystemData f K
  letI := S.hasProduct
  inverseSystemDifferenceMap S.system (productPresentation S.system)

structure DerivedLocalizationRestrictionData (A : Type u) [CommRing A]
    [HasDerivedCategory.{w} (Mod A)] (f : A)
    [HasDerivedCategory.{w} (Mod (Localization.Away f))] where
  functor : D (Localization.Away f) ⥤ D A

theorem exists_derivedLocalizationRestrictionData (A : Type u) [CommRing A]
    [HasDerivedCategory.{w} (Mod A)] (f : A)
    [HasDerivedCategory.{w} (Mod (Localization.Away f))] :
    Nonempty (DerivedLocalizationRestrictionData A f) := by
  sorry

noncomputable def derivedLocalizationRestriction {A : Type u} [CommRing A]
    [HasDerivedCategory.{w} (Mod A)] (f : A)
    [HasDerivedCategory.{w} (Mod (Localization.Away f))] :
    D (Localization.Away f) ⥤ D A :=
  (Classical.choice (exists_derivedLocalizationRestrictionData A f)).functor

/- The first lemma of the section.  The eighth source item is literally the
   placeholder “add more here” and is intentionally not turned into a false
   theorem. -/
theorem derived_localization_vanishing_iff {A : Type u} [CommRing A]
    [HasDerivedCategory.{w} (Mod A)] (f : A)
    [HasDerivedCategory.{w} (Mod (Localization.Away f))] (K : D A) :
    List.TFAE
      [∀ n : ℤ, IsZero (derivedExt f K n),
       ∀ E : D (Localization.Away f),
         HomVanishes ((derivedLocalizationRestriction f).obj E) K,
       IsZero (T K f),
       ∀ p : ℤ,
         IsZero (T (moduleInDerived A ((derivedCohomology A p).obj K)) f),
       ∀ p : ℤ,
         HomVanishes (localizedModule A f) ((derivedCohomology A p).obj K) ∧
           IsZero (Formalization.Books.Algebra.Unit71.ExtModule (localizedModule A f)
             ((derivedCohomology A p).obj K) 1),
       IsZero (RHom (moduleInDerived A (localizedModule A f)) K),
       IsIso (scalarProductDifferenceMap f K)] := by
  sorry

/-! ## Derived completeness and ordinary adic completeness -/

def derivedComplete {A : Type u} [CommRing A]
    [HasDerivedCategory.{w} (Mod A)] (I : Ideal A) (K : D A) : Prop :=
  ∀ f : A, f ∈ I → IsZero (T K f)

def derivedCompleteModule {A : Type u} [CommRing A]
    [HasDerivedCategory.{w} (Mod A)] (I : Ideal A) (M : Mod A) : Prop :=
  derivedComplete I (moduleInDerived A M)

def derivedCompleteElements {A : Type u} [CommRing A]
    [HasDerivedCategory.{w} (Mod A)] (K : D A) : Set A :=
  {f | IsZero (T K f)}

theorem derivedCompleteElements_is_radicalIdeal {A : Type u} [CommRing A]
    [HasDerivedCategory.{w} (Mod A)] (K : D A) :
    ∃ J : Ideal A, J.IsRadical ∧ (J : Set A) = derivedCompleteElements K := by
  sorry

def moduleBinaryProduct {A : Type u} [CommRing A] (M N : Mod A) : Mod A :=
  M ⊞ N

structure LocalizationCoverShortExactData {A : Type u} [CommRing A]
    (f g : A) where
  left : localizedModule A (f + g) ⟶
    moduleBinaryProduct
      (localizedModule A (f * (f + g)))
      (localizedModule A (g * (f + g)))
  right : moduleBinaryProduct
      (localizedModule A (f * (f + g)))
      (localizedModule A (g * (f + g))) ⟶
    localizedModule A (g * f * (f + g))
  zero : left ≫ right = 0
  exact : CategoryTheory.ShortComplex.ShortExact
    { f := left, g := right, zero := zero }

theorem exists_localizationCoverShortExactData {A : Type u} [CommRing A]
    (f g : A) : Nonempty (LocalizationCoverShortExactData f g) := by
  sorry

theorem derived_complete_of_adic_complete {A : Type u} [CommRing A]
    [HasDerivedCategory.{w} (Mod A)] (I : Ideal A) (M : Mod A)
    [IsAdicComplete I (M : Type u)] :
    derivedCompleteModule I M := by
  sorry

theorem derived_complete_completion_surjective {A : Type u} [CommRing A]
    [HasDerivedCategory.{w} (Mod A)] (I : Ideal A) (M : Mod A)
    (hI : I.FG) (hM : derivedCompleteModule I M) :
    Function.Surjective (AdicCompletion.of I (M : Type u)) := by
  sorry

theorem derived_complete_module_iff_adic_complete {A : Type u} [CommRing A]
    [HasDerivedCategory.{w} (Mod A)] (I : Ideal A) (M : Mod A) (hI : I.FG) :
    List.TFAE
      [IsAdicComplete I (M : Type u),
       derivedCompleteModule I M ∧
         (⨅ n : ℕ, (I ^ n) • (⊤ : Submodule A (M : Type u))) = ⊥] := by
  sorry

def derivedCompleteDerivedProperty {A : Type u} [CommRing A]
    [HasDerivedCategory.{w} (Mod A)] (I : Ideal A) : ObjectProperty (D A) :=
  derivedComplete I

def derivedCompleteModuleProperty {A : Type u} [CommRing A]
    [HasDerivedCategory.{w} (Mod A)] (I : Ideal A) : ObjectProperty (Mod A) :=
  derivedCompleteModule I

abbrev DerivedCompleteModuleCategory {A : Type u} [CommRing A]
    [HasDerivedCategory.{w} (Mod A)] (I : Ideal A) :=
  (derivedCompleteModuleProperty I).FullSubcategory

abbrev DerivedCompleteDerivedCategory {A : Type u} [CommRing A]
    [HasDerivedCategory.{w} (Mod A)] (I : Ideal A) :=
  (derivedCompleteDerivedProperty I).FullSubcategory

theorem derivedComplete_subcategory_properties {A : Type u} [CommRing A]
    [HasDerivedCategory.{w} (Mod A)] (I : Ideal A) :
    (derivedCompleteDerivedProperty I).IsClosedUnderIsomorphisms ∧
      Formalization.Books.Derived.Unit06.IsSaturated (derivedCompleteDerivedProperty I) ∧
      (derivedCompleteDerivedProperty I).IsTriangulated := by
  sorry

theorem derivedComplete_module_weakSerre {A : Type u} [CommRing A]
    [HasDerivedCategory.{w} (Mod A)] (I : Ideal A) :
    (derivedCompleteModuleProperty I).IsWeakSerreClass := by
  sorry

def derivedCompleteCohomologyProperty {A : Type u} [CommRing A]
    [HasDerivedCategory.{w} (Mod A)] (I : Ideal A) : ObjectProperty (D A) :=
  fun K => ∀ i : ℤ, derivedCompleteModule I ((derivedCohomology A i).obj K)

theorem derivedComplete_cohomology_property_eq {A : Type u} [CommRing A]
    [HasDerivedCategory.{w} (Mod A)] (I : Ideal A) :
    derivedCompleteDerivedProperty I = derivedCompleteCohomologyProperty I := by
  sorry

theorem derivedComplete_closed_under_products {A : Type u} [CommRing A]
    [HasDerivedCategory.{w} (Mod A)] (I : Ideal A)
    (ι : Type u) (F : ι → D A)
    [HasProduct F] (hF : ∀ i, derivedComplete I (F i)) :
    derivedComplete I (∏ᶜ F) := by
  sorry

theorem derivedComplete_closed_under_derived_limit {A : Type u} [CommRing A]
    [HasDerivedCategory.{w} (Mod A)] (I : Ideal A)
    (F : DerivedInverseSystem (D A))
    (hF : HasProduct (fun n : ℕ => F.obj (Opposite.op n)))
    (hcomplete : ∀ n, derivedComplete I (F.obj (Opposite.op n))) :
    derivedComplete I (derivedLimitWithProduct F hF) := by
  sorry

theorem derived_complete_module_zero {A : Type u} [CommRing A]
    [HasDerivedCategory.{w} (Mod A)] (I : Ideal A) (hI : I.FG) (M : Mod A)
    (hM : derivedCompleteModule I M)
    (hquot : IsZero (ModuleCat.of A
      ((M : Type u) ⧸ (I • (⊤ : Submodule A (M : Type u)))))) :
    IsZero M := by
  sorry

/-! ## Further basic lemmas and Cech completion -/

theorem pseudoCoherent_is_derivedComplete {A : Type u} [CommRing A]
    [HasDerivedCategory.{w} (Mod A)] (I : Ideal A)
    (hA : derivedComplete I (moduleInDerived A (ModuleCat.of A A)))
    (K : D A) (hK : Formalization.Books.MoreAlgebra.Unit65.IsPseudoCoherent A K) :
    derivedComplete I K := by
  sorry

theorem derived_double_localize {A : Type u} [CommRing A]
    [HasDerivedCategory.{w} (Mod A)] (f g : A) (K : D A) :
    Nonempty
      (RHom (moduleInDerived A (localizedModule A f))
          (RHom (moduleInDerived A (localizedModule A g)) K) ≅
        RHom (moduleInDerived A (localizedModule A (f * g))) K) := by
  sorry

structure ExtendedCechComplexData (A : Type u) [CommRing A]
    (r : ℕ) (f : Fin r → A) where
  complex : Comp A
  isExtendedAlternating : Prop

structure DerivedCompletionData (A : Type u) [CommRing A]
    [HasDerivedCategory.{w} (Mod A)] (I : Ideal A) where
  completion : D A ⥤ D A
  unit : 𝟭 (D A) ⟶ completion
  complete : ∀ K, derivedComplete I (completion.obj K)
  universal : ∀ K E, derivedComplete I E →
    Function.Bijective (fun g : completion.obj K ⟶ E => unit.app K ≫ g)

theorem exists_derivedCompletionData {A : Type u} [CommRing A]
    [HasDerivedCategory.{w} (Mod A)] (I : Ideal A) (hI : I.FG) :
    Nonempty (DerivedCompletionData A I) := by
  sorry

noncomputable def derivedCompletionData {A : Type u} [CommRing A]
    [HasDerivedCategory.{w} (Mod A)] (I : Ideal A) (hI : I.FG) :
    DerivedCompletionData A I :=
  Classical.choice (exists_derivedCompletionData I hI)

noncomputable abbrev derivedCompletion {A : Type u} [CommRing A]
    [HasDerivedCategory.{w} (Mod A)] (I : Ideal A) (hI : I.FG) : D A ⥤ D A :=
  (derivedCompletionData I hI).completion

noncomputable abbrev derivedCompletionUnit {A : Type u} [CommRing A]
    [HasDerivedCategory.{w} (Mod A)] (I : Ideal A) (hI : I.FG) :
    𝟭 (D A) ⟶ derivedCompletion I hI :=
  (derivedCompletionData I hI).unit

noncomputable abbrev completedObject {A : Type u} [CommRing A]
    [HasDerivedCategory.{w} (Mod A)] (I : Ideal A) (hI : I.FG) (K : D A) : D A :=
  (derivedCompletion I hI).obj K

theorem derivedCompletion_is_complete {A : Type u} [CommRing A]
    [HasDerivedCategory.{w} (Mod A)] (I : Ideal A) (hI : I.FG) (K : D A) :
    derivedComplete I (completedObject I hI K) := by
  exact (derivedCompletionData I hI).complete K

theorem derivedCompletion_unit_universal {A : Type u} [CommRing A]
    [HasDerivedCategory.{w} (Mod A)] (I : Ideal A) (hI : I.FG)
    (K E : D A) (hE : derivedComplete I E) :
    Function.Bijective
      (fun g : completedObject I hI K ⟶ E =>
        (derivedCompletionUnit I hI).app K ≫ g) := by
  exact (derivedCompletionData I hI).universal K E hE

theorem derivedCompletion_cech_formula {A : Type u} [CommRing A]
    [HasDerivedCategory.{w} (Mod A)] (I : Ideal A) (hI : I.FG)
    {r : ℕ} (f : Fin r → A) (hgen : I = Ideal.span (Set.range f)) (K : D A) :
    ∃ C : ExtendedCechComplexData A r f,
      Nonempty
        (completedObject I hI K ≅
          RHom ((DerivedCategory.Q : Comp A ⥤ D A).obj C.complex) K) := by
  sorry

theorem derivedComplete_is_fixed_by_completion {A : Type u} [CommRing A]
    [HasDerivedCategory.{w} (Mod A)] (I : Ideal A) (hI : I.FG) (K : D A)
    (hK : derivedComplete I K) :
    IsIso ((derivedCompletionUnit I hI).app K) := by
  sorry

def IsComplexLocalizedAt {A : Type u} [CommRing A]
    (f : A) (K : Comp A) : Prop :=
  ∃ α : K ⟶ K, IsIso α ∧ ∀ n : ℤ, α.f n = f • 𝟙 (K.X n)

theorem derivedCompletion_vanishes_on_localized {A : Type u} [CommRing A]
    [HasDerivedCategory.{w} (Mod A)] (I : Ideal A) (hI : I.FG)
    (f : A) (hf : f ∈ I) (K : Comp A) (hK : IsComplexLocalizedAt f K) :
    IsZero (completedObject I hI ((DerivedCategory.Q : Comp A ⥤ D A).obj K)) := by
  sorry

theorem derivedCompletion_RHom {A : Type u} [CommRing A]
    [HasDerivedCategory.{w} (Mod A)] (I : Ideal A) (hI : I.FG)
    (K L : D A) :
    Nonempty (completedObject I hI (RHom K L) ≅
      RHom K (completedObject I hI L)) ∧
      Nonempty (completedObject I hI (RHom K L) ≅
        RHom (completedObject I hI K) (completedObject I hI L)) := by
  sorry

/-! ## Naive and Koszul models -/

noncomputable def derivedTensorInverseSystem {A : Type u} [CommRing A]
    [HasDerivedCategory.{w} (Mod A)] (K : D A)
    (S : DerivedInverseSystem (D A)) : DerivedInverseSystem (D A) :=
  ((Functor.const (ℕᵒᵖ)).obj K).prod' S ⋙ derivedTensorFunctor (R := A)

def ScalarPowerVanishes {A : Type u} [CommRing A]
    [HasDerivedCategory.{w} (Mod A)] (f : A) (n : ℕ) (K : D A) : Prop :=
  ∃ e : ℕ, derivedScalarMap (f ^ e) K = 0

theorem naive_derived_completion_is_complete {A : Type u} [CommRing A]
    [HasDerivedCategory.{w} (Mod A)] (I : Ideal A) (K : D A)
    (S : DerivedInverseSystem (D A))
    (hS : HasProduct (fun n : ℕ =>
      (derivedTensorInverseSystem K S).obj (Opposite.op n)))
    (hvanish : ∀ f ∈ I, ∀ n : ℕ,
      ScalarPowerVanishes f n (S.obj (Opposite.op n))) :
    derivedComplete I
      (derivedLimitWithProduct (derivedTensorInverseSystem K S) hS) := by
  sorry

structure KoszulSituation (A : Type u) [CommRing A]
    [HasDerivedCategory.{w} (Mod A)] (I : Ideal A) (r : ℕ) (f : Fin r → A) where
  system : DerivedInverseSystem (D A)
  stage : ℕ → Comp A
  stage_represents : ∀ n : ℕ,
    Nonempty ((DerivedCategory.Q : Comp A ⥤ D A).obj (stage n) ≅
      system.obj (Opposite.op n))
  stage_is_koszul : ∀ n : ℕ, Prop
  transition_component_formula : ∀ (m n : ℕ), n ≤ m → Prop
  hasProduct : HasProduct (fun n : ℕ => system.obj (Opposite.op n))

theorem exists_koszulSituation {A : Type u} [CommRing A]
    [HasDerivedCategory.{w} (Mod A)] (I : Ideal A) (r : ℕ) (f : Fin r → A)
    (hgen : I = Ideal.span (Set.range f)) :
    Nonempty (KoszulSituation A I r f) := by
  sorry

noncomputable def koszulSituation {A : Type u} [CommRing A]
    [HasDerivedCategory.{w} (Mod A)] (I : Ideal A) (r : ℕ) (f : Fin r → A)
    (hgen : I = Ideal.span (Set.range f)) : KoszulSituation A I r f :=
  Classical.choice (exists_koszulSituation I r f hgen)

theorem koszul_completion_is_complete {A : Type u} [CommRing A]
    [HasDerivedCategory.{w} (Mod A)] (I : Ideal A) (r : ℕ) (f : Fin r → A)
    (hgen : I = Ideal.span (Set.range f)) (K : D A)
    (S : KoszulSituation A I r f)
    (hS : HasProduct (fun n : ℕ =>
      (derivedTensorInverseSystem K S.system).obj (Opposite.op n))) :
    derivedComplete I
      (derivedLimitWithProduct (derivedTensorInverseSystem K S.system)
        hS) := by
  sorry

theorem derivedComplete_iff_koszul_limit {A : Type u} [CommRing A]
    [HasDerivedCategory.{w} (Mod A)] (I : Ideal A) (r : ℕ) (f : Fin r → A)
    (hgen : I = Ideal.span (Set.range f)) (K : D A)
    (S : KoszulSituation A I r f)
    (hS : HasProduct (fun n : ℕ =>
      (derivedTensorInverseSystem K S.system).obj (Opposite.op n))) :
    derivedComplete I K ↔
      Nonempty (K ≅
        derivedLimitWithProduct (derivedTensorInverseSystem K S.system)
          hS) := by
  sorry

theorem koszul_derived_completion_adjunction {A : Type u} [CommRing A]
    [HasDerivedCategory.{w} (Mod A)] (I : Ideal A) (r : ℕ) (f : Fin r → A)
    (hgen : I = Ideal.span (Set.range f)) (K : D A)
    (S : KoszulSituation A I r f)
    (hS : HasProduct (fun n : ℕ =>
      (derivedTensorInverseSystem K S.system).obj (Opposite.op n)))
    (hI : I.FG) :
    Nonempty
      (derivedLimitWithProduct (derivedTensorInverseSystem K S.system)
          hS ≅ completedObject I hI K) := by
  sorry

/-! ## Boundedness, derived Nakayama, and finite cohomological dimension -/

theorem derivedComplete_bounded_iff {A : Type u} [CommRing A]
    [HasDerivedCategory.{w} (Mod A)] (I : Ideal A) (r : ℕ) (f : Fin r → A)
    (hgen : I = Ideal.span (Set.range f)) (K : D A)
    (hK : derivedComplete I K) :
    List.TFAE
      [∀ i : ℤ, 0 < i → IsZero ((derivedCohomology A i).obj K),
       ∀ i : ℤ, 0 < i →
         IsZero ((derivedCohomology A i).obj
           (derivedTensorWithModule K (ModuleCat.of A (A ⧸ I)))),
       ∀ i : ℤ, 0 < i →
           IsZero ((derivedCohomology A i).obj
             (derivedTensor K
             ((DerivedCategory.Q : Comp A ⥤ D A).obj
               ((koszulSituation I r f hgen).stage 1))))] := by
  sorry

theorem derivedComplete_derived_nakayama {A : Type u} [CommRing A]
    [HasDerivedCategory.{w} (Mod A)] (I : Ideal A) (hI : I.FG) (K : D A)
    (hK : derivedComplete I K)
    (hvanish : IsZero
      (derivedTensorWithModule K (ModuleCat.of A (A ⧸ I)))) :
    IsZero K := by
  sorry

theorem derivedCompletion_finite_cohomological_dimension {A : Type u}
    [CommRing A] [HasDerivedCategory.{w} (Mod A)] (I : Ideal A) (r : ℕ)
    (hgen : ∃ f : Fin r → A, I = Ideal.span (Set.range f))
    (hI : I.FG) (K L : D A) (α : K ⟶ L)
    (hα_iso : ∀ i : ℤ, 1 ≤ i →
      IsIso ((derivedCohomology A i).map α))
    (hα_surjective : Epi ((derivedCohomology A 0).map α)) :
    (∀ i : ℤ, 1 ≤ i →
      IsIso ((derivedCohomology A i).map
        ((derivedCompletion I hI).map α))) ∧
      Epi ((derivedCohomology A 0).map ((derivedCompletion I hI).map α)) := by
  sorry

theorem derivedCompletion_finite_cohomological_dimension_lower {A : Type u}
    [CommRing A] [HasDerivedCategory.{w} (Mod A)] (I : Ideal A)
    (r : ℕ) (hgen : ∃ f : Fin r → A, I = Ideal.span (Set.range f))
    (hI : I.FG) (K L : D A) (α : K ⟶ L)
    (hα_iso : ∀ i : ℤ, i ≤ -1 →
      IsIso ((derivedCohomology A i).map α))
    (hα_injective : Mono ((derivedCohomology A 0).map α)) :
    (∀ i : ℤ, i ≤ -(r : ℤ) - 1 →
      IsIso ((derivedCohomology A i).map
        ((derivedCompletion I hI).map α))) ∧
      Mono ((derivedCohomology A (-r : ℤ)).map
        ((derivedCompletion I hI).map α)) := by
  sorry

structure DerivedCompletionSpectralSequenceData {A : Type u} [CommRing A]
    [HasDerivedCategory.{w} (Mod A)] (I : Ideal A) (hI : I.FG)
    (K : FilteredComplex (Mod A)) where
  spectralSequence :
    Formalization.Books.Homology.Unit24.FilteredComplexSpectralSequence K
  page_complete : ∀ r p q,
    derivedCompleteModule I ((spectralSequence.page r) (p, q))
  page_one : ∀ p q, Nonempty
    ((spectralSequence.page 1) (p, q) ≅
      (derivedCohomology A (p + q)).obj
        (completedObject I hI ((DerivedCategory.Q : Comp A ⥤ D A).obj
          (filteredComplexGradedPiece K p))))
  bounded_converges : Prop

theorem exists_derivedCompletion_spectral_sequence {A : Type u} [CommRing A]
    [HasDerivedCategory.{w} (Mod A)] (I : Ideal A) (hI : I.FG)
    (K : FilteredComplex (Mod A)) :
    Nonempty (DerivedCompletionSpectralSequenceData I hI K) := by
  sorry

def completedCohomology {A : Type u} [CommRing A]
    [HasDerivedCategory.{w} (Mod A)] (I : Ideal A) (hI : I.FG) (i : ℤ)
    (M : Mod A) : Mod A :=
  (derivedCohomology A i).obj
    (completedObject I hI (moduleInDerived A M))

structure DerivedCompletionCohomologySpectralSequenceData {A : Type u}
    [CommRing A] [HasDerivedCategory.{w} (Mod A)] (I : Ideal A) (hI : I.FG)
    (K : D A) where
  page : ℕ → ℤ → ℤ → Mod A
  differential : ∀ r i j, page r i j ⟶ page r (i + r) (j - r + 1)
  page_complete : ∀ r i j, derivedCompleteModule I (page r i j)
  page_two : ∀ i j, Nonempty (page 2 i j ≅
    completedCohomology I hI i ((derivedCohomology A j).obj K))
  converges : Prop

theorem exists_derivedCompletion_cohomology_spectral_sequence
    {A : Type u} [CommRing A] [HasDerivedCategory.{w} (Mod A)]
    (I : Ideal A) (hI : I.FG) (K : D A) :
    Nonempty (DerivedCompletionCohomologySpectralSequenceData I hI K) := by
  sorry

/-! ## Restriction of scalars -/

structure DerivedRestrictionData {A B : Type u} [CommRing A] [CommRing B]
    [HasDerivedCategory.{w} (Mod A)] [HasDerivedCategory.{w} (Mod B)]
    (φ : A →+* B) where
  functor : D B ⥤ D A

theorem exists_derivedRestrictionData {A B : Type u} [CommRing A] [CommRing B]
    [HasDerivedCategory.{w} (Mod A)] [HasDerivedCategory.{w} (Mod B)]
    (φ : A →+* B) : Nonempty (DerivedRestrictionData φ) := by
  sorry

noncomputable def derivedRestriction {A B : Type u} [CommRing A] [CommRing B]
    [HasDerivedCategory.{w} (Mod A)] [HasDerivedCategory.{w} (Mod B)]
    (φ : A →+* B) : D B ⥤ D A :=
  (Classical.choice (exists_derivedRestrictionData φ)).functor

theorem derivedRestriction_complete_iff {A B : Type u} [CommRing A] [CommRing B]
    [HasDerivedCategory.{w} (Mod A)] [HasDerivedCategory.{w} (Mod B)]
    (φ : A →+* B) (I : Ideal A) (L : D B) :
    derivedComplete (Ideal.map φ I) L ↔
      derivedComplete I ((derivedRestriction φ).obj L) := by
  sorry

theorem derivedRestriction_complete_equivalence {A B : Type u} [CommRing A]
    [CommRing B] [HasDerivedCategory.{w} (Mod A)]
    [HasDerivedCategory.{w} (Mod B)] (φ : A →+* B) (I : Ideal A)
    (hI : I.FG) (hflat : RingHom.Flat φ)
    (hquot : Nonempty (A ⧸ I ≃+* B ⧸ Ideal.map φ I)) :
    ∃ F : DerivedCompleteDerivedCategory (Ideal.map φ I) ⥤
        DerivedCompleteDerivedCategory I,
      Functor.IsEquivalence F := by
  sorry

end Formalization.Books.MoreAlgebra.Unit92
