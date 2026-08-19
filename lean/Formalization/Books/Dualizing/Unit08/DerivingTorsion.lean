import Formalization.Books.Dualizing.Unit05.InjectiveHulls
import Formalization.Books.Categories.Unit24.AdjointFunctors
import Formalization.Books.Derived.Unit17.TriangulatedSubcategories
import Formalization.Books.Derived.Unit27.ExtGroups
import Formalization.Books.Derived.Unit20.HigherDerivedFunctors
import Formalization.Books.Derived.Unit30.DerivingAdjoints
import Formalization.Books.Derived.Unit33.DerivedColimits
import Formalization.Books.MoreAlgebra.Unit74.DerivedHom
import Formalization.Books.MoreAlgebra.Unit89.TorsionModules
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# Dualizing Complexes, Chapter 8: deriving torsion

This file records the statements in the chapter's section on the derived
functor of ideal-power torsion.  The ideal-power torsion submodule, its Serre
subcategory, and the derived comparison functor are the canonical objects
from the earlier More Algebra and Derived Categories formalizations.
-/

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open Formalization.Books.Categories.Unit23
open Formalization.Books.Derived.Unit11
open Formalization.Books.Derived.Unit17
open Formalization.Books.Derived.Unit27
open Formalization.Books.Derived.Unit20
open Formalization.Books.Derived.Unit30
open Formalization.Books.Derived.Unit33
open Formalization.Books.Homology.Unit07
open Formalization.Books.MoreAlgebra.Unit53
open Formalization.Books.MoreAlgebra.Unit74
open Formalization.Books.MoreAlgebra.Unit89
open scoped CategoryTheory.Pretriangulated.Opposite ZeroObject

universe u v w

namespace Formalization.Books.Dualizing.Unit08

/-! ## The torsion category and the functor `H⁰_I` -/

abbrev ModuleDerivedCategory (R : Type u) [CommRing R]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)] :=
  DerivedCategory (ModuleCat.{u} R)

abbrev TorsionModuleCategory (R : Type u) [CommRing R] (I : Ideal R) :=
  iPowerTorsionModuleCategory R I

abbrev TorsionDerivedCategory (R : Type u) [CommRing R] (I : Ideal R)
    [Abelian (TorsionModuleCategory R I)]
    [HasDerivedCategory.{w} (TorsionModuleCategory R I)] :=
  DerivedCategory (TorsionModuleCategory R I)

theorem torsion_modules_form_serre
    {R : Type u} [CommRing R] (I : Ideal R) (hI : I.FG) :
    (iPowerTorsionModuleProperty R I).IsSerreClass :=
  iPowerTorsionModuleProperty_isSerreClass R I hI

theorem torsion_module_category_is_abelian
    {R : Type u} [CommRing R] (I : Ideal R) (hI : I.FG) :
    Nonempty (Abelian (TorsionModuleCategory R I)) :=
  iPowerTorsionModuleCategory_is_abelian R I hI

/- The source's Grothendieck-category assertion is stronger than the Serre
   assertion above.  It is kept as a class-valued interface so that the
   subsequent derived-category declarations can use Mathlib's exact API. -/
theorem torsion_module_category_is_grothendieck
    {R : Type u} [CommRing R] (I : Ideal R) (hI : I.FG)
    [Abelian (TorsionModuleCategory R I)] :
    Nonempty (IsGrothendieckAbelian.{w} (TorsionModuleCategory R I)) := by
  sorry

theorem torsion_module_category_has_derived_category
    {R : Type u} [CommRing R] (I : Ideal R) (hI : I.FG)
    [Abelian (TorsionModuleCategory R I)] :
    Nonempty (HasDerivedCategory.{w} (TorsionModuleCategory R I)) := by
  sorry

theorem idealPowerTorsionSubmoduleInfinity_isIPowerTorsion
    {R M : Type u} [CommRing R] [AddCommGroup M] [Module R M]
    (I : Ideal R) :
    IsIPowerTorsion I
      (idealPowerTorsionSubmoduleInfinity (M := M) I : Type u) := by
  intro x
  obtain ⟨n, hn, hkill⟩ :=
    (mem_idealPowerTorsionSubmoduleInfinity_iff (M := M) I (x : M)).mp
      x.property
  refine ⟨n, hn, ?_⟩
  intro a ha
  apply Subtype.ext
  exact hkill a ha

theorem idealPowerTorsionSubmoduleInfinity_map_mem
    {R : Type u} [CommRing R] (I : Ideal R)
    {X Y : ModuleCat.{u} R} (f : X ⟶ Y)
    (x : idealPowerTorsionSubmoduleInfinity (M := (X : Type u)) I) :
    f.hom x ∈ idealPowerTorsionSubmoduleInfinity (M := (Y : Type u)) I := by
  sorry

noncomputable def idealPowerTorsionSubmoduleFunctor
    {R : Type u} [CommRing R] (I : Ideal R) :
    ModuleCat.{u} R ⥤ ModuleCat.{u} R where
  obj X := ModuleCat.of R
    (idealPowerTorsionSubmoduleInfinity (M := (X : Type u)) I : Type u)
  map {X Y} f := ModuleCat.ofHom
    ((f.hom.comp (idealPowerTorsionSubmoduleInfinity (M := (X : Type u)) I).subtype).codRestrict
      (idealPowerTorsionSubmoduleInfinity (M := (Y : Type u)) I)
      (fun x => idealPowerTorsionSubmoduleInfinity_map_mem I f x))
  map_id X := by
    apply ModuleCat.hom_ext
    rfl
  map_comp f g := by
    apply ModuleCat.hom_ext
    rfl

/- `H⁰_I(M) = M[I^∞]` is the lift of the preceding canonical submodule
   functor through the full subcategory of `I`-power torsion modules. -/
noncomputable def idealPowerTorsionFunctor
    {R : Type u} [CommRing R] (I : Ideal R) :
    ModuleCat.{u} R ⥤ TorsionModuleCategory R I :=
  (iPowerTorsionModuleProperty R I).lift
    (idealPowerTorsionSubmoduleFunctor I)
    (fun X => by
      intro x
      obtain ⟨n, hn, hkill⟩ :=
        (mem_idealPowerTorsionSubmoduleInfinity_iff
          (M := (X : Type u)) I (x.1 : (X : Type u))).mp x.property
      refine ⟨n, hn, ?_⟩
      intro a ha
      apply Subtype.ext
      exact hkill a ha)

theorem idealPowerTorsionFunctor_isLeftExact
    {R : Type u} [CommRing R] (I : Ideal R) (hI : I.FG) :
    IsLeftExact (idealPowerTorsionFunctor I) := by
  sorry

/- The equality of the closed supports is the source-facing form of the
   assertion that the torsion category does not depend on the chosen finitely
   generated ideal.  The elementwise content is already proved by the
   canonical More Algebra theorem. -/
theorem torsion_property_depends_only_on_zeroLocus
    {R : Type u} [CommRing R] (I J : Ideal R)
    (hI : I.FG) (hJ : J.FG)
    (hZ : PrimeSpectrum.zeroLocus (I : Set R) =
      PrimeSpectrum.zeroLocus (J : Set R)) :
    iPowerTorsionModuleProperty R I = iPowerTorsionModuleProperty R J := by
  funext M
  apply propext
  exact iPowerTorsion_depends_only_on_zeroLocus I J hI hJ hZ

/- The terminology warning in the source is recorded by the interfaces above:
   they assume only finite generation of `I`, never Noetherianity of `R`, and
   therefore do not assert an identification with a separately defined
   `RΓ_Z` construction. -/

/-! ## The derived functor `RΓ_I` and its satellites -/

def IsDerivedTorsionExtension
    {R : Type u} [CommRing R]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)]
    (I : Ideal R) (hI : I.FG) [Abelian (TorsionModuleCategory R I)]
    [HasDerivedCategory.{w} (TorsionModuleCategory R I)]
    (F : ModuleDerivedCategory R ⥤ TorsionDerivedCategory R I)
    (hF : IsLeftExact (idealPowerTorsionFunctor I)) : Prop :=
  IsLeftExact (idealPowerTorsionFunctor I) ∧ ∃ hAdd :
      @Functor.Additive (ModuleCat.{u} R) (TorsionModuleCategory R I)
        _ _ (abelian_additiveCategory (ModuleCat.{u} R)).toPreadditive
          (abelian_additiveCategory (TorsionModuleCategory R I)).toPreadditive
          (idealPowerTorsionFunctor I),
    @IsUnboundedRightDerivedFunctor
      (ModuleCat.{u} R) _ _ (TorsionModuleCategory R I) _ _ _ _
      (idealPowerTorsionFunctor I) hAdd F

structure DerivedTorsionFunctorData
    {R : Type u} [CommRing R]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)]
    (I : Ideal R) (hI : I.FG) [Abelian (TorsionModuleCategory R I)]
    [HasDerivedCategory.{w} (TorsionModuleCategory R I)]
    (hF : IsLeftExact (idealPowerTorsionFunctor I)) where
  functor : ModuleDerivedCategory R ⥤ TorsionDerivedCategory R I
  isDerived : IsDerivedTorsionExtension I hI functor hF

theorem derivedTorsionFunctorData_exists
    {R : Type u} [CommRing R]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)]
    (I : Ideal R) (hI : I.FG) [Abelian (TorsionModuleCategory R I)]
    [HasDerivedCategory.{w} (TorsionModuleCategory R I)]
    (hF : IsLeftExact (idealPowerTorsionFunctor I)) :
    Nonempty (DerivedTorsionFunctorData I hI hF) := by
  sorry

noncomputable def derivedTorsionFunctor
    {R : Type u} [CommRing R]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)]
    (I : Ideal R) (hI : I.FG) [Abelian (TorsionModuleCategory R I)]
    [HasDerivedCategory.{w} (TorsionModuleCategory R I)]
    (hF : IsLeftExact (idealPowerTorsionFunctor I)) :
    ModuleDerivedCategory R ⥤ TorsionDerivedCategory R I :=
  (Classical.choice (derivedTorsionFunctorData_exists I hI hF)).functor

theorem derivedTorsionFunctor_isDerived
    {R : Type u} [CommRing R]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)]
    (I : Ideal R) (hI : I.FG) [Abelian (TorsionModuleCategory R I)]
    [HasDerivedCategory.{w} (TorsionModuleCategory R I)]
    (hF : IsLeftExact (idealPowerTorsionFunctor I)) :
    IsDerivedTorsionExtension I hI (derivedTorsionFunctor I hI hF) hF := by
  exact (Classical.choice (derivedTorsionFunctorData_exists I hI hF)).isDerived

noncomputable def localCohomologyFunctor
    {R : Type u} [CommRing R] (I : Ideal R) (hI : I.FG)
    [HasDerivedCategory.{w} (ModuleCat.{u} R)]
    [Abelian (TorsionModuleCategory R I)]
    [HasDerivedCategory.{w} (TorsionModuleCategory R I)] (p : ℤ) :
    ModuleCat.{u} R ⥤ TorsionModuleCategory R I :=
  higherRightDerivedFunctor (idealPowerTorsionFunctor I)
    (idealPowerTorsionFunctor_isLeftExact I hI) p

theorem localCohomologyFunctor_zero_iso
    {R : Type u} [CommRing R] (I : Ideal R) (hI : I.FG)
    [HasDerivedCategory.{w} (ModuleCat.{u} R)]
    [Abelian (TorsionModuleCategory R I)]
    [HasDerivedCategory.{w} (TorsionModuleCategory R I)] :
    Nonempty (localCohomologyFunctor I hI 0 ≅ idealPowerTorsionFunctor I) := by
  exact higherRightDerivedFunctor_zero_iso (idealPowerTorsionFunctor I)
    (idealPowerTorsionFunctor_isLeftExact I hI)

/-! ## Comparing the two derived torsion categories -/

structure DerivedTorsionComparisonData
    {R : Type u} [CommRing R]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)]
    (I : Ideal R) (hI : I.FG)
    [Abelian (TorsionModuleCategory R I)]
    [HasDerivedCategory.{w} (TorsionModuleCategory R I)] where
  comparison : TorsionDerivedCategory R I ⥤
    derivedCohomologySubcategory (iPowerTorsionModuleProperty R I)
  inclusion : TorsionDerivedCategory R I ⥤ ModuleDerivedCategory R

theorem derivedTorsionComparisonData_exists
    {R : Type u} [CommRing R]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)]
    (I : Ideal R) (hI : I.FG)
    [Abelian (TorsionModuleCategory R I)]
    [HasDerivedCategory.{w} (TorsionModuleCategory R I)] :
    Nonempty (DerivedTorsionComparisonData I hI) := by
  sorry

noncomputable def derivedTorsionComparisonFunctor
    {R : Type u} [CommRing R]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)]
    (I : Ideal R) (hI : I.FG)
    [Abelian (TorsionModuleCategory R I)]
    [HasDerivedCategory.{w} (TorsionModuleCategory R I)] :
    TorsionDerivedCategory R I ⥤
      derivedCohomologySubcategory (iPowerTorsionModuleProperty R I) := by
  exact (Classical.choice (derivedTorsionComparisonData_exists I hI)).comparison

noncomputable def derivedTorsionInclusionFunctor
    {R : Type u} [CommRing R]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)]
    (I : Ideal R) (hI : I.FG)
    [Abelian (TorsionModuleCategory R I)]
    [HasDerivedCategory.{w} (TorsionModuleCategory R I)] :
    TorsionDerivedCategory R I ⥤ ModuleDerivedCategory R := by
  exact (Classical.choice (derivedTorsionComparisonData_exists I hI)).inclusion

theorem derivedTorsionFunctor_rightAdjoint_to_inclusion
    {R : Type u} [CommRing R]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)]
    (I : Ideal R) (hI : I.FG)
    [Abelian (TorsionModuleCategory R I)]
    [HasDerivedCategory.{w} (TorsionModuleCategory R I)]
    (hF : IsLeftExact (idealPowerTorsionFunctor I)) :
    Nonempty
      (derivedTorsionInclusionFunctor I hI ⊣ derivedTorsionFunctor I hI hF) := by
  sorry

/-! The displayed hocolimit identity is stated after applying the canonical
   derived inclusion.  This is the type-correct form of the source's
   identification of `D(I^∞-torsion)` with its full subcategory in `D(A)`. -/

noncomputable def idealPowerQuotientMap
    {R : Type u} [CommRing R] (I : Ideal R) (n : ℕ) :
    ModuleCat.of R (R ⧸ I ^ (n + 2)) ⟶
      ModuleCat.of R (R ⧸ I ^ (n + 1)) :=
  ModuleCat.ofHom
    (Ideal.Quotient.factorₐ R
      (Ideal.pow_le_pow_right (I := I) (Nat.le_succ (n + 1)))).toLinearMap

structure IdealPowerRHomSystem
    {R : Type u} [CommRing R]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)]
    (I : Ideal R) (K : ModuleDerivedCategory R) where
  system : ℕ ⥤ ModuleDerivedCategory R
  stageIso : ∀ n, system.obj n ≅
    RHom (R := R)
      ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj
        (ModuleCat.of R (R ⧸ I ^ (n + 1)))) K
  transition : ∀ n,
    system.map (homOfLE (Nat.le_succ n)) ≫ (stageIso (n + 1)).hom =
      (stageIso n).hom ≫
        rHomMap (R := R)
          ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).map
            (idealPowerQuotientMap I n)) (𝟙 K)

theorem idealPowerRHomSystem_exists
    {R : Type u} [CommRing R]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)]
    (I : Ideal R) (K : ModuleDerivedCategory R) :
    Nonempty (IdealPowerRHomSystem I K) := by
  sorry

noncomputable def idealPowerRHomSystem
    {R : Type u} [CommRing R]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)]
    (I : Ideal R) (K : ModuleDerivedCategory R) :
    IdealPowerRHomSystem I K :=
  Classical.choice (idealPowerRHomSystem_exists I K)

noncomputable def idealPowerRHomSystem_hocolim
    {R : Type u} [CommRing R]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)]
    {I : Ideal R} {K : ModuleDerivedCategory R}
    (S : IdealPowerRHomSystem I K) : ModuleDerivedCategory R :=
  homotopyColimit S.system (derivedCategory_homotopyColimit_exists S.system)

theorem derivedTorsion_hocolim_RHom
    {R : Type u} [CommRing R]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)]
    (I : Ideal R) (hI : I.FG)
    [Abelian (TorsionModuleCategory R I)]
    [HasDerivedCategory.{w} (TorsionModuleCategory R I)]
    (hF : IsLeftExact (idealPowerTorsionFunctor I))
    (K : ModuleDerivedCategory R) :
    Nonempty
      ((derivedTorsionInclusionFunctor I hI).obj
          ((derivedTorsionFunctor I hI hF).obj K) ≅
        idealPowerRHomSystem_hocolim
          (I := I) (K := K) (idealPowerRHomSystem I K)) := by
  sorry

/-! The module-valued cohomology identity is recorded with the actual
   sequential system of cohomologies of the displayed derived-Hom system. -/
structure IdealPowerExtSystem
    {R : Type u} [CommRing R]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)]
    (I : Ideal R) (K : ModuleDerivedCategory R) (q : ℤ) where
  system : ℕ ⥤ ModuleCat.{u} R
  stageIso : ∀ n, system.obj n ≅
    (derivedCohomologyFunctor (ModuleCat.{u} R) q).obj
      (RHom (R := R)
        ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj
          (ModuleCat.of R (R ⧸ I ^ (n + 1)))) K)
  transition : ∀ n,
    system.map (homOfLE (Nat.le_succ n)) ≫ (stageIso (n + 1)).hom =
      (stageIso n).hom ≫
        (derivedCohomologyFunctor (ModuleCat.{u} R) q).map
          (rHomMap (R := R)
            ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).map
              (idealPowerQuotientMap I n)) (𝟙 K))

noncomputable def idealPowerExtSystem_colimit
    {R : Type u} [CommRing R]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)]
    {I : Ideal R} {K : ModuleDerivedCategory R} {q : ℤ}
    (S : IdealPowerExtSystem I K q) : ModuleCat.{u} R :=
  colimit S.system

theorem derivedTorsion_cohomology_colim_Ext
    {R : Type u} [CommRing R]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)]
    (I : Ideal R) (hI : I.FG)
    [Abelian (TorsionModuleCategory R I)]
    [HasDerivedCategory.{w} (TorsionModuleCategory R I)]
    (hF : IsLeftExact (idealPowerTorsionFunctor I))
    (K : ModuleDerivedCategory R) (q : ℤ) :
    ∃ S : IdealPowerExtSystem I K q,
      Nonempty
        (((iPowerTorsionModuleProperty R I).ι.obj
            ((derivedCohomologyFunctor (TorsionModuleCategory R I) q).obj
              ((derivedTorsionFunctor I hI hF).obj K))) ≅
          idealPowerExtSystem_colimit S) := by
  sorry

/-! ## Vanishing after inverting an element -/

def ScalarActionIsInvertible
    {R : Type u} [CommRing R] (K : CochainComplex (ModuleCat.{u} R) ℤ)
    (f : R) : Prop :=
  ∀ n : ℤ, Function.Bijective (fun x : K.X n => f • x)

theorem derivedTorsion_vanishes_of_scalar_invertible
    {R : Type u} [CommRing R]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)]
    (I : Ideal R) (hI : I.FG)
    [Abelian (TorsionModuleCategory R I)]
    [HasDerivedCategory.{w} (TorsionModuleCategory R I)]
    (hF : IsLeftExact (idealPowerTorsionFunctor I))
    {K : CochainComplex (ModuleCat.{u} R) ℤ} {f : R}
    (hfI : f ∈ I) (hK : ScalarActionIsInvertible K f) :
    IsZero ((derivedTorsionFunctor I hI hF).obj
      ((DerivedCategory.Q (C := ModuleCat.{u} R)).obj K)) := by
  sorry

/-! ## The comparison is not an equivalence in general -/

theorem derivedTorsionInclusionFunctor_commShift
    {R : Type u} [CommRing R]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)]
    (I : Ideal R) (hI : I.FG)
    [Abelian (TorsionModuleCategory R I)]
    [HasDerivedCategory.{w} (TorsionModuleCategory R I)] :
    Nonempty ((derivedTorsionInclusionFunctor I hI).CommShift ℤ) := by
  sorry

noncomputable def derivedExtComparisonMap
    {R : Type u} [CommRing R]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)]
    (I : Ideal R) (hI : I.FG)
    [Abelian (TorsionModuleCategory R I)]
    [HasDerivedCategory.{w} (TorsionModuleCategory R I)]
    {X Y : TorsionDerivedCategory R I} (q : ℤ) :
    DerivedExt X Y q →+
      DerivedExt ((derivedTorsionInclusionFunctor I hI).obj X)
        ((derivedTorsionInclusionFunctor I hI).obj Y) q := by
  letI : (derivedTorsionInclusionFunctor I hI).CommShift ℤ :=
    Classical.choice (derivedTorsionInclusionFunctor_commShift I hI)
  exact
    { toFun := fun ξ => ShiftedHom.map ξ (derivedTorsionInclusionFunctor I hI)
      map_zero' := by sorry
      map_add' := by sorry }

theorem torsion_hom_comparison
    {R : Type u} [CommRing R]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)]
    (I : Ideal R) (hI : I.FG)
    [Abelian (TorsionModuleCategory R I)]
    [HasDerivedCategory.{w} (TorsionModuleCategory R I)]
    (M N : TorsionModuleCategory R I) :
    Nonempty
      (DerivedExt (DerivedObject M) (DerivedObject N) 0 ≃+
        DerivedExt
          ((derivedTorsionInclusionFunctor I hI).obj (DerivedObject M))
          ((derivedTorsionInclusionFunctor I hI).obj (DerivedObject N)) 0) := by
  sorry

theorem torsion_ext_one_comparison
    {R : Type u} [CommRing R]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)]
    (I : Ideal R) (hI : I.FG)
    [Abelian (TorsionModuleCategory R I)]
    [HasDerivedCategory.{w} (TorsionModuleCategory R I)]
    (M N : TorsionModuleCategory R I) :
    Nonempty
      (DerivedExt (DerivedObject M) (DerivedObject N) 1 ≃+
        DerivedExt
          ((derivedTorsionInclusionFunctor I hI).obj (DerivedObject M))
          ((derivedTorsionInclusionFunctor I hI).obj (DerivedObject N)) 1) := by
  sorry

/-! ## The explicit principal-ideal example -/

structure BadTorsionExample where
  A : Type u
  commRing : CommRing A
  f : A
  x : A
  xSeq : ℕ → A
  x_ne_zero : x ≠ 0
  f_annihilates_x : f * x = 0
  power_relation : ∀ n : ℕ, f ^ n * xSeq n = x

theorem exists_badTorsionExample : Nonempty (BadTorsionExample.{u}) := by
  sorry

def principalAnnihilatorSubmodule
    {A : Type u} [CommRing A] (f : A) : Submodule A A :=
  Submodule.torsionBySet A A ({f} : Set A)

noncomputable def badTorsionExampleAnnihilatorElement
    (e : BadTorsionExample.{u}) :
    letI := e.commRing
    ↥(principalAnnihilatorSubmodule e.f) := by
  letI := e.commRing
  exact ⟨e.x, by
    simp [principalAnnihilatorSubmodule, smul_eq_mul, e.f_annihilates_x]⟩

noncomputable def principalTwoExtension
    (e : BadTorsionExample.{u}) :
    letI := e.commRing
    ComposableArrows (ModuleCat.{u} e.A) 4 := by
  letI := e.commRing
  exact ComposableArrows.mk₄
    (0 : (0 : ModuleCat e.A) ⟶
      ModuleCat.of e.A (principalAnnihilatorSubmodule (A := e.A) e.f))
    (ModuleCat.ofHom
      (principalAnnihilatorSubmodule (A := e.A) e.f).subtype)
    (ModuleCat.ofHom (LinearMap.toSpanSingleton e.A e.A e.f))
    (ModuleCat.ofHom (Ideal.span ({e.f} : Set e.A)).mkQ)

theorem principalTwoExtension_exact
    (e : BadTorsionExample.{u}) :
    (principalTwoExtension e).Exact := by
  sorry

theorem principalAnnihilator_isIPowerTorsion
    {A : Type u} [CommRing A] (f : A) :
    IsIPowerTorsion (Ideal.span ({f} : Set A))
      (principalAnnihilatorSubmodule (A := A) f : Type u) := by
  sorry

theorem principalQuotient_isIPowerTorsion
    {A : Type u} [CommRing A] (f : A) :
    IsIPowerTorsion (Ideal.span ({f} : Set A))
      (A ⧸ Ideal.span ({f} : Set A)) := by
  sorry

theorem principalTwoExtension_class_exists
    (e : BadTorsionExample.{u}) :
    letI := e.commRing
    ∃ hD : HasDerivedCategory.{w} (ModuleCat.{u} e.A),
      letI := hD
      Nonempty
        (DerivedExt
          (DerivedObject (ModuleCat.of e.A
            (e.A ⧸ Ideal.span ({e.f} : Set e.A))))
          (DerivedObject
            (ModuleCat.of e.A
              (principalAnnihilatorSubmodule e.f))) 2) := by
  sorry

theorem torsion_ext_two_comparison_not_surjective_in_general :
    ∃ (e : BadTorsionExample.{u}),
      letI := e.commRing
      ∃ hD : HasDerivedCategory.{w} (ModuleCat.{u} e.A),
        letI := hD
        ∃ hT : Abelian
          (TorsionModuleCategory e.A (Ideal.span ({e.f} : Set e.A))),
          letI := hT
          ∃ hDT : HasDerivedCategory.{w}
              (TorsionModuleCategory e.A (Ideal.span ({e.f} : Set e.A))),
            letI := hDT
            ¬ Function.Surjective
              (derivedExtComparisonMap
                (X := DerivedObject
                  (⟨ModuleCat.of e.A
                      (e.A ⧸ Ideal.span ({e.f} : Set e.A)),
                    principalQuotient_isIPowerTorsion e.f⟩ :
                    TorsionModuleCategory e.A
                      (Ideal.span ({e.f} : Set e.A))))
                (Y := DerivedObject
                  (⟨ModuleCat.of e.A
                      (principalAnnihilatorSubmodule e.f),
                    principalAnnihilator_isIPowerTorsion e.f⟩ :
                    TorsionModuleCategory e.A
                      (Ideal.span ({e.f} : Set e.A))))
                (Ideal.span ({e.f} : Set e.A))
                (Submodule.fg_span_singleton e.f) 2) := by
  sorry

theorem derived_torsion_comparison_not_equivalence_in_general :
    ∃ (R : Type u) (_ : CommRing R) (I : Ideal R) (hI : I.FG)
      (_ : HasDerivedCategory.{w} (ModuleCat.{u} R))
      (hT : Abelian (TorsionModuleCategory R I))
      (_ : HasDerivedCategory.{w} (TorsionModuleCategory R I)),
      ¬ (derivedTorsionComparisonFunctor I hI).IsEquivalence := by
  sorry

end Formalization.Books.Dualizing.Unit08
