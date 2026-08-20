import Formalization.Books.Algebra.Unit72.Depth
import Formalization.Books.Algebra.Unit103.CohenMacaulayModules
import Formalization.Books.Dualizing.Unit08.DerivingTorsion
import Formalization.Books.Dualizing.Unit09.LocalCohomology
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.LocalRing.RingHom.Basic

/-!
# Dualizing Complexes, Chapter 11: Depth

This file formalizes the six statements in the numbered `Depth` section.
The depth, Ext, regular-sequence, Cohen--Macaulay, support-dimension, and
flatness notions are the canonical declarations from Mathlib and the earlier
formalization chapters.  The source uses both the ideal-power torsion functor
and the closed-support functor; the two corresponding cohomology objects are
kept distinct below.
-/

namespace Formalization.Books.Dualizing.Unit11

open CategoryTheory
open CategoryTheory.Limits
open Formalization.Books.Algebra.Unit72
open Formalization.Books.Algebra.Unit103
open Formalization.Books.Dualizing.Unit08
open Formalization.Books.Dualizing.Unit09
open Formalization.Books.MoreAlgebra.Unit89

universe u w

noncomputable section

/-! ## Ideal-power and closed-support local cohomology -/

noncomputable def idealTorsionAmbient
    {A : Type u} [CommRing A]
    [HasDerivedCategory.{w} (ModuleCat.{u} A)] (I : Ideal A) (hI : I.FG) :
    Formalization.Books.Dualizing.Unit09.D A ⥤
      Formalization.Books.Dualizing.Unit09.D A := by
  letI : Abelian (TorsionModuleCategory A I) :=
    Classical.choice (torsion_module_category_is_abelian I hI)
  letI : HasDerivedCategory.{w} (TorsionModuleCategory A I) :=
    Classical.choice (torsion_module_category_has_derived_category I hI)
  exact
    derivedTorsionFunctor I hI
        (idealPowerTorsionFunctor_isLeftExact I hI) ⋙
      derivedTorsionInclusionFunctor I hI

/-- The module `H^p_I(M)` for the ideal-power torsion functor. -/
noncomputable def idealLocalCohomologyModule
    {A M : Type u} [CommRing A]
    [HasDerivedCategory.{w} (ModuleCat.{u} A)]
    [AddCommGroup M] [Module A M] (I : Ideal A) (hI : I.FG) (p : ℤ) :
    ModuleCat.{u} A :=
  (Formalization.Books.MoreAlgebra.Unit67.derivedCohomology A p).obj
    ((idealTorsionAmbient I hI).obj
      (Formalization.Books.MoreAlgebra.Unit67.moduleInDerived A (ModuleCat.of A M)))

/-- The module `H^p_Z(M)` for `Z = V(I)`. -/
noncomputable abbrev supportLocalCohomologyModule
    {A M : Type u} [CommRing A]
    [HasDerivedCategory.{w} (ModuleCat.{u} A)]
    [AddCommGroup M] [Module A M] (I : Ideal A) (hI : I.FG) (p : ℤ) :
    ModuleCat.{u} A :=
  localCohomologyModule I hI
    (Formalization.Books.MoreAlgebra.Unit67.moduleInDerived A (ModuleCat.of A M)) p

/-! ## The Ext and local-cohomology characterization of depth -/

/-- `depth_I(M)` is the common first nonvanishing degree of Ext and ideal
local cohomology.  The explicit finite value records the source's phrase
“smallest integer” in the `ℕ∞` convention used by the canonical depth API. -/
theorem depth_eq_min_ext_and_localCohomology
    {A M : Type u} [CommRing A] [IsNoetherianRing A]
    [AddCommGroup M] [Module A M] [Module.Finite A M]
    [HasDerivedCategory.{w} (ModuleCat.{u} A)]
    (I : Ideal A) (hIM : I • (⊤ : Submodule A M) ≠ ⊤) :
    ∃ i : ℕ,
      depth I M = (i : ℕ∞) ∧
        Nontrivial
          (Formalization.Books.Algebra.Unit71.ExtGroup
            (ModuleCat.of A (A ⧸ I)) (ModuleCat.of A M) i) ∧
        Nontrivial (idealLocalCohomologyModule I I.fg_of_isNoetherianRing
          (M := M) (i : ℤ)) ∧
        (∀ j : ℕ, j < i →
          ¬ Nontrivial
            (Formalization.Books.Algebra.Unit71.ExtGroup
              (ModuleCat.of A (A ⧸ I)) (ModuleCat.of A M) j)) ∧
        (∀ j : ℕ, j < i →
          ¬ Nontrivial (idealLocalCohomologyModule I
            I.fg_of_isNoetherianRing (M := M) (j : ℤ))) := by
  sorry

/-- Every finite module killed by a power of `I` has vanishing Ext below
`depth_I(M)`. -/
theorem ext_vanishes_below_depth_for_power_torsion
    {A M : Type u} [CommRing A] [IsNoetherianRing A]
    [AddCommGroup M] [Module A M] [Module.Finite A M]
    [HasDerivedCategory.{w} (ModuleCat.{u} A)]
    (I : Ideal A) (hIM : I • (⊤ : Submodule A M) ≠ ⊤)
    (N : Type u) [AddCommGroup N] [Module A N] [Module.Finite A N]
    (hN : ∃ n : ℕ, I ^ n • (⊤ : Submodule A N) = ⊥) :
    ∀ i : ℕ, i < depth I M →
      Subsingleton
        (Formalization.Books.Algebra.Unit71.ExtGroup
          (ModuleCat.of A N) (ModuleCat.of A M) i) := by
  sorry

/-! ## Depth in a short exact sequence -/

/-- The three depth inequalities for a short exact sequence of finite modules.
The maps and exactness hypotheses are the module-category spelling of the
source's displayed `0 → N' → N → N'' → 0`. -/
theorem depth_in_short_exact
    {A N' N N'' : Type u} [CommRing A] [IsNoetherianRing A]
    [AddCommGroup N'] [Module A N'] [Module.Finite A N']
    [AddCommGroup N] [Module A N] [Module.Finite A N]
    [AddCommGroup N''] [Module A N''] [Module.Finite A N'']
    (I : Ideal A) (f : N' →ₗ[A] N) (g : N →ₗ[A] N'')
    (hf : Function.Injective f) (hfg : Function.Exact f g)
    (hg : Function.Surjective g) :
    depth I N ≥ min (depth I N') (depth I N'') ∧
      depth I N'' ≥ min (depth I N) (depth I N' - 1) ∧
      depth I N' ≥ min (depth I N) (depth I N'' + 1) := by
  sorry

/-! ## Regular elements and extension of regular sequences -/

/-- Quotienting by a nonzerodivisor in `I` lowers `I`-depth by one. -/
theorem depth_quotient_by_regular
    {A M : Type u} [CommRing A] [IsNoetherianRing A]
    [AddCommGroup M] [Module A M] [Module.Finite A M]
    (I : Ideal A) (hIM : I • (⊤ : Submodule A M) ≠ ⊤)
    (x : A) (hx : x ∈ I) (hreg : IsSMulRegular M x) :
    depth I (QuotSMulTop x M) = depth I M - 1 := by
  sorry

/-- An `M`-regular sequence in `I` extends to one whose length is
`depth_I(M)`. -/
theorem regular_sequence_extend_to_depth
    {A M : Type u} [CommRing A] [IsNoetherianRing A]
    [AddCommGroup M] [Module A M] [Module.Finite A M]
    (I : Ideal A) (hIM : I • (⊤ : Submodule A M) ≠ ⊤) :
    ∀ xs : List A, RingTheory.Sequence.IsRegular M xs →
      (∀ x ∈ xs, x ∈ I) →
      ∃ ys : List A,
        RingTheory.Sequence.IsRegular M (xs ++ ys) ∧
          (∀ x ∈ xs ++ ys, x ∈ I) ∧
          depth I M = ((xs ++ ys).length : ℕ∞) := by
  sorry

/-! ## Cohen--Macaulay modules and flat Cohen--Macaulay fibers -/

/-- Truncated subtraction in the `WithBot ℕ∞` dimension convention. -/
def dimensionDifference (a b : WithBot ℕ∞) : WithBot ℕ∞ :=
  WithBot.map₂ (fun x y : ℕ∞ => x - y) a b

/-- The depth formula for a finite Cohen--Macaulay module over a local
Noetherian ring.  `I ≠ ⊤` is the canonical ring-theoretic reading of the
source's “nontrivial ideal” hypothesis. -/
theorem depth_eq_supportDim_sub_supportDim_quotient_of_isCohenMacaulay
    {R M : Type u} [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] [AddCommGroup M] [Module R M]
    [Module.Finite R M]
    (I : Ideal R) (hI : I ≠ ⊤)
    (hM : IsCohenMacaulay R M) :
    ((depth I M : ℕ∞) : WithBot ℕ∞) =
      dimensionDifference (Module.supportDim R M)
        (Module.supportDim R (M ⧸ (I • (⊤ : Submodule R M)))) := by
  sorry

def fiberIdeal
    {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) : Ideal R → Ideal S :=
  fun J => J.map f

abbrev fiberRing
    {R S : Type u} [CommRing R] [CommRing S] [IsLocalRing R]
    (f : R →+* S) : Type u :=
  S ⧸ fiberIdeal f (IsLocalRing.maximalIdeal R)

abbrev fiberCutRing
    {R S : Type u} [CommRing R] [CommRing S] [IsLocalRing R]
    (f : R →+* S) (I : Ideal S) : Type u :=
  S ⧸ (fiberIdeal f (IsLocalRing.maximalIdeal R) ⊔ I)

/-- The fiber Cohen--Macaulay hypothesis, retaining the local-ring instance
needed by the canonical `IsCohenMacaulay` predicate on the quotient fiber. -/
structure FiberIsCohenMacaulay
    {R S : Type u} [CommRing R] [CommRing S] [IsLocalRing R]
    [IsLocalRing S] [IsNoetherianRing R] [IsNoetherianRing S]
    (f : R →+* S) : Prop where
  localRing : IsLocalRing (fiberRing f)
  cm : @IsCohenMacaulay (fiberRing f) (fiberRing f) inferInstance localRing
    inferInstance inferInstance inferInstance inferInstance

/-- A flat local map with Cohen--Macaulay closed fiber gives the source's
depth lower bound.  The term `fiberCutRing` is the unambiguous quotient by
`mS + I` in the displayed source formula. -/
theorem depth_ge_fiber_dimension_sub_cut_dimension
    {R S : Type u} [CommRing R] [CommRing S]
    [IsLocalRing R] [IsLocalRing S] [IsNoetherianRing R]
    [IsNoetherianRing S]
    (f : R →+* S) (hlocal : IsLocalHom f) (hflat : RingHom.Flat f)
    (I : Ideal S) (hfiber : FiberIsCohenMacaulay f) :
    depth I S ≥ dimensionDifference (ringKrullDim (fiberRing f))
      (ringKrullDim (fiberCutRing f I)) := by
  sorry

/-! ## Dividing by ideal-power torsion -/

/-- The canonical module `M[I^∞]`, used as the common `H⁰` value. -/
def idealPowerTorsionModule
    {A M : Type u} [CommRing A] [AddCommGroup M] [Module A M]
    (I : Ideal A) : ModuleCat.{u} A :=
  ModuleCat.of A
    (idealPowerTorsionSubmoduleInfinity (M := M) I)

/-- The quotient by the canonical ideal-power torsion submodule. -/
def torsionFreeQuotient
    {A M : Type u} [CommRing A] [AddCommGroup M] [Module A M]
    (I : Ideal A) : ModuleCat.{u} A :=
  ModuleCat.of A
    (M ⧸ idealPowerTorsionSubmoduleInfinity (M := M) I)

/-- The `H⁰` comparison and all higher-cohomology consequences of dividing a
module by its ideal-power torsion. -/
structure DivideByTorsionData
    {A M : Type u} [CommRing A] [AddCommGroup M] [Module A M]
    [HasDerivedCategory.{w} (ModuleCat.{u} A)] (I : Ideal A) (hI : I.FG) where
  h0_ideal : Nonempty
    (idealLocalCohomologyModule I hI (M := M) 0 ≅
      idealPowerTorsionModule (M := M) I)
  h0_support : Nonempty
    (supportLocalCohomologyModule I hI (M := M) 0 ≅
      idealPowerTorsionModule (M := M) I)
  /- The two `H⁰` isomorphisms to the same canonical object account for the
     source's equality `H⁰_I(M) = H⁰_Z(M)`. -/
  h0_ideal_quotient : IsZero
    (idealLocalCohomologyModule I hI
      (M := (torsionFreeQuotient (M := M) I : Type u)) 0)
  h0_support_quotient : IsZero
    (supportLocalCohomologyModule I hI
      (M := (torsionFreeQuotient (M := M) I : Type u)) 0)
  higher_ideal_torsion : ∀ p : ℤ, 0 < p →
    IsZero (idealLocalCohomologyModule I hI
      (M := (idealPowerTorsionModule (M := M) I : Type u)) p)
  higher_support_torsion : ∀ p : ℤ, 0 < p →
    IsZero (supportLocalCohomologyModule I hI
      (M := (idealPowerTorsionModule (M := M) I : Type u)) p)
  higher_ideal_quotient : ∀ p : ℤ, 0 < p →
    Nonempty (idealLocalCohomologyModule I hI (M := M) p ≅
      idealLocalCohomologyModule I hI
        (M := (torsionFreeQuotient (M := M) I : Type u)) p)
  higher_support_quotient : ∀ p : ℤ, 0 < p →
    Nonempty (supportLocalCohomologyModule I hI (M := M) p ≅
      supportLocalCohomologyModule I hI
        (M := (torsionFreeQuotient (M := M) I : Type u)) p)

theorem divide_by_torsion
    {A M : Type u} [CommRing A]
    [AddCommGroup M] [Module A M]
    [HasDerivedCategory.{w} (ModuleCat.{u} A)]
    (I : Ideal A) (hI : I.FG) :
    Nonempty (DivideByTorsionData (M := M) I hI) := by
  sorry

end

end Formalization.Books.Dualizing.Unit11
