import Formalization.Books.Algebra.Unit37.NormalRings
import Formalization.Books.Algebra.Unit104.CohenMacaulayRings
import Formalization.Books.Algebra.Unit157.SerresCriterion
import Mathlib.RingTheory.Ideal.Quotient.Noetherian
import Mathlib.RingTheory.LocalRing.ResidueField.Fiber
import Mathlib.RingTheory.RingHom.Flat
import Mathlib.RingTheory.RingHom.Smooth
import Mathlib.RingTheory.TensorProduct.Finite
import Mathlib.RingTheory.RegularLocalRing.Defs

/-!
# Commutative Algebra, Chapter 163: Ascending properties

This file records the source statements about ascent of depth, Cohen–Macaulayness,
Serre's conditions, reducedness, normality, and regularity.  The chapter uses
the canonical predicates from Chapters 37, 72, 103, 104, and 157.
-/

namespace Formalization.Books.Algebra.Unit163

open Formalization.Books.Algebra.Unit37
open Formalization.Books.Algebra.Unit72
open Formalization.Books.Algebra.Unit103
open Formalization.Books.Algebra.Unit104
open Formalization.Books.Algebra.Unit157
open scoped TensorProduct

universe u v

noncomputable section

/- The ring map determines the scalar structure used by the canonical
   residue-field fibre.  This small abbreviation prevents the fibre
   hypotheses below from losing the map `f` at elaboration time. -/
abbrev fiberRing
    {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) (p : PrimeSpectrum R) : Type _ :=
  letI : Algebra R S := f.toAlgebra
  p.asIdeal.Fiber S

/-! ## Ascending depth -/

/-- The source's module form of the depth formula.  The tensor product is
represented in the order `N ⊗[R] M`, so its `S`-module structure is the
canonical one coming from the first factor; this is canonically symmetric to
the source's `M ⊗[R] N`.  The depth of the fibre is written as the depth of
`N` at the extended maximal ideal, the standard quotient-module realization
of `N / 𝔪_R N`. -/
theorem depth_tensorProduct_eq_add
    {R S : Type u} {M N : Type v} [CommRing R] [CommRing S]
    [IsLocalRing R] [IsLocalRing S]
    [IsNoetherianRing R] [IsNoetherianRing S]
    [AddCommGroup M] [Module R M] [Module.Finite R M]
    [AddCommGroup N] [Module S N] [Module.Finite S N]
    (f : R →+* S)
    (hNflat : @Module.Flat R N _ _ (Module.compHom N f)) [IsLocalHom f] :
    letI : Algebra R S := f.toAlgebra
    letI : Module R N := Module.compHom N f
    letI : IsScalarTower R S N := SMul.comp.isScalarTower f
    letI : SMulCommClass R S N := ⟨by
      intro r s n
      change f r • s • n = s • f r • n
      rw [smul_comm]⟩
    letI : Module S (TensorProduct R N M) := TensorProduct.leftModule
    letI : IsScalarTower R S (TensorProduct R N M) :=
      TensorProduct.isScalarTower_left
    letI : Module.Finite S (TensorProduct R N M) :=
      Module.Finite.of_restrictScalars_finite R S (TensorProduct R N M)
    localDepth S (TensorProduct R N M) =
      localDepth R M + depth (Ideal.map f (IsLocalRing.maximalIdeal R)) N := by
  sorry

/-- The ring form of the depth formula, obtained by taking `M = R` in the
module statement. -/
theorem depth_eq_add_depth_fibre
    {R S : Type u} [CommRing R] [CommRing S]
    [IsLocalRing R] [IsLocalRing S]
    [IsNoetherianRing R] [IsNoetherianRing S]
    (f : R →+* S) (hflat : RingHom.Flat f) [IsLocalHom f] :
    letI : Algebra R S := f.toAlgebra
    localDepth S S =
      localDepth R R + depth (Ideal.map f (IsLocalRing.maximalIdeal R)) S := by
  sorry

/-- Cohen–Macaulayness ascends along a flat local map exactly when it holds
for the base and for the closed fibre. -/
theorem cohenMacaulay_goes_up
    {R S : Type u} [CommRing R] [CommRing S]
    [IsLocalRing R] [IsLocalRing S]
    [IsNoetherianRing R] [IsNoetherianRing S]
    (f : R →+* S) (hflat : RingHom.Flat f) [IsLocalHom f] :
    IsCohenMacaulayLocalRing S ↔
      IsCohenMacaulayLocalRing R ∧
        ∃ hlocal : IsLocalRing (S ⧸ Ideal.map f (IsLocalRing.maximalIdeal R)),
          letI : IsLocalRing (S ⧸ Ideal.map f (IsLocalRing.maximalIdeal R)) := hlocal
          IsCohenMacaulayLocalRing (S ⧸ Ideal.map f (IsLocalRing.maximalIdeal R)) := by
  sorry

/-! ## Serre conditions -/

/-- Property `(S_k)` ascends along a flat map when it holds on the base and
on every residue-field fibre. -/
theorem propertySk_goes_up
    {R S : Type u} [CommRing R] [CommRing S]
    [IsNoetherianRing R] [IsNoetherianRing S]
    (f : R →+* S) (hflat : RingHom.Flat f) (k : ℕ)
    (hSkR : HasPropertySk R k)
    (hSkFib : ∀ p : PrimeSpectrum R, HasPropertySk (fiberRing f p) k) :
    HasPropertySk S k := by
  sorry

/-- Property `(R_k)` ascends along a flat map when it holds on the base and
on every residue-field fibre. -/
theorem propertyRk_goes_up
    {R S : Type u} [CommRing R] [CommRing S]
    [IsNoetherianRing R] [IsNoetherianRing S]
    (f : R →+* S) (hflat : RingHom.Flat f) (k : ℕ)
    (hRkR : HasPropertyRk R k)
    (hRkFib : ∀ p : PrimeSpectrum R, HasPropertyRk (fiberRing f p) k) :
    HasPropertyRk S k := by
  sorry

/-! ## Reduced, normal, and regular rings -/

/-- Reducedness ascends along a flat map of Noetherian rings with reduced
fibres. -/
theorem reduced_goes_up_noetherian
    {R S : Type u} [CommRing R] [CommRing S]
    [IsNoetherianRing R] [IsNoetherianRing S]
    (f : R →+* S) (hflat : RingHom.Flat f)
    (hredR : IsReduced R)
    (hredFib : ∀ p : PrimeSpectrum R, IsReduced (fiberRing f p)) :
    IsReduced S := by
  sorry

/-- Reducedness ascends along a smooth map. -/
theorem reduced_goes_up
    {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) (hsmooth : RingHom.Smooth f)
    (hredR : IsReduced R) :
    IsReduced S := by
  sorry

/-- Normality ascends along a flat map of Noetherian rings with normal
fibres. -/
theorem normal_goes_up_noetherian
    {R S : Type u} [CommRing R] [CommRing S]
    [IsNoetherianRing R] [IsNoetherianRing S]
    (f : R →+* S) (hflat : RingHom.Flat f)
    (hnormalR : IsNormalRing R)
    (hnormalFib : ∀ p : PrimeSpectrum R, IsNormalRing (fiberRing f p)) :
    IsNormalRing S := by
  sorry

/-- Normality ascends along a smooth map. -/
theorem normal_goes_up
    {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) (hsmooth : RingHom.Smooth f)
    (hnormalR : IsNormalRing R) :
    IsNormalRing S := by
  sorry

/-- Regularity ascends along a smooth map. -/
theorem regular_goes_up
    {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) (hsmooth : RingHom.Smooth f)
    (hregularR : IsRegularRing R) :
    IsRegularRing S := by
  sorry

end

end Formalization.Books.Algebra.Unit163
