import Formalization.Books.MoreAlgebra.Unit65.PseudoCoherentModules
import Formalization.Books.MoreAlgebra.Unit67.TorDimension
import Formalization.Books.MoreAlgebra.Unit69.ProjectiveDimension
import Formalization.Books.MoreAlgebra.Unit74.DerivedHom
import Formalization.Books.MoreAlgebra.Unit60.DerivedBaseChange
import Formalization.Books.Derived.Unit34.DerivedLimits
import Formalization.Books.Derived.Unit37.CompactObjects
import Formalization.Books.Algebra.Unit110.RegularRingsAndGlobalDimension
import Mathlib.RingTheory.Noetherian.Basic

/-!
# More on Algebra, Chapter 75: Perfect complexes

This file records the definitions and theorem interfaces in the first section
of the chapter.  The perfect predicate uses the bounded finite-projective
representative supplied by the preceding pseudo-coherence and derived-category
interfaces.
-/

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Preadditive
open CategoryTheory.Pretriangulated
open CategoryTheory.Triangulated
open Formalization.Books.Derived.Unit08
open Formalization.Books.Derived.Unit11
open Formalization.Books.Derived.Unit33
open Formalization.Books.Derived.Unit34
open Formalization.Books.Derived.Unit36
open Formalization.Books.Derived.Unit37
open Formalization.Books.MoreAlgebra.Unit65
open Formalization.Books.MoreAlgebra.Unit67
open Formalization.Books.MoreAlgebra.Unit69
open Formalization.Books.MoreAlgebra.Unit74
open Formalization.Books.MoreAlgebra.Unit60
open scoped CategoryTheory.Pretriangulated.Opposite ZeroObject

universe w u

namespace Formalization.Books.MoreAlgebra.Unit75

abbrev Mod (R : Type u) [CommRing R] := ModuleCat.{u} R

abbrev Comp (R : Type u) [CommRing R] := Unit65.Comp R

abbrev D (R : Type u) [CommRing R]
    [HasDerivedCategory.{w} (Mod R)] := Unit65.D R

noncomputable abbrev derivedQuotient (R : Type u) [CommRing R]
    [HasDerivedCategory.{w} (Mod R)] : Comp R ⥤ D R :=
  Unit59.derivedComplexQuotient R

noncomputable abbrev moduleInDerived (R : Type u) [CommRing R]
    [HasDerivedCategory.{w} (Mod R)] (M : Mod R) : D R :=
  Unit65.moduleInDerived R M

noncomputable abbrev derivedBaseChange
    {A B : Type u} [CommRing A] [CommRing B]
    [HasDerivedCategory.{w} (Mod A)] [HasDerivedCategory.{w} (Mod B)]
    (f : A →+* B) : D A ⥤ D B :=
  Unit63.derivedBaseChange f

/-! ## Definitions -/

def BoundedFiniteProjectiveComplex (R : Type u) [CommRing R] (E : Comp R) : Prop :=
  IsBounded E ∧ ∀ i : ℤ, FiniteProjectiveModule R (E.X i)

def FiniteProjectiveResolution (R : Type u) [CommRing R]
    [HasDerivedCategory.{w} (Mod R)] (M : Mod R) : Prop :=
  ∃ d : ℕ, ∃ E : Comp R,
    (∀ i : ℤ, i < -(d : ℤ) ∨ 0 < i → IsZero (E.X i)) ∧
    (∀ i : ℤ, -(d : ℤ) ≤ i → i ≤ 0 → FiniteProjectiveModule R (E.X i)) ∧
    Nonempty ((derivedQuotient R).obj E ≅ moduleInDerived R M)

def Perfect (R : Type u) [CommRing R]
    [HasDerivedCategory.{w} (Mod R)] (K : D R) : Prop :=
  ∃ E : Comp R,
    BoundedFiniteProjectiveComplex R E ∧
      Nonempty ((derivedQuotient R).obj E ≅ K)

def PerfectModule (R : Type u) [CommRing R]
    [HasDerivedCategory.{w} (Mod R)] (M : Mod R) : Prop :=
  Perfect R (moduleInDerived R M)

def IsDistinguishedTriangle (R : Type u) [CommRing R]
    [HasDerivedCategory.{w} (Mod R)] (T : Triangle (D R)) : Prop :=
  T ∈ distTriang (D R)

theorem perfect_iff_pseudoCoherent_and_finite_tor_dimension
    (R : Type u) [CommRing R]
    [HasDerivedCategory.{w} (Mod R)] (K : D R) :
    Perfect R K ↔
      IsPseudoCoherent R K ∧ HasFiniteTorDimension R K := by
  sorry

theorem perfect_has_finite_projective_representative
    (R : Type u) [CommRing R]
    [HasDerivedCategory.{w} (Mod R)] (K : D R) (a b : ℤ)
    (hK : Perfect R K) (hamp : TorAmplitude R K a b) :
    ∃ E : Comp R,
      (∀ i : ℤ, i ∉ Set.Icc a b → IsZero (E.X i)) ∧
      (∀ i : ℤ, i ∈ Set.Icc a b → FiniteProjectiveModule R (E.X i)) ∧
      Nonempty ((derivedQuotient R).obj E ≅ K) := by
  sorry

theorem perfect_module_iff_finite_projective_resolution
    (R : Type u) [CommRing R]
    [HasDerivedCategory.{w} (Mod R)] (M : Mod R) :
    PerfectModule R M ↔ FiniteProjectiveResolution R M := by
  sorry

theorem perfect_two_out_of_three
    (R : Type u) [CommRing R]
    [HasDerivedCategory.{w} (Mod R)] (T : Triangle (D R))
    (hT : IsDistinguishedTriangle R T) :
    ((Perfect R T.obj₁ ∧ Perfect R T.obj₂) → Perfect R T.obj₃) ∧
      ((Perfect R T.obj₁ ∧ Perfect R T.obj₃) → Perfect R T.obj₂) ∧
      ((Perfect R T.obj₂ ∧ Perfect R T.obj₃) → Perfect R T.obj₁) := by
  sorry

theorem perfect_of_biproduct
    (R : Type u) [CommRing R]
    [HasDerivedCategory.{w} (Mod R)] {K L : D R}
    (hKL : Perfect R (K ⊞ L)) :
    Perfect R K ∧ Perfect R L := by
  sorry

theorem perfect_of_bounded_complex_of_perfect_modules
    (R : Type u) [CommRing R]
    [HasDerivedCategory.{w} (Mod R)] (E : Comp R)
    (hbounded : IsBounded E)
    (hterms : ∀ i : ℤ, PerfectModule R (E.X i)) :
    Perfect R ((derivedQuotient R).obj E) := by
  sorry

theorem perfect_of_bounded_object_with_perfect_cohomology
    (R : Type u) [CommRing R]
    [HasDerivedCategory.{w} (Mod R)] (K : D R)
    (hbounded : derivedBoundedProperty (Mod R) K)
    (hcoh : ∀ i : ℤ,
      PerfectModule R ((derivedCohomologyFunctor (Mod R) i).obj K)) :
    Perfect R K := by
  sorry

theorem perfect_pushforward
    {A B : Type u} [CommRing A] [CommRing B]
    [HasDerivedCategory.{w} (Mod A)] [HasDerivedCategory.{w} (Mod B)]
    (f : A →+* B) (K : D B)
    (hB : PerfectModule A (ringMapModule f)) (hK : Perfect B K) :
    Perfect A ((Unit60.derivedRestrictionFunctor f).obj K) := by
  sorry

theorem perfect_pullback
    {A B : Type u} [CommRing A] [CommRing B]
    [HasDerivedCategory.{w} (Mod A)] [HasDerivedCategory.{w} (Mod B)]
    (f : A →+* B) (K : D A) (hK : Perfect A K) :
    Perfect B ((derivedPullback f).obj K) := by
  sorry

theorem perfect_module_flat_base_change
    {A B : Type u} [CommRing A] [CommRing B]
    [HasDerivedCategory.{w} (Mod A)] [HasDerivedCategory.{w} (Mod B)]
    (f : A →+* B) (hf : f.Flat) (M : Mod A)
    (hM : PerfectModule A M) :
    PerfectModule B ((ModuleCat.extendScalars f).obj M) := by
  sorry

theorem perfect_tensor
    (R : Type u) [CommRing R]
    [HasDerivedCategory.{w} (Mod R)] {K L : D R}
    (hK : Perfect R K) (hL : Perfect R L) :
    Perfect R (Unit74.derivedTensor K L) := by
  sorry

theorem perfect_localization_glue
    (R : Type u) [CommRing R]
    [HasDerivedCategory.{w} (Mod R)] {n : ℕ} (f : Fin n → R)
    (hunit : Ideal.span (Set.range f) = ⊤) (K : D R)
    (hlocalDC : ∀ i : Fin n,
      HasDerivedCategory.{w} (ModuleCat.{u} (Localization.Away (f i))))
    (hlocal : ∀ i : Fin n,
      letI := hlocalDC i
      Perfect (Localization.Away (f i))
        ((Formalization.Books.MoreAlgebra.Unit63.derivedBaseChange
          (algebraMap R (Localization.Away (f i)))).obj K)) :
    Perfect R K := by
  sorry

theorem perfect_faithfully_flat_descent
    {R S : Type u} [CommRing R] [CommRing S]
    [HasDerivedCategory.{w} (Mod R)] [HasDerivedCategory.{w} (Mod S)]
    (f : R →+* S) (hfaithful : f.FaithfullyFlat) (K : D R)
    (hK : Perfect S
      ((Formalization.Books.MoreAlgebra.Unit63.derivedBaseChange f).obj K)) :
    Perfect R K := by
  sorry

theorem regular_ring_perfect_module_iff_finite
    (R : Type u) [CommRing R] [IsNoetherianRing R]
    (hR : IsRegularRing R)
    [HasDerivedCategory.{w} (Mod R)] (M : Mod R) :
    PerfectModule R M ↔ FiniteType R M := by
  sorry

theorem regular_ring_perfect_iff_bounded_finite_cohomology
    (R : Type u) [CommRing R] [IsNoetherianRing R]
    (hR : IsRegularRing R)
    [HasDerivedCategory.{w} (Mod R)] (K : D R) :
    Perfect R K ↔
      derivedBoundedProperty (Mod R) K ∧
        ∀ i : ℤ, FiniteType R ((derivedCohomologyFunctor (Mod R) i).obj K) := by
  sorry

/-! ## Duality -/

noncomputable def perfectDual
    (R : Type u) [CommRing R]
    [HasDerivedCategory.{w} (Mod R)] (K : D R) : D R :=
  Unit74.RHom K (moduleInDerived R (ModuleCat.of R R))

theorem perfect_dual
    (R : Type u) [CommRing R]
    [HasDerivedCategory.{w} (Mod R)] (K : D R) (hK : Perfect R K) :
    Perfect R (perfectDual R K) ∧
      Nonempty (K ≅ perfectDual R (perfectDual R K)) := by
  sorry

theorem perfect_dual_tensor_hom
    (R : Type u) [CommRing R]
    [HasDerivedCategory.{w} (Mod R)] (K L : D R) (hK : Perfect R K) :
    Nonempty (Unit74.derivedTensor L (perfectDual R K) ≅ Unit74.RHom K L) := by
  sorry

theorem perfect_dual_cohomology_zero
    (R : Type u) [CommRing R]
    [HasDerivedCategory.{w} (Mod R)] (K L : D R) (hK : Perfect R K) :
    Nonempty ((derivedCohomologyFunctor (Mod R) 0).obj
      (Unit74.derivedTensor L (perfectDual R K)) ≅
      (derivedCohomologyFunctor (Mod R) 0).obj (Unit74.RHom K L)) := by
  sorry

theorem perfect_dual_tor_amplitude
    (R : Type u) [CommRing R]
    [HasDerivedCategory.{w} (Mod R)] (K : D R) (a b : ℤ)
    (hK : Perfect R K) (hamp : TorAmplitude R K a b) :
    TorAmplitude R (perfectDual R K) (-b) (-a) := by
  sorry

noncomputable def perfectDualInverseSystem
    (R : Type u) [CommRing R]
    [HasDerivedCategory.{w} (Mod R)]
    (F : SequentialSystem (D R)) (E : D R) :
    DerivedInverseSystem (D R) :=
  (F.op.prod' ((Functor.const (ℕᵒᵖ)).obj E)) ⋙
    Unit74.derivedHomFunctor (R := R)

theorem perfect_hocolim_dual
    (R : Type u) [CommRing R]
    [HasDerivedCategory.{w} (Mod R)] (F : SequentialSystem (D R))
    (hF : ∀ n : ℕ, Perfect R (F.obj n)) (K E : D R)
    (hK : IsDerivedColimit F K)
    (hlim : ∃ L : D R,
      IsDerivedLimit (perfectDualInverseSystem R F E) L) :
    Nonempty (Unit74.RHom K E ≅
      derivedLimit (perfectDualInverseSystem R F E) hlim) := by
  sorry

/-! A filtered colimit of rings is handled categorically by a filtered diagram
of `CommRingCat`; the two source assertions are recorded in one interface. -/

theorem perfect_descends_through_filtered_ring_colimit
    {J : Type u} [Category.{u} J] [IsFiltered J]
    (F : J ⥤ CommRingCat.{u}) (C : Cocone F) (hC : IsColimit C)
    [hCderived : HasDerivedCategory.{w} (Mod (C.pt : Type u))]
    (hstageDC : ∀ j : J,
      HasDerivedCategory.{w} (Mod (F.obj j : Type u)))
    (K : D (C.pt : Type u)) (hK : Perfect (C.pt : Type u) K) :
    ∃ j : J, letI := hstageDC j
      letI : HasDerivedCategory.{w} (Mod (C.pt : Type u)) := hCderived
      ∃ Kj : D (F.obj j : Type u), Perfect (F.obj j : Type u) Kj ∧
        Nonempty ((derivedBaseChange (A := (F.obj j : Type u))
          (B := (C.pt : Type u)) (C.ι.app j).hom).obj Kj ≅ K) := by
  sorry

end Formalization.Books.MoreAlgebra.Unit75
