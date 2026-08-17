import Formalization.Books.Algebra.Unit03.BasicNotions
import Formalization.Books.Algebra.Unit99.CriteriaForFlatness
import Formalization.Books.Algebra.Unit101.FlatnessCriteriaArtinian
import Formalization.Books.Algebra.Unit104.CohenMacaulayRings
import Formalization.Books.Algebra.Unit106.RegularLocalRings
import Formalization.Books.Algebra.Unit127.ColimitsAndFinitePresentation
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.RingTheory.Localization.AtPrime.Basic

/-!
# Commutative Algebra, Chapter 128: More flatness criteria

This file records the source-facing interfaces in the section.  The local,
Cohen--Macaulay, regular-local, regular-sequence, finite-presentation,
restricted-scalar, Tor, and fibre constructions are the canonical interfaces
from earlier chapters and Mathlib.

The displayed Tor kernel identity and the localization diagrams in the source
are proof scaffolding for the surrounding lemmas.  They are therefore
accounted for in the theorem interfaces rather than duplicated as unreferenced
maps.
-/

namespace Formalization.Books.Algebra.Unit128

open Formalization.Books.Algebra.Unit60
open Formalization.Books.Algebra.Unit101
open Formalization.Books.Algebra.Unit104
open Formalization.Books.Algebra.Unit127
open CategoryTheory
open CategoryTheory.Limits

universe u

noncomputable section

/-! ## Shared source-facing notation -/

/-- The extension to `S` of the maximal ideal of the local base ring `R`. -/
def mappedMaximalIdeal
    {R S : Type u} [CommRing R] [CommRing S] [IsLocalRing R]
    (f : R →+* S) : Ideal S :=
  Ideal.map f (IsLocalRing.maximalIdeal R)

/-- Injectivity of the map induced by an `S`-linear map on the residue modules
of a local map.  The two quotients use the extension of the base maximal ideal,
which is the canonical `S`-module presentation of `m M` and `m N`. -/
def residueMapInjective
    {R S M N : Type u} [CommRing R] [CommRing S] [IsLocalRing R]
    [AddCommGroup M] [Module S M] [AddCommGroup N] [Module S N]
    (f : R →+* S) (u : M →ₗ[S] N) : Prop :=
  Function.Injective
    ((mappedMaximalIdeal f • (⊤ : Submodule S M)).mapQ
      (mappedMaximalIdeal f • (⊤ : Submodule S N)) u
      (Submodule.smul_top_le_comap_smul_top
        (mappedMaximalIdeal f) u))

/-! ## Miracle flatness and regular parameters -/

/-- Miracle flatness: the dimension formula forces a local map from a regular
local ring to a Cohen--Macaulay local ring to be flat. -/
theorem miracle_flatness
    {R S : Type u} [CommRing R] [CommRing S]
    [IsLocalRing R] [IsLocalRing S]
    [IsNoetherianRing R] [IsNoetherianRing S]
    (f : R →+* S) [IsLocalHom f]
    (hR : IsRegularLocalRing R)
    (hS : IsCohenMacaulayLocalRing S)
    (hdim : ringKrullDim S =
      ringKrullDim R + ringKrullDim (S ⧸ mappedMaximalIdeal f)) :
    RingHom.Flat f := by
  sorry

/-- A regular system of parameters of a regular local base that becomes a
regular sequence in the target gives a flat local ring map. -/
theorem flat_of_regular_system_of_parameters
    {R S : Type u} [CommRing R] [CommRing S]
    [IsLocalRing R] [IsLocalRing S]
    [IsNoetherianRing R] [IsNoetherianRing S]
    (f : R →+* S) [IsLocalHom f]
    (hR : IsRegularLocalRing R) (d : ℕ) (x : Fin d → R)
    (hx : IsRegularSystemOfParameters R d x)
    (hxs : RingTheory.Sequence.IsRegular S
      (List.ofFn (fun i => f (x i)))) :
    RingHom.Flat f := by
  sorry

/-! ## Directed colimits and finite presentation -/

/-- In a Chapter 127 local essentially-finite-presentation module colimit, a
flat target module is already flat over one of the source stages. -/
theorem colimit_eventually_flat
    {R S M : Type u} [CommRing R] [CommRing S]
    [IsLocalRing R] [IsLocalRing S] {f : R →+* S} [IsLocalHom f]
    [AddCommGroup M] [Module S M]
    (D : DirectedLocalModuleEssentiallyFinitePresentation (M := M) f)
    (hflat : Module.Flat R
      ((ModuleCat.restrictScalars f).obj (ModuleCat.of S M))) :
    ∃ i, letI : Preorder D.ringApproximation.base.colimit.index :=
        D.ringApproximation.base.colimit.indexPreorder
      letI : Module
          (D.ringApproximation.base.colimit.sourceDiagram.obj i)
          (D.moduleApproximation.stage i).module :=
        Module.compHom (D.moduleApproximation.stage i).module
          (D.ringApproximation.base.colimit.stageMap i)
      Module.Flat
        (D.ringApproximation.base.colimit.sourceDiagram.obj i)
        (D.moduleApproximation.stage i).module := by
  sorry

/-! ## Local maps and finitely presented modules -/

/-- The general finite-presentation version of the injectivity criterion: a
residue-injective map has injective source map and flat quotient. -/
theorem mod_injective_general
    {R S M N : Type u} [CommRing R] [CommRing S]
    [IsLocalRing R] [IsLocalRing S]
    (f : R →+* S) [IsLocalHom f]
    [AddCommGroup M] [Module S M] [AddCommGroup N] [Module S N]
    (hS : f.EssFinitePresentation)
    (hM : Module.FinitePresentation S M)
    (hN : Module.FinitePresentation S N)
    (hNflat : Module.Flat R
      ((ModuleCat.restrictScalars f).obj (ModuleCat.of S N)))
    (u : M →ₗ[S] N)
    (hbar : residueMapInjective f u) :
    Function.Injective u ∧
      Module.Flat R
        ((ModuleCat.restrictScalars f).obj
          (ModuleCat.of S (N ⧸ LinearMap.range u))) := by
  sorry

/-- The general Grothendieck criterion for a regular element in the closed
fibre. -/
theorem grothendieck_general
    {R S : Type u} [CommRing R] [CommRing S]
    [IsLocalRing R] [IsLocalRing S]
    (f : R →+* S) [IsLocalHom f]
    (hS : f.EssFinitePresentation)
    (hflat : Module.Flat R
      ((ModuleCat.restrictScalars f).obj (ModuleCat.of S S)))
    (g : S)
    (hg : IsSMulRegular
      (S ⧸ (mappedMaximalIdeal f : Submodule S S)) g) :
    Module.Flat R
        ((ModuleCat.restrictScalars f).obj
          (ModuleCat.of S
            (S ⧸ (Ideal.span ({g} : Set S) : Submodule S S)))) ∧
      IsSMulRegular S g := by
  sorry

/-- The regular-sequence version of the general Grothendieck criterion. -/
theorem grothendieck_regular_sequence_general
    {R S : Type u} [CommRing R] [CommRing S]
    [IsLocalRing R] [IsLocalRing S]
    (f : R →+* S) [IsLocalHom f]
    (hS : f.EssFinitePresentation)
    (hflat : Module.Flat R
      ((ModuleCat.restrictScalars f).obj (ModuleCat.of S S)))
    (xs : List S)
    (hxs : RingTheory.Sequence.IsRegular
      (S ⧸ (mappedMaximalIdeal f : Submodule S S))
      (xs.map (Ideal.Quotient.mk (mappedMaximalIdeal f)))) :
    RingTheory.Sequence.IsRegular S xs ∧
      (∀ i : Fin xs.length,
        Module.Flat R
          ((ModuleCat.restrictScalars f).obj
            (ModuleCat.of S
              (S ⧸ (Ideal.ofList (xs.take (i.1 + 1)) : Submodule S S))))) := by
  sorry

/-- The local finite-presentation Tor criterion for flatness. -/
theorem variant_local_criterion_flatness_general
    {R S M : Type u} [CommRing R] [CommRing S]
    [IsLocalRing R] [IsLocalRing S]
    (f : R →+* S) [IsLocalHom f]
    [AddCommGroup M] [Module S M]
    (hS : f.EssFinitePresentation)
    (hM : Module.FinitePresentation S M)
    (I : Ideal R) (hI : I ≠ ⊤)
    (hTor :
      letI : Module R M := Module.compHom M f
      IsZero
        (Formalization.Books.Algebra.Unit99.tor
          (R := R) M (R ⧸ I) 1))
    (hflat :
      letI : Module R M := Module.compHom M f
      Module.Flat (R ⧸ I)
        (M ⧸ (I • (⊤ : Submodule R M)))) :
    Module.Flat R
      ((ModuleCat.restrictScalars f).obj (ModuleCat.of S M)) := by
  sorry

/-! ## Fibre criteria -/

/-- The fibre criterion for a chain of local ring maps. -/
theorem criterion_flatness_fibre
    {R S S' M : Type u} [CommRing R] [CommRing S] [CommRing S']
    [IsLocalRing R] [IsLocalRing S] [IsLocalRing S']
    (f : R →+* S) (g : S →+* S') (h : R →+* S')
    [IsLocalHom f] [IsLocalHom g] [IsLocalHom h]
    (comm : g.comp f = h)
    [AddCommGroup M] [Module S' M]
    (hS : f.EssFinitePresentation)
    (hS' : h.EssFinitePresentation)
    (hM : Module.FinitePresentation S' M)
    (hMnonzero : Nontrivial M)
    (hflat_fibre :
      letI : Module S M := Module.compHom M g
      Module.Flat (S ⧸ (mappedMaximalIdeal f : Submodule S S))
        (M ⧸ (mappedMaximalIdeal f • (⊤ : Submodule S M))))
    (hflat_base : Module.Flat R
      ((ModuleCat.restrictScalars h).obj (ModuleCat.of S' M))) :
    Module.Flat R
        ((ModuleCat.restrictScalars f).obj (ModuleCat.of S S)) ∧
      Module.Flat S
        ((ModuleCat.restrictScalars g).obj (ModuleCat.of S' M)) := by
  sorry

/-- The fibre criterion when the intermediate map is initially only
essentially of finite type. -/
theorem criterion_flatness_fibre_fp_over_ft
    {R S S' M : Type u} [CommRing R] [CommRing S] [CommRing S']
    [IsLocalRing R] [IsLocalRing S] [IsLocalRing S']
    (f : R →+* S) (g : S →+* S') (h : R →+* S')
    [IsLocalHom f] [IsLocalHom g] [IsLocalHom h]
    (comm : g.comp f = h)
    [AddCommGroup M] [Module S' M]
    (hS' : h.EssFinitePresentation)
    (hS : f.EssFiniteType)
    (hM : Module.FinitePresentation S' M)
    (hMnonzero : Nontrivial M)
    (hflat_fibre :
      letI : Module S M := Module.compHom M g
      Module.Flat (S ⧸ (mappedMaximalIdeal f : Submodule S S))
        (M ⧸ (mappedMaximalIdeal f • (⊤ : Submodule S M))))
    (hflat_base : Module.Flat R
      ((ModuleCat.restrictScalars h).obj (ModuleCat.of S' M))) :
    f.EssFinitePresentation ∧
      Module.Flat R
        ((ModuleCat.restrictScalars f).obj (ModuleCat.of S S)) ∧
      Module.Flat S
        ((ModuleCat.restrictScalars g).obj (ModuleCat.of S' M)) := by
  sorry

/-- The fibre criterion over a locally nilpotent ideal.  The nonzero-fibre
condition is the existing Chapter 101 `nontrivialFibreAt` predicate, and the
stalk conclusion is expressed by the canonical localized ring map. -/
theorem criterion_flatness_fibre_locally_nilpotent
    {R S S' M : Type u} [CommRing R] [CommRing S] [CommRing S']
    (f : R →+* S) (g : S →+* S') (h : R →+* S')
    (comm : g.comp f = h) (I : Ideal R)
    (hI : Formalization.Books.Algebra.Unit03.locallyNilpotentIdeal I)
    [AddCommGroup M] [Module S' M]
    (hfinite : f.FiniteType)
    (hfp : h.FinitePresentation)
    (hM : Module.FinitePresentation S' M)
    (hflat_fibre :
      letI : Module S M := Module.compHom M g
      Module.Flat (S ⧸ (I.map f))
        (M ⧸ ((I.map f) • (⊤ : Submodule S M))))
    (hflat_base : Module.Flat R
      ((ModuleCat.restrictScalars h).obj (ModuleCat.of S' M))) :
    Module.Flat S
        ((ModuleCat.restrictScalars g).obj (ModuleCat.of S' M)) ∧
      ∀ q : PrimeSpectrum S,
        nontrivialFibreAt (M := M) g q →
          RingHom.EssFinitePresentation
              ((algebraMap S (Localization.AtPrime q.asIdeal)).comp f) ∧
            RingHom.Flat
              ((algebraMap S (Localization.AtPrime q.asIdeal)).comp f) := by
  sorry

end

end Formalization.Books.Algebra.Unit128
