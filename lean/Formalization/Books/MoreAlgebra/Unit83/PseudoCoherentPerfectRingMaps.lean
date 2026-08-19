import Mathlib.RingTheory.KrullDimension.Basic
import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.RingTheory.RingHom.FinitePresentation
import Mathlib.RingTheory.RingHom.Flat
import Formalization.Books.MoreAlgebra.Unit33.Core
import Formalization.Books.MoreAlgebra.Unit67.TorDimension
import Formalization.Books.MoreAlgebra.Unit75.PerfectComplexes
import Formalization.Books.MoreAlgebra.Unit82.RelativelyPseudoCoherent

/-!
# More on Algebra, Chapter 83: Pseudo-coherent and perfect ring maps

This file records the source definitions and theorem interfaces for
pseudo-coherent and perfect ring maps.  Polynomial quotient presentations are
represented by surjective maps from multivariate polynomial rings, and the
derived restriction functor is the canonical one from Chapter 60.
-/

noncomputable section

open CategoryTheory
open Formalization.Books.MoreAlgebra.Unit65
open Formalization.Books.MoreAlgebra.Unit60
open Formalization.Books.MoreAlgebra.Unit67
open Formalization.Books.MoreAlgebra.Unit75
open Formalization.Books.MoreAlgebra.Unit82

universe u

namespace Formalization.Books.MoreAlgebra.Unit83

variable {R A B : Type u} [CommRing R] [CommRing A] [CommRing B]

/-! ## Definitions -/

/- The target copy of `B` is retained as a `B`-module in the first
   conjunct.  The second conjunct explicitly restricts it to an `R`-module,
   as required by the tor-dimension definition. -/
/-- A ring map is pseudo-coherent when it is finite type and its target,
viewed as a module over itself, is pseudo-coherent relative to the source. -/
def IsPseudoCoherentRingMap (f : R →+* A) : Prop :=
  RingHom.FiniteType f ∧
    IsPseudoCoherentRelativeModule f (ModuleCat.of A A)

/-- A pseudo-coherent ring map is perfect when its target has finite Tor
dimension over the source. -/
def IsPerfectRingMap (f : R →+* A) : Prop :=
  IsPseudoCoherentRingMap f ∧
    ModuleHasFiniteTorDimension R
      ((ModuleCat.restrictScalars f).obj (ModuleCat.of A A))

/- A ring map is a local complete intersection map.  Unit33 exposes the
   canonical algebra-form predicate, while this wrapper supplies the algebra
   structure canonically associated to a ring homomorphism. -/
/-- The ring-homomorphism form of the local complete-intersection predicate. -/
def IsLocalCompleteIntersectionHom (f : R →+* A) : Prop :=
  letI : Algebra R A := f.toAlgebra
  Formalization.Books.MoreAlgebra.Unit33.IsLocalCompleteIntersection R A

/-! ## Polynomial-presentation characterizations -/

/-- The source's polynomial-presentation characterization of
pseudo-coherent ring maps. -/
theorem pseudoCoherentRingMap_iff_polynomial_presentation (f : R →+* A) :
    IsPseudoCoherentRingMap f ↔
      letI : Algebra R A := f.toAlgebra
      ∃ (n : ℕ) (α : MvPolynomial (Fin n) R →ₐ[R] A),
        Function.Surjective α ∧
          HasInfiniteFreeResolution (MvPolynomial (Fin n) R)
            ((ModuleCat.restrictScalars α.toRingHom).obj
              (ModuleCat.of A A)) := by
  sorry

/-- A perfect ring map is equivalently a polynomial quotient whose target has
a finite resolution by finite projective modules over the polynomial ring. -/
theorem perfectRingMap_iff_polynomial_presentation (f : R →+* A) :
    IsPerfectRingMap f ↔
      letI : Algebra R A := f.toAlgebra
      ∃ (n : ℕ) (α : MvPolynomial (Fin n) R →ₐ[R] A),
        Function.Surjective α ∧
          FiniteProjectiveResolution (MvPolynomial (Fin n) R)
            ((ModuleCat.restrictScalars α.toRingHom).obj
              (ModuleCat.of A A)) := by
  sorry

/-! ## Basic examples and criteria -/

/- The source says "of Noetherian rings"; both the source and target
   Noetherian hypotheses are therefore kept explicit, although the target
   hypothesis is redundant once finite type over a Noetherian source is used. -/
/-- A finite-type map between Noetherian rings is pseudo-coherent. -/
theorem pseudoCoherentRingMap_of_finiteType_of_noetherian
    (f : R →+* A) (hf : RingHom.FiniteType f)
    [IsNoetherianRing R] [IsNoetherianRing A] :
    IsPseudoCoherentRingMap f := by
  sorry

/-- A flat map of finite presentation is a perfect ring map. -/
theorem perfectRingMap_of_flat_of_finitePresentation
    (f : R →+* A) (hflat : RingHom.Flat f)
    (hfp : RingHom.FinitePresentation f) :
    IsPerfectRingMap f := by
  sorry

/-- A finite-type map out of a regular ring of finite Krull dimension is
perfect. -/
theorem perfectRingMap_of_finiteType_of_regular_finiteDimension
    (f : R →+* A) (hf : RingHom.FiniteType f)
    [IsRegularRing R]
    (hdim : ∃ d : ℕ,
      ringKrullDim R = ((d : ℕ∞) : WithBot ℕ∞)) :
    IsPerfectRingMap f := by
  sorry

/-- Every local complete-intersection homomorphism is a perfect ring map. -/
theorem perfectRingMap_of_localCompleteIntersection
    (f : R →+* A) (hf : IsLocalCompleteIntersectionHom f) :
    IsPerfectRingMap f := by
  sorry

/-! ## Removing relative qualifiers -/

/-- For a pseudo-coherent ring map, relative pseudo-coherence over the source
is the same as ordinary pseudo-coherence over the target. -/
theorem relative_pseudoCoherent_iff_pseudoCoherent
    (f : R →+* A) (hf : IsPseudoCoherentRingMap f)
    (m : ℤ) (K : Formalization.Books.MoreAlgebra.Unit82.D A) :
    (IsMPseudoCoherentRelativeObject f m K ↔
      IsMPseudoCoherent A m K) ∧
      (IsPseudoCoherentRelativeObject f K ↔ IsPseudoCoherent A K) := by
  sorry

/- The source's `φ_* K` is represented by the canonical derived restriction
   functor, whose complex-level representation is supplied by Unit60. -/
/-- The five-way pseudo-coherence equivalence for a surjective intermediate
ring map, together with its `m`-pseudo-coherent analogue. -/
theorem relative_pseudoCoherent_five_way
    (f : R →+* B) (g : B →+* A) (hg : Function.Surjective g)
    (hflatf : RingHom.Flat f)
    (hfp_f : RingHom.FinitePresentation f)
    (hflatgf : RingHom.Flat (g.comp f))
    (hfp_gf : RingHom.FinitePresentation (g.comp f))
    (K : Formalization.Books.MoreAlgebra.Unit82.D A) :
    List.TFAE
      [ IsPseudoCoherent A K,
        IsPseudoCoherentRelativeObject (g.comp f) K,
        IsPseudoCoherentRelativeObject (RingHom.id A) K,
        IsPseudoCoherent B ((derivedRestrictionFunctor g).obj K),
        IsPseudoCoherentRelativeObject f
          ((derivedRestrictionFunctor g).obj K) ] ∧
      (∀ m : ℤ, List.TFAE
        [ IsMPseudoCoherent A m K,
          IsMPseudoCoherentRelativeObject (g.comp f) m K,
          IsMPseudoCoherentRelativeObject (RingHom.id A) m K,
          IsMPseudoCoherent B m ((derivedRestrictionFunctor g).obj K),
          IsMPseudoCoherentRelativeObject f m
            ((derivedRestrictionFunctor g).obj K) ]) := by
  sorry

end Formalization.Books.MoreAlgebra.Unit83
