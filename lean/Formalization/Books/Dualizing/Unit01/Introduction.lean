import Mathlib.Algebra.Homology.DerivedCategory.Plus
import Formalization.Books.MoreAlgebra.Unit70.InjectiveDimension
import Formalization.Books.MoreAlgebra.Unit74.DerivedHom

/-!
# Dualizing Complexes, Chapter 1: Introduction

The numbered source section is introductory prose, except for the definition
of a dualizing complex over a Noetherian ring.  The bounded-below derived
category, finite cohomology modules, finite injective dimension, and derived
internal Hom all use the earlier project APIs.
-/

namespace Formalization.Books.Dualizing.Unit01

open CategoryTheory
open Formalization.Books.Derived.Unit11
open Formalization.Books.Derived.Unit27
open Formalization.Books.MoreAlgebra.Unit70
open Formalization.Books.MoreAlgebra.Unit74

universe u w

noncomputable section

/-! ## The self-duality map -/

/- The earlier derived-Hom API supplies `RHom`, but does not expose the
canonical unit map from the regular derived module to `RHom K K`.  The
source-facing interface therefore records the map together with the
condition that it is an isomorphism in the derived category (the derived
category formulation of being a quasi-isomorphism). -/
structure SelfDualityData {A : Type u} [CommRing A]
    [HasDerivedCategory.{w} (ModuleCat.{u} A)]
    (K : DPlus (ModuleCat.{u} A)) where
  map : DerivedObject (ModuleCat.of A A) ⟶
    RHom (R := A)
      ((DerivedCategory.Plus.ι (C := ModuleCat.{u} A)).obj K)
      ((DerivedCategory.Plus.ι (C := ModuleCat.{u} A)).obj K)
  isIso : IsIso map

/-! ## The definition from the source -/

/-- A dualizing complex over a Noetherian ring.

The object lies in `D⁺(A)`, has finite cohomology modules, has finite
injective dimension after inclusion into `D(A)`, and has the self-duality
map `A ⟶ RHom_A(K, K)` as an isomorphism in `D(A)`. -/
def IsDualizingComplex {A : Type u} [CommRing A] [IsNoetherianRing A]
    [HasDerivedCategory.{w} (ModuleCat.{u} A)]
    (K : DPlus (ModuleCat.{u} A)) : Prop :=
  HasFiniteCohomologyModules (R := A) K ∧
    HasFiniteInjectiveDimension (R := A)
      (K := (DerivedCategory.Plus.ι (C := ModuleCat.{u} A)).obj K) ∧
    Nonempty (SelfDualityData K)

end

end Formalization.Books.Dualizing.Unit01
