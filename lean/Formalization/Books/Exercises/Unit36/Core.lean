import Mathlib.AlgebraicGeometry.Modules.Tilde
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.Restrict
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Morphisms.Immersion
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact

/-!
# Exercises, Chapter 36: Quasi-coherent Sheaves

The chapter uses Mathlib's canonical category `X.Modules` of sheaves of
`𝒪_X`-modules.  Quasi-coherence and finite type are recorded by Mathlib's
`SheafOfModules.IsQuasicoherent` and `SheafOfModules.IsFiniteType` classes;
the definitions below only package those APIs in the source-facing forms
needed by the exercises.
-/

namespace Formalization.Books.Exercises.Unit36

open CategoryTheory
open AlgebraicGeometry
open TopologicalSpace
open scoped AlgebraicGeometry

universe u

noncomputable section

/-! ## Affine schemes and canonical quasi-coherent modules -/

/-- The affine scheme `Spec(R)`. -/
abbrev affineSpec (R : Type u) [CommRing R] : Scheme.{u} :=
  Scheme.Spec.obj (Opposite.op (CommRingCat.of R))

/-- The full subcategory of quasi-coherent `𝒪_X`-modules. -/
abbrev QuasiCoherentModules (X : Scheme.{u}) :=
  (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory

/-- The scheme underlying the basic open `D(f) ⊆ Spec(R)`. -/
abbrev basicOpenScheme (R : Type u) [CommRing R] (f : R) : Scheme.{u} :=
  Scheme.Opens.toScheme (X := affineSpec R) (PrimeSpectrum.basicOpen f)

/-- The canonical open immersion `D(f) → Spec(R)`. -/
def basicOpenInclusion (R : Type u) [CommRing R] (f : R) :
    basicOpenScheme R f ⟶ affineSpec R :=
  Scheme.Opens.ι (X := affineSpec R) (PrimeSpectrum.basicOpen f)

/-- The source's specialization relation, with the stated orientation. -/
def IsSpecialization {X : Type u} [TopologicalSpace X] (x x' : X) : Prop :=
  x ∈ closure ({x'} : Set X)

/-- A sheaf on `Y` is the restriction of a sheaf on `X` along `i : Y → X`.

The source writes equality of sheaves; an isomorphism is the invariant
category-theoretic formulation and is what Mathlib's pullback API exposes.
-/
def IsRestrictionOf {X Y : Scheme.{u}} (i : Y ⟶ X)
    (G : Y.Modules) (F : X.Modules) : Prop :=
  Nonempty ((Scheme.Modules.pullback i).obj F ≅ G)

/-! ## Locally Noetherian schemes and coherent modules -/

/-- The source's coherent-sheaf condition, using Mathlib's canonical local
quasi-coherence and finite-type predicates. -/
def IsCoherent {X : Scheme.{u}} (M : X.Modules) : Prop :=
  M.IsQuasicoherent ∧ M.IsFiniteType

/-! ## The affine closed subscheme used in the second extension exercise -/

/-- The affine closed subscheme of `Spec(R)` defined by `I`. -/
abbrev quotientClosedSubscheme (R : Type u) [CommRing R] (I : Ideal R) : Scheme.{u} :=
  affineSpec (R ⧸ I)

/-- The canonical closed immersion of the quotient subscheme. -/
def quotientClosedImmersion (R : Type u) [CommRing R] (I : Ideal R) :
    quotientClosedSubscheme R I ⟶ affineSpec R :=
  AlgebraicGeometry.Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))

end

end Formalization.Books.Exercises.Unit36
