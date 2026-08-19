import Formalization.Books.MoreAlgebra.Unit59.DerivedTensorProduct
import Formalization.Books.MoreAlgebra.Unit63.ProductsAndTor
import Formalization.Books.Algebra.Unit90.CoherentRings
import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.RingTheory.RingHom.FaithfullyFlat

/-!
# More on Algebra, Chapter 65: Pseudo-coherent modules, I

This file records the finite-free approximation predicates and the
stability, base-change, descent, tensor-product, Noetherian, and coherent
criteria from the section.  The categorical objects are Mathlib's module
complexes and derived categories; the propositions below are the chapter's
interfaces for the source terminology.
-/

noncomputable section

open CategoryTheory
open CategoryTheory.Pretriangulated
open CategoryTheory.Limits
open Formalization.Books.Derived.Unit08
open Formalization.Books.Derived.Unit11
open Formalization.Books.MoreAlgebra.Unit56
open Formalization.Books.MoreAlgebra.Unit59
open Formalization.Books.MoreAlgebra.Unit63
open Formalization.Books.Algebra.Unit90

universe w u

namespace Formalization.Books.MoreAlgebra.Unit65

/-! ## Canonical objects and finite-free complexes -/

abbrev Mod (R : Type u) [CommRing R] := ModuleCat.{u} R

abbrev Comp (R : Type u) [CommRing R] := Unit59.Comp R

abbrev D (R : Type u) [CommRing R]
    [HasDerivedCategory.{w} (Mod R)] := Unit59.D R

noncomputable abbrev derivedCohomologyFunctor
    (R : Type u) [CommRing R]
    [HasDerivedCategory.{w} (Mod R)] (i : ℤ) : D R ⥤ Mod R :=
  DerivedCategory.homologyFunctor (Mod R) i

noncomputable abbrev cochainCohomologyFunctor
    (R : Type u) [CommRing R] (i : ℤ) : Comp R ⥤ Mod R :=
  HomologicalComplex.homologyFunctor (Mod R) (.up ℤ) i

noncomputable def moduleInDerived
    (R : Type u) [CommRing R]
    [HasDerivedCategory.{w} (Mod R)] (M : Mod R) : D R :=
  (derivedComplexQuotient R).obj
    ((CochainComplex.singleFunctor (Mod R) 0).obj M)

abbrev FiniteType (R : Type u) [CommRing R] (M : Mod R) : Prop :=
  Module.Finite R (M : Type u)

abbrev FinitelyPresented (R : Type u) [CommRing R] (M : Mod R) : Prop :=
  Module.FinitePresentation R (M : Type u)

def FiniteFreeModule (R : Type u) [CommRing R] (M : Mod R) : Prop :=
  Module.Free R (M : Type u) ∧ Module.Finite R (M : Type u)

def FiniteProjectiveModule (R : Type u) [CommRing R] (M : Mod R) : Prop :=
  Module.Projective R (M : Type u) ∧ Module.Finite R (M : Type u)

def FiniteFreeComplex (R : Type u) [CommRing R] (E : Comp R) : Prop :=
  IsBounded E ∧ ∀ i : ℤ, FiniteFreeModule R (E.X i)

def BoundedAboveFiniteFreeComplex
    (R : Type u) [CommRing R] (E : Comp R) : Prop :=
  IsBoundedAbove E ∧ ∀ i : ℤ, FiniteFreeModule R (E.X i)

def BoundedAboveFiniteProjectiveComplex
    (R : Type u) [CommRing R] (E : Comp R) : Prop :=
  IsBoundedAbove E ∧ ∀ i : ℤ, FiniteProjectiveModule R (E.X i)

def IsInDMinus
    (R : Type u) [CommRing R]
    [HasDerivedCategory.{w} (Mod R)] (K : D R) : Prop :=
  ∃ E : Comp R, IsBoundedAbove E ∧
    Nonempty ((derivedComplexQuotient R).obj E ≅ K)

/-! The displayed finite-free resolution is represented by a finite complex
quasi-isomorphic to the stalk module, with the indicated degree support. -/
def HasFiniteFreeResolution
    (R : Type u) [CommRing R]
    [HasDerivedCategory.{w} (Mod R)] (M : Mod R) (d : ℕ) : Prop :=
  ∃ E : Comp R,
    (∀ i : ℤ, i < -(d : ℤ) ∨ 0 < i → IsZero (E.X i)) ∧
    (∀ i : ℤ, -(d : ℤ) ≤ i → i ≤ 0 → FiniteFreeModule R (E.X i)) ∧
    Nonempty ((derivedComplexQuotient R).obj E ≅ moduleInDerived R M)

def HasInfiniteFreeResolution
    (R : Type u) [CommRing R]
    [HasDerivedCategory.{w} (Mod R)] (M : Mod R) : Prop :=
  ∃ E : Comp R,
    IsBoundedAbove E ∧
    (∀ i : ℤ, FiniteFreeModule R (E.X i)) ∧
    (∀ i : ℤ, 0 < i → IsZero (E.X i)) ∧
    Nonempty ((derivedComplexQuotient R).obj E ≅ moduleInDerived R M)

/-! ## Pseudo-coherence -/

def IsMPseudoCoherent
    (R : Type u) [CommRing R]
    [HasDerivedCategory.{w} (Mod R)] (m : ℤ) (K : D R) : Prop :=
  ∃ E : Comp R, FiniteFreeComplex R E ∧
    ∃ α : (derivedComplexQuotient R).obj E ⟶ K,
      (∀ i : ℤ, m < i → IsIso ((derivedCohomologyFunctor R i).map α)) ∧
      Epi ((derivedCohomologyFunctor R m).map α)

def IsPseudoCoherent
    (R : Type u) [CommRing R]
    [HasDerivedCategory.{w} (Mod R)] (K : D R) : Prop :=
  ∃ E : Comp R, BoundedAboveFiniteFreeComplex R E ∧
    Nonempty ((derivedComplexQuotient R).obj E ≅ K)

def IsMPseudoCoherentModule
    (R : Type u) [CommRing R]
    [HasDerivedCategory.{w} (Mod R)] (m : ℤ) (M : Mod R) : Prop :=
  IsMPseudoCoherent R m (moduleInDerived R M)

def IsPseudoCoherentModule
    (R : Type u) [CommRing R]
    [HasDerivedCategory.{w} (Mod R)] (M : Mod R) : Prop :=
  IsPseudoCoherent R (moduleInDerived R M)

def IsMPseudoCoherentComplex
    (R : Type u) [CommRing R]
    [HasDerivedCategory.{w} (Mod R)] (m : ℤ) (K : Comp R) : Prop :=
  IsMPseudoCoherent R m ((derivedComplexQuotient R).obj K)

def IsPseudoCoherentComplex
    (R : Type u) [CommRing R]
    [HasDerivedCategory.{w} (Mod R)] (K : Comp R) : Prop :=
  IsPseudoCoherent R ((derivedComplexQuotient R).obj K)

/-! ## Triangles and permanence -/

def IsDistinguishedTriangle
    (R : Type u) [CommRing R]
    [HasDerivedCategory.{w} (Mod R)] (T : Triangle (D R)) : Prop :=
  T ∈ distTriang (D R)

theorem cone_pseudoCoherent
    (R : Type u) [CommRing R]
    [HasDerivedCategory.{w} (Mod R)] (m : ℤ)
    (T : Triangle (D R)) (hT : IsDistinguishedTriangle R T) :
    ((IsMPseudoCoherent R (m + 1) T.obj₁ ∧ IsMPseudoCoherent R m T.obj₂) →
        IsMPseudoCoherent R m T.obj₃) ∧
      ((IsMPseudoCoherent R m T.obj₁ ∧ IsMPseudoCoherent R m T.obj₃) →
        IsMPseudoCoherent R m T.obj₂) ∧
      ((IsMPseudoCoherent R (m + 1) T.obj₂ ∧ IsMPseudoCoherent R m T.obj₃) →
        IsMPseudoCoherent R (m + 1) T.obj₁) := by
  sorry

theorem finite_cohomology_pseudoCoherent
    (R : Type u) [CommRing R]
    [HasDerivedCategory.{w} (Mod R)] (m : ℤ) (K : D R)
    (hK : IsMPseudoCoherent R m K) :
    ((∀ i : ℤ, m < i → IsZero ((derivedCohomologyFunctor R i).obj K)) →
        FiniteType R ((derivedCohomologyFunctor R m).obj K)) ∧
      ((∀ i : ℤ, m + 1 < i →
          IsZero ((derivedCohomologyFunctor R i).obj K)) →
        FinitelyPresented R ((derivedCohomologyFunctor R (m + 1)).obj K)) := by
  sorry

theorem n_pseudoCoherent_module
    (R : Type u) [CommRing R]
    [HasDerivedCategory.{w} (Mod R)] (M : Mod R) :
    (IsMPseudoCoherentModule R 0 M ↔ FiniteType R M) ∧
      (IsMPseudoCoherentModule R (-1) M ↔ FinitelyPresented R M) ∧
      (∀ d : ℕ,
        IsMPseudoCoherentModule R (-(d : ℤ)) M ↔
          HasFiniteFreeResolution R M d) ∧
      (IsPseudoCoherentModule R M ↔ HasInfiniteFreeResolution R M) := by
  sorry

theorem pseudoCoherent_iff
    (R : Type u) [CommRing R]
    [HasDerivedCategory.{w} (Mod R)] (K : D R) :
    (IsPseudoCoherent R K ↔
      ∀ m : ℤ, IsMPseudoCoherent R m K) ∧
      (IsPseudoCoherent R K ↔
        ∃ E : Comp R, BoundedAboveFiniteProjectiveComplex R E ∧
          Nonempty ((derivedComplexQuotient R).obj E ≅ K)) ∧
      (∀ b : ℤ,
        (∀ i : ℤ, b < i → IsZero ((derivedCohomologyFunctor R i).obj K)) →
        ∃ F : Comp R,
          (∀ i : ℤ, FiniteFreeModule R (F.X i)) ∧
          (∀ i : ℤ, b < i → IsZero (F.X i)) ∧
          Nonempty ((derivedComplexQuotient R).obj F ≅ K)) := by
  sorry

theorem two_out_of_three_pseudoCoherent
    (R : Type u) [CommRing R]
    [HasDerivedCategory.{w} (Mod R)]
    (T : Triangle (D R)) (hT : IsDistinguishedTriangle R T) :
    ((IsPseudoCoherent R T.obj₁ ∧ IsPseudoCoherent R T.obj₂) →
        IsPseudoCoherent R T.obj₃) ∧
      ((IsPseudoCoherent R T.obj₁ ∧ IsPseudoCoherent R T.obj₃) →
        IsPseudoCoherent R T.obj₂) ∧
      ((IsPseudoCoherent R T.obj₂ ∧ IsPseudoCoherent R T.obj₃) →
        IsPseudoCoherent R T.obj₁) := by
  sorry

theorem recognize_pseudoCoherent
    (R : Type u) [CommRing R]
    [HasDerivedCategory.{w} (Mod R)] (m : ℤ) (K : D R) :
    ((∀ i : ℤ, m ≤ i → IsZero ((derivedCohomologyFunctor R i).obj K)) →
        IsMPseudoCoherent R m K) ∧
      ((∀ i : ℤ, m < i → IsZero ((derivedCohomologyFunctor R i).obj K)) →
        (FiniteType R ((derivedCohomologyFunctor R m).obj K) →
          IsMPseudoCoherent R m K)) ∧
      ((∀ i : ℤ, m + 1 < i →
          IsZero ((derivedCohomologyFunctor R i).obj K)) →
        (FinitelyPresented R ((derivedCohomologyFunctor R (m + 1)).obj K) →
          FiniteType R ((derivedCohomologyFunctor R m).obj K) →
          IsMPseudoCoherent R m K)) := by
  sorry

theorem summands_pseudoCoherent
    (R : Type u) [CommRing R]
    [HasDerivedCategory.{w} (Mod R)] (m : ℤ) (K L : D R) :
    IsMPseudoCoherent R m (K ⊞ L) →
      IsMPseudoCoherent R m K ∧ IsMPseudoCoherent R m L := by
  sorry

theorem summands_pseudoCoherent_of_pseudoCoherent
    (R : Type u) [CommRing R]
    [HasDerivedCategory.{w} (Mod R)] (K L : D R) :
    IsPseudoCoherent R (K ⊞ L) →
      IsPseudoCoherent R K ∧ IsPseudoCoherent R L := by
  sorry

theorem complex_pseudoCoherent_modules
    (R : Type u) [CommRing R]
    [HasDerivedCategory.{w} (Mod R)] (m : ℤ) (K : Comp R)
    (hK : IsBoundedAbove K)
    (hterms : ∀ i : ℤ, IsMPseudoCoherentModule R (m - i) (K.X i)) :
    IsMPseudoCoherent R m ((derivedComplexQuotient R).obj K) := by
  sorry

theorem boundedAbove_complex_pseudoCoherent
    (R : Type u) [CommRing R]
    [HasDerivedCategory.{w} (Mod R)] (K : Comp R)
    (hK : IsBoundedAbove K)
    (hterms : ∀ i : ℤ, IsPseudoCoherentModule R (K.X i)) :
    IsPseudoCoherent R ((derivedComplexQuotient R).obj K) := by
  sorry

theorem cohomology_pseudoCoherent
    (R : Type u) [CommRing R]
    [HasDerivedCategory.{w} (Mod R)] (m : ℤ) (K : D R)
    (hK : IsInDMinus R K)
    (hcoh : ∀ i : ℤ,
      IsMPseudoCoherentModule R (m - i)
        ((derivedCohomologyFunctor R i).obj K)) :
    IsMPseudoCoherent R m K := by
  sorry

theorem cohomology_pseudoCoherent_of_pseudoCoherent
    (R : Type u) [CommRing R]
    [HasDerivedCategory.{w} (Mod R)] (K : D R)
    (hK : IsInDMinus R K)
    (hcoh : ∀ i : ℤ,
      IsPseudoCoherentModule R ((derivedCohomologyFunctor R i).obj K)) :
    IsPseudoCoherent R K := by
  sorry

/-! ## Restriction and extension of scalars -/

noncomputable def ringMapModule
    {A B : Type u} [CommRing A] [CommRing B] (f : A →+* B) : Mod A :=
  letI : Algebra A B := f.toAlgebra
  ModuleCat.of A B

noncomputable abbrev derivedPullback
    {A B : Type u} [CommRing A] [CommRing B]
    [HasDerivedCategory.{w} (Mod A)]
    [HasDerivedCategory.{w} (Mod B)] (f : A →+* B) : D A ⥤ D B :=
  Unit63.derivedBaseChange f

theorem finite_push_pseudoCoherent
    {A B : Type u} [CommRing A] [CommRing B]
    [HasDerivedCategory.{w} (Mod A)]
    [HasDerivedCategory.{w} (Mod B)] (f : A →+* B)
    (hB : IsPseudoCoherentModule A (ringMapModule f))
    (K : Comp B) (m : ℤ) :
    (IsMPseudoCoherent B m ((derivedComplexQuotient B).obj K) ↔
      IsMPseudoCoherent A m
        ((derivedComplexQuotient A).obj (restrictScalarsComplex f K))) ∧
      (IsPseudoCoherent B ((derivedComplexQuotient B).obj K) ↔
        IsPseudoCoherent A
          ((derivedComplexQuotient A).obj (restrictScalarsComplex f K))) := by
  sorry

theorem pull_pseudoCoherent
    {A B : Type u} [CommRing A] [CommRing B]
    [HasDerivedCategory.{w} (Mod A)]
    [HasDerivedCategory.{w} (Mod B)] (f : A →+* B)
    (K : Comp A) (m : ℤ)
    (hK : IsMPseudoCoherent A m ((derivedComplexQuotient A).obj K)) :
    IsMPseudoCoherent B m
        ((derivedPullback f).obj ((derivedComplexQuotient A).obj K)) := by
  sorry

theorem pull_pseudoCoherent_of_pseudoCoherent
    {A B : Type u} [CommRing A] [CommRing B]
    [HasDerivedCategory.{w} (Mod A)]
    [HasDerivedCategory.{w} (Mod B)] (f : A →+* B) (K : Comp A)
    (hK : IsPseudoCoherent A ((derivedComplexQuotient A).obj K)) :
    IsPseudoCoherent B
      ((derivedPullback f).obj ((derivedComplexQuotient A).obj K)) := by
  sorry

noncomputable abbrev pullModule
    {A B : Type u} [CommRing A] [CommRing B] (f : A →+* B) :
    Mod A ⥤ Mod B :=
  ModuleCat.extendScalars f

theorem flat_base_change_pseudoCoherent
    {A B : Type u} [CommRing A] [CommRing B] (f : A →+* B)
    [HasDerivedCategory.{w} (Mod A)]
    [HasDerivedCategory.{w} (Mod B)]
    (hf : f.Flat) (M : Mod A) (m : ℤ)
    (hM : IsMPseudoCoherentModule A m M) :
    IsMPseudoCoherentModule B m ((pullModule f).obj M) := by
  sorry

/-! ## Localization and faithfully flat descent -/

noncomputable abbrev localizedComplex
    {R : Type u} [CommRing R] (f : R) (K : Comp R) :
    Comp (Localization.Away f) :=
  baseChangeComplex (algebraMap R (Localization.Away f)) K

theorem glue_pseudoCoherent
    (R : Type u) [CommRing R] (r : ℕ) (f : Fin r → R)
    (hunit : Ideal.span (Set.range f) = ⊤)
    [HasDerivedCategory.{w} (Mod R)]
    (hD : ∀ i : Fin r, HasDerivedCategory.{w} (Mod (Localization.Away (f i))))
    (m : ℤ) (K : Comp R) :
    ((∀ i : Fin r,
        @IsMPseudoCoherent (Localization.Away (f i)) _ (hD i) m
          ((derivedComplexQuotient (Localization.Away (f i))).obj
            (localizedComplex (f i) K))) →
      IsMPseudoCoherent R m ((derivedComplexQuotient R).obj K)) ∧
    ((∀ i : Fin r,
        @IsPseudoCoherent (Localization.Away (f i)) _ (hD i)
          ((derivedComplexQuotient (Localization.Away (f i))).obj
            (localizedComplex (f i) K))) →
      IsPseudoCoherent R ((derivedComplexQuotient R).obj K)) := by
  sorry

theorem flat_descent_pseudoCoherent
    {R R' : Type u} [CommRing R] [CommRing R'] (f : R →+* R')
    [HasDerivedCategory.{w} (Mod R)]
    [HasDerivedCategory.{w} (Mod R')]
    (hf : f.FaithfullyFlat) (m : ℤ) (K : Comp R) :
    (IsMPseudoCoherent R' m
        ((derivedComplexQuotient R').obj (baseChangeComplex f K)) →
      IsMPseudoCoherent R m ((derivedComplexQuotient R).obj K)) ∧
      (IsPseudoCoherent R'
          ((derivedComplexQuotient R').obj (baseChangeComplex f K)) →
        IsPseudoCoherent R ((derivedComplexQuotient R).obj K)) := by
  sorry

/-! ## Derived tensor products -/

theorem tensor_pseudoCoherent
    (R : Type u) [CommRing R]
    [HasDerivedCategory.{w} (Mod R)] (K L : D R)
    (n m a b : ℤ)
    (hK : IsMPseudoCoherent R n K)
    (hKa : ∀ i : ℤ, a < i →
      IsZero ((derivedCohomologyFunctor R i).obj K))
    (hL : IsMPseudoCoherent R m L)
    (hLb : ∀ j : ℤ, b < j →
      IsZero ((derivedCohomologyFunctor R j).obj L)) :
    IsMPseudoCoherent R (max (m + a) (n + b)) (derivedTensor K L) := by
  sorry

theorem tensor_pseudoCoherent_of_pseudoCoherent
    (R : Type u) [CommRing R]
    [HasDerivedCategory.{w} (Mod R)] (K L : D R)
    (hK : IsPseudoCoherent R K) (hL : IsPseudoCoherent R L) :
    IsPseudoCoherent R (derivedTensor K L) := by
  sorry

/-! ## Noetherian and coherent criteria -/

theorem noetherian_pseudoCoherent
    (R : Type u) [CommRing R] [IsNoetherianRing R]
    [HasDerivedCategory.{w} (Mod R)] (m : ℤ) (K : D R) :
    (IsMPseudoCoherent R m K ↔
      IsInDMinus R K ∧
        ∀ i : ℤ, m ≤ i →
          FiniteType R ((derivedCohomologyFunctor R i).obj K)) ∧
      (IsPseudoCoherent R K ↔
        IsInDMinus R K ∧
          ∀ i : ℤ, FiniteType R ((derivedCohomologyFunctor R i).obj K)) ∧
      (∀ M : Mod R, IsPseudoCoherentModule R M ↔ FiniteType R M) := by
  sorry

theorem coherent_pseudoCoherent
    (R : Type u) [CommRing R] (hR : IsCoherentRing R)
    [HasDerivedCategory.{w} (Mod R)] (m : ℤ) (K : D R) :
    (IsMPseudoCoherent R m K ↔
      IsInDMinus R K ∧
        (FiniteType R ((derivedCohomologyFunctor R m).obj K) ∧
          ∀ i : ℤ, m < i →
            IsCoherentModule R ((derivedCohomologyFunctor R i).obj K))) ∧
      (IsMPseudoCoherent R m K ↔
        IsInDMinus R K ∧
          (FiniteType R ((derivedCohomologyFunctor R m).obj K) ∧
            ∀ i : ℤ, m < i →
              FinitelyPresented R ((derivedCohomologyFunctor R i).obj K))) ∧
      (IsPseudoCoherent R K ↔
        IsInDMinus R K ∧
          ∀ i : ℤ, IsCoherentModule R ((derivedCohomologyFunctor R i).obj K)) := by
  sorry

end Formalization.Books.MoreAlgebra.Unit65
