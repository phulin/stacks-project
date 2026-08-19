import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.RingTheory.Localization.Away.Basic
import Formalization.Books.MoreAlgebra.Unit65.PseudoCoherentModules
import Formalization.Books.MoreAlgebra.Unit61
import Formalization.Books.MoreAlgebra.Unit81.RelativelyFinitelyPresented

/-!
# More on Algebra, Chapter 82: Relatively pseudo-coherent modules

This file formalizes the definitions and theorem interfaces in the source
section.  Relative pseudo-coherence is tested after restricting a complex to
one (equivalently, every) finite polynomial presentation of the target
algebra.  The derived-category versions quantify over representatives, while
the complex version is the source-facing definition.
-/

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Pretriangulated
open Formalization.Books.Derived.Unit08
open Formalization.Books.Derived.Unit11
open Formalization.Books.MoreAlgebra.Unit56
open Formalization.Books.MoreAlgebra.Unit59
open Formalization.Books.MoreAlgebra.Unit65
open Formalization.Books.MoreAlgebra.Unit81

universe u

namespace Formalization.Books.MoreAlgebra.Unit82

variable {R A B R' : Type u} [CommRing R] [CommRing A] [CommRing B]
  [CommRing R']

/-! Unit65 makes the derived-category argument explicit.  The standard
derived category of a module category supplies it uniformly for this chapter's
polynomial presentations as well. -/
noncomputable instance moduleCatHasDerivedCategory
    (S : Type u) [Ring S] : HasDerivedCategory (ModuleCat.{u} S) := by
  exact HasDerivedCategory.standard _

abbrev Mod (R : Type u) [CommRing R] := Unit65.Mod R

abbrev Comp (R : Type u) [CommRing R] := Unit65.Comp R

abbrev D (R : Type u) [CommRing R]
    [HasDerivedCategory (Mod R)] := Unit65.D R

/-! ## The two preliminary change-of-rings lemmas -/

theorem pull_push
    (R : Type u) [CommRing R] [HasDerivedCategory (Mod R)]
    (K : Comp R) :
    let e : Polynomial R →+* R := Polynomial.eval₂RingHom (RingHom.id R) 0
    Nonempty ((derivedPullback e).obj
        ((derivedComplexQuotient (Polynomial R)).obj
          (restrictScalarsComplex e K)) ≅
      (derivedComplexQuotient R).obj K ⊞
        (shiftFunctor (D R) (1 : ℤ)).obj ((derivedComplexQuotient R).obj K)) := by
  sorry

theorem add_variable_pseudoCoherent
    (R : Type u) [CommRing R] [HasDerivedCategory (Mod R)]
    (K : Comp R) (m : ℤ) :
    let e : Polynomial R →+* R := Polynomial.eval₂RingHom (RingHom.id R) 0
    IsMPseudoCoherent R m ((derivedComplexQuotient R).obj K) ↔
      IsMPseudoCoherent (Polynomial R) m
        ((derivedComplexQuotient (Polynomial R)).obj
          (restrictScalarsComplex e K)) := by
  sorry

/-! ## Relative pseudo-coherence and its definition -/

/-- Relative `m`-pseudo-coherence for a complex, using a polynomial
presentation of the target algebra. -/
def IsMPseudoCoherentRelative
    (f : R →+* A) (m : ℤ) (K : Comp A) : Prop :=
  letI : Algebra R A := f.toAlgebra
  RingHom.FiniteType f ∧
    ∃ (n : ℕ) (α : MvPolynomial (Fin n) R →ₐ[R] A),
      Function.Surjective α ∧
        IsMPseudoCoherent (MvPolynomial (Fin n) R) m
          ((derivedComplexQuotient (MvPolynomial (Fin n) R)).obj
            (restrictScalarsComplex α.toRingHom K))

/-- Relative pseudo-coherence for a complex. -/
def IsPseudoCoherentRelative
    (f : R →+* A) (K : Comp A) : Prop :=
  ∀ m : ℤ, IsMPseudoCoherentRelative f m K

/-- The source's representative-independent derived-object formulation. -/
def IsMPseudoCoherentRelativeObject
    (f : R →+* A) (m : ℤ) (K : D A) : Prop :=
  ∀ (C : Comp A),
    Nonempty ((derivedComplexQuotient A).obj C ≅ K) →
      IsMPseudoCoherentRelative f m C

def IsPseudoCoherentRelativeObject
    (f : R →+* A) (K : D A) : Prop :=
  ∀ m : ℤ, IsMPseudoCoherentRelativeObject f m K

def IsMPseudoCoherentRelativeModule
    (f : R →+* A) (m : ℤ) (M : Mod A) : Prop :=
  IsMPseudoCoherentRelativeObject f m (moduleInDerived A M)

def IsPseudoCoherentRelativeModule
    (f : R →+* A) (M : Mod A) : Prop :=
  IsPseudoCoherentRelativeObject f (moduleInDerived A M)

theorem relatively_pseudoCoherent_iff_all_presentations
    (f : R →+* A) (hf : RingHom.FiniteType f) (m : ℤ) (K : Comp A) :
    letI : Algebra R A := f.toAlgebra
    (IsMPseudoCoherentRelative f m K ↔
      ∀ (n : ℕ) (α : MvPolynomial (Fin n) R →ₐ[R] A),
        Function.Surjective α →
          IsMPseudoCoherent (MvPolynomial (Fin n) R) m
            ((derivedComplexQuotient (MvPolynomial (Fin n) R)).obj
              (restrictScalarsComplex α.toRingHom K))) ∧
    (IsPseudoCoherentRelative f K ↔
      ∀ (n : ℕ) (α : MvPolynomial (Fin n) R →ₐ[R] A),
        Function.Surjective α →
          IsPseudoCoherent (MvPolynomial (Fin n) R)
            ((derivedComplexQuotient (MvPolynomial (Fin n) R)).obj
              (restrictScalarsComplex α.toRingHom K))) := by
  sorry

/-! ## Stability under finite maps and triangles -/

theorem finite_extension_pseudoCoherent
    (f : R →+* A) (g : A →+* B)
    (hf : RingHom.FiniteType f)
    (hfg : RingHom.FiniteType (g.comp f))
    (hfinite : RingHom.Finite g) (K : Comp B) (m : ℤ) :
    (IsMPseudoCoherentRelative f m (restrictScalarsComplex g K) ↔
      IsMPseudoCoherentRelative (g.comp f) m K) ∧
    (IsPseudoCoherentRelative f (restrictScalarsComplex g K) ↔
      IsPseudoCoherentRelative (g.comp f) K) := by
  sorry

theorem cone_relatively_pseudoCoherent
    (f : R →+* A) (hf : RingHom.FiniteType f) (m : ℤ)
    (T : Triangle (D A)) (hT : T ∈ distTriang (D A)) :
    ((IsMPseudoCoherentRelativeObject f (m + 1) T.obj₁ ∧
        IsMPseudoCoherentRelativeObject f m T.obj₂) →
        IsMPseudoCoherentRelativeObject f m T.obj₃) ∧
      ((IsMPseudoCoherentRelativeObject f m T.obj₁ ∧
        IsMPseudoCoherentRelativeObject f m T.obj₃) →
        IsMPseudoCoherentRelativeObject f m T.obj₂) ∧
      ((IsMPseudoCoherentRelativeObject f (m + 1) T.obj₂ ∧
        IsMPseudoCoherentRelativeObject f m T.obj₃) →
        IsMPseudoCoherentRelativeObject f (m + 1) T.obj₁) ∧
      ((IsPseudoCoherentRelativeObject f T.obj₁ ∧
        IsPseudoCoherentRelativeObject f T.obj₂) →
        IsPseudoCoherentRelativeObject f T.obj₃) ∧
      ((IsPseudoCoherentRelativeObject f T.obj₁ ∧
        IsPseudoCoherentRelativeObject f T.obj₃) →
        IsPseudoCoherentRelativeObject f T.obj₂) ∧
      ((IsPseudoCoherentRelativeObject f T.obj₂ ∧
        IsPseudoCoherentRelativeObject f T.obj₃) →
        IsPseudoCoherentRelativeObject f T.obj₁) := by
  sorry

/-! ## Module formulations and complexes -/

def HasRelativeFiniteFreeResolution
    (f : R →+* A) (M : Mod A) (d : ℕ) : Prop :=
  letI : Algebra R A := f.toAlgebra
  ∀ (n : ℕ) (α : MvPolynomial (Fin n) R →ₐ[R] A),
    Function.Surjective α →
      HasFiniteFreeResolution (MvPolynomial (Fin n) R)
        ((ModuleCat.restrictScalars α.toRingHom).obj M) d

def HasRelativeInfiniteFreeResolution
    (f : R →+* A) (M : Mod A) : Prop :=
  letI : Algebra R A := f.toAlgebra
  ∀ (n : ℕ) (α : MvPolynomial (Fin n) R →ₐ[R] A),
    Function.Surjective α →
      HasInfiniteFreeResolution (MvPolynomial (Fin n) R)
        ((ModuleCat.restrictScalars α.toRingHom).obj M)

theorem rel_n_pseudoCoherent_module
    (f : R →+* A) (hf : RingHom.FiniteType f) (M : Mod A) :
    (IsMPseudoCoherentRelativeModule f 0 M ↔ FiniteType A M) ∧
      (IsMPseudoCoherentRelativeModule f (-1) M ↔
        RelativelyFinitelyPresented f (M : Type u)) ∧
      (∀ d : ℕ,
        IsMPseudoCoherentRelativeModule f (-(d : ℤ)) M ↔
          HasRelativeFiniteFreeResolution f M d) ∧
      (IsPseudoCoherentRelativeModule f M ↔
        HasRelativeInfiniteFreeResolution f M) := by
  sorry

theorem summands_relative_pseudoCoherent
    (f : R →+* A) (hf : RingHom.FiniteType f) (m : ℤ)
    (K L : D A) :
    IsMPseudoCoherentRelativeObject f m (K ⊞ L) →
      IsMPseudoCoherentRelativeObject f m K ∧
        IsMPseudoCoherentRelativeObject f m L := by
  sorry

theorem summands_relative_pseudoCoherent_of_pseudoCoherent
    (f : R →+* A) (hf : RingHom.FiniteType f) (K L : D A) :
    IsPseudoCoherentRelativeObject f (K ⊞ L) →
      IsPseudoCoherentRelativeObject f K ∧
        IsPseudoCoherentRelativeObject f L := by
  sorry

theorem complex_relative_pseudoCoherent_modules
    (f : R →+* A) (hf : RingHom.FiniteType f) (m : ℤ) (K : Comp A)
    (hK : IsBoundedAbove K)
    (hterms : ∀ i : ℤ,
      IsMPseudoCoherentRelativeModule f (m - i) (K.X i)) :
    IsMPseudoCoherentRelative f m K := by
  sorry

theorem boundedAbove_complex_relative_pseudoCoherent
    (f : R →+* A) (hf : RingHom.FiniteType f) (K : Comp A)
    (hK : IsBoundedAbove K)
    (hterms : ∀ i : ℤ,
      IsPseudoCoherentRelativeModule f (K.X i)) :
    IsPseudoCoherentRelative f K := by
  sorry

theorem cohomology_relative_pseudoCoherent
    (f : R →+* A) (hf : RingHom.FiniteType f) (m : ℤ) (K : D A)
    (hK : IsInDMinus A K)
    (hcoh : ∀ i : ℤ,
      IsMPseudoCoherentRelativeModule f (m - i)
        ((derivedCohomologyFunctor A i).obj K)) :
    IsMPseudoCoherentRelativeObject f m K := by
  sorry

theorem cohomology_relative_pseudoCoherent_of_pseudoCoherent
    (f : R →+* A) (hf : RingHom.FiniteType f) (K : D A)
    (hK : IsInDMinus A K)
    (hcoh : ∀ i : ℤ,
      IsPseudoCoherentRelativeModule f
        ((derivedCohomologyFunctor A i).obj K)) :
    IsPseudoCoherentRelativeObject f K := by
  sorry

/-! ## Localization, base change, and pullback -/

theorem localize_relative_pseudoCoherent
    (R A : Type u) [CommRing R] [CommRing A] (f : R)
    (h : Localization.Away f →+* A) (hh : RingHom.FiniteType h)
    (g : A) (K : Comp A) (m : ℤ) :
    (IsMPseudoCoherentRelative h m K →
      IsMPseudoCoherentRelative
        (((algebraMap A (Localization.Away g)).comp h).comp
          (algebraMap R (Localization.Away f))) m
        (baseChangeComplex (algebraMap A (Localization.Away g)) K)) ∧
    (IsPseudoCoherentRelative h K →
      IsPseudoCoherentRelative
        (((algebraMap A (Localization.Away g)).comp h).comp
          (algebraMap R (Localization.Away f)))
        (baseChangeComplex (algebraMap A (Localization.Away g)) K)) := by
  sorry

theorem base_change_relative_pseudoCoherent
    (f : R →+* A) (g : R →+* R') (hf : RingHom.FiniteType f)
    (hTor : Formalization.Books.MoreAlgebra.Unit61.TorIndependentVia f g)
    (K : Comp A) (m : ℤ) :
    (IsMPseudoCoherentRelative f m K →
      IsMPseudoCoherentRelative
        (Formalization.Books.Algebra.Unit14.baseChangeRingMap f g) m
        (baseChangeComplex
          (Formalization.Books.Algebra.Unit14.baseChangeAlgebraMap f g) K)) ∧
    (IsPseudoCoherentRelative f K →
      IsPseudoCoherentRelative
        (Formalization.Books.Algebra.Unit14.baseChangeRingMap f g)
        (baseChangeComplex
          (Formalization.Books.Algebra.Unit14.baseChangeAlgebraMap f g) K)) := by
  sorry

theorem pull_relative_pseudoCoherent
    (f : R →+* A) (g : A →+* B)
    (hf : RingHom.FiniteType f) (hfg : RingHom.FiniteType (g.comp f))
    (hg : RingHom.FiniteType g) (m : ℤ) (K : Comp A)
    (hB : IsPseudoCoherentRelativeModule g (ModuleCat.of B B)) :
    (IsMPseudoCoherentRelative f m K →
      IsMPseudoCoherentRelative (g.comp f) m (baseChangeComplex g K)) ∧
    (IsPseudoCoherentRelative f K →
      IsPseudoCoherentRelative (g.comp f) (baseChangeComplex g K)) := by
  sorry

theorem pull_relative_pseudoCoherent_module
    (f : R →+* A) (g : A →+* B)
    (hf : RingHom.FiniteType f) (hfg : RingHom.FiniteType (g.comp f))
    (hg : RingHom.FiniteType g) (m : ℤ) (M : Mod A)
    (hflat : RingHom.Flat g)
    (hB : IsPseudoCoherentRelativeModule g (ModuleCat.of B B)) :
    (IsMPseudoCoherentRelativeModule f m M →
      IsMPseudoCoherentRelativeModule (g.comp f) m
        ((pullModule g).obj M)) ∧
    (IsPseudoCoherentRelativeModule f M →
      IsPseudoCoherentRelativeModule (g.comp f) ((pullModule g).obj M)) := by
  sorry

theorem composition_relative_pseudoCoherent
    (f : R →+* A) (g : A →+* B)
    (hf : RingHom.FiniteType f) (hfg : RingHom.FiniteType (g.comp f))
    (hg : RingHom.FiniteType g) (m : ℤ) (K : Comp B)
    (hA : IsPseudoCoherentRelativeModule f (ModuleCat.of A A)) :
    (IsMPseudoCoherentRelative g m K ↔
      IsMPseudoCoherentRelative (g.comp f) m K) ∧
    (IsPseudoCoherentRelative g K ↔
      IsPseudoCoherentRelative (g.comp f) K) := by
  sorry

theorem glue_relative_pseudoCoherent
    (f : R →+* A) (hf : RingHom.FiniteType f) (m : ℤ) (K : Comp A)
    (r : ℕ) (fs : Fin r → A)
    (hunit : Ideal.span (Set.range fs) = ⊤) :
    (IsMPseudoCoherentRelative f m K ↔
      ∀ i : Fin r,
        IsMPseudoCoherentRelative
          ((algebraMap A (Localization.Away (fs i))).comp f) m
          (localizedComplex (fs i) K)) ∧
    (IsPseudoCoherentRelative f K ↔
      ∀ i : Fin r,
        IsPseudoCoherentRelative
          ((algebraMap A (Localization.Away (fs i))).comp f)
          (localizedComplex (fs i) K)) := by
  sorry

/-! ## The Noetherian criterion -/

theorem noetherian_relative_pseudoCoherent
    (f : R →+* A) (hf : RingHom.FiniteType f)
    [IsNoetherianRing R] (m : ℤ) (K : Comp A) :
    (IsMPseudoCoherentRelative f m K ↔
      IsInDMinus A ((derivedComplexQuotient A).obj K) ∧
        ∀ i : ℤ, m ≤ i →
          FiniteType A ((derivedCohomologyFunctor A i).obj
            ((derivedComplexQuotient A).obj K))) ∧
    (IsPseudoCoherentRelative f K ↔
      IsInDMinus A ((derivedComplexQuotient A).obj K) ∧
        ∀ i : ℤ,
          FiniteType A ((derivedCohomologyFunctor A i).obj
            ((derivedComplexQuotient A).obj K))) ∧
    (∀ M : Mod A,
      IsPseudoCoherentRelativeModule f M ↔ FiniteType A M) := by
  sorry

end Formalization.Books.MoreAlgebra.Unit82
