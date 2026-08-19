import Formalization.Books.MoreAlgebra.Unit75.PerfectComplexes
import Formalization.Books.MoreAlgebra.Unit03.StablyFree
import Formalization.Books.MoreAlgebra.Unit13
import Mathlib.RingTheory.LocalRing.ResidueField.Ideal

/-!
# More on Algebra, Chapter 75: lifting complexes

The lifting statements are expressed with a class of module-category objects.
Reduction modulo an ideal is scalar extension along the canonical quotient map,
so the displayed source complexes remain ordinary Mathlib cochain complexes.
-/

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open Formalization.Books.Derived.Unit08
open Formalization.Books.Derived.Unit11
open Formalization.Books.MoreAlgebra.Unit03
open Formalization.Books.MoreAlgebra.Unit13
open Formalization.Books.MoreAlgebra.Unit59
open Formalization.Books.MoreAlgebra.Unit65
open Formalization.Books.MoreAlgebra.Unit75

universe w u

namespace Formalization.Books.MoreAlgebra.Unit75

/-! ## Classes of modules and reduction modulo an ideal -/

def SurjectiveModuloIdeal {R : Type u} [CommRing R] {M N : Mod R}
    (I : Ideal R) (f : M ⟶ N) : Prop :=
  ∀ y : (N : Type u), ∃ x : (M : Type u),
    f.hom x - y ∈ I • (⊤ : Submodule R (N : Type u))

def LiftingClass {R : Type u} [CommRing R] (I : Ideal R)
    (PClass : Set (Mod R)) : Prop :=
  (∀ P : Mod R, P ∈ PClass → Module.Projective R (P : Type u)) ∧
    (∀ P₁ P₂ : Mod R, P₁ ∈ PClass → (P₁ ⊞ P₂) ∈ PClass → P₂ ∈ PClass) ∧
    (∀ P₁ P₂ : Mod R, P₁ ∈ PClass → P₂ ∈ PClass →
      ∀ f : P₁ ⟶ P₂, SurjectiveModuloIdeal I f → Function.Surjective f.hom)

def IsFiniteStablyFreeModule (R : Type u) [CommRing R] (M : Mod R) : Prop :=
  FiniteType R M ∧ StablyFree R (M : Type u)

def IsHenselianPairIdeal {R : Type u} [CommRing R] (I : Ideal R) : Prop :=
  HenselianPair R I

def ReducedComplexTermsIn {R S : Type u} [CommRing R] [CommRing S]
    (PClass : Set (Mod R)) (f : R →+* S) (E : Comp S) : Prop :=
  ∀ i : ℤ, ∃ P : Mod R, P ∈ PClass ∧
    Nonempty ((ModuleCat.extendScalars f).obj P ≅ E.X i)

def BoundedAboveComplexIn {R : Type u} [CommRing R]
    [HasDerivedCategory.{w} (Mod R)] (PClass : Set (Mod R)) (K : D R) : Prop :=
  ∃ E : Comp R,
    IsBoundedAbove E ∧
      (∀ i : ℤ, ∃ P : Mod R, P ∈ PClass ∧ Nonempty (P ≅ E.X i)) ∧
      Nonempty ((derivedQuotient R).obj E ≅ K)

theorem lift_acyclic_complex
    (R : Type u) [CommRing R] (I : Ideal R)
    [HasDerivedCategory.{w} (Mod R)]
    (PClass : Set (Mod R)) (hPClass : LiftingClass I PClass)
    (E : Comp (R ⧸ I)) (hE : IsBoundedAbove E ∧ IsAcyclic E)
    (hterms : ReducedComplexTermsIn PClass (Ideal.Quotient.mk I) E) :
    ∃ P : Comp R,
      IsBoundedAbove P ∧ IsAcyclic P ∧
        (∀ i : ℤ, ∃ Q : Mod R, Q ∈ PClass ∧ Nonempty (Q ≅ P.X i)) ∧
        Nonempty (baseChangeComplex (Ideal.Quotient.mk I) P ≅ E) := by
  sorry

theorem lift_complex
    (R : Type u) [CommRing R] (I : Ideal R)
    [HasDerivedCategory.{w} (Mod R)]
    [HasDerivedCategory.{w} (Mod (R ⧸ I))]
    (PClass : Set (Mod R)) (hPClass : LiftingClass I PClass)
    (K : D R) (E : Comp (R ⧸ I))
    (hE : IsBoundedAbove E ∧ ReducedComplexTermsIn PClass
      (Ideal.Quotient.mk I) E)
    (hK : BoundedAboveComplexIn PClass K)
    (hrep : Nonempty ((derivedBaseChange (Ideal.Quotient.mk I)).obj K ≅
      (derivedQuotient (R ⧸ I)).obj E)) :
    ∃ P : Comp R,
      IsBoundedAbove P ∧
        (∀ i : ℤ, ∃ Q : Mod R, Q ∈ PClass ∧ Nonempty (Q ≅ P.X i)) ∧
        Nonempty (baseChangeComplex (Ideal.Quotient.mk I) P ≅ E) ∧
        Nonempty ((derivedQuotient R).obj P ≅ K) := by
  sorry

theorem lift_complex_projectives
    (R : Type u) [CommRing R] (I : Ideal R)
    [HasDerivedCategory.{w} (Mod R)]
    [HasDerivedCategory.{w} (Mod (R ⧸ I))]
    (K : D R) (E : Comp (R ⧸ I))
    (hE : IsBoundedAbove E ∧ ∀ i : ℤ, Module.Projective (R ⧸ I)
      ((E.X i : Type u)))
    (hrep : Nonempty ((derivedBaseChange (Ideal.Quotient.mk I)).obj K ≅
      (derivedQuotient (R ⧸ I)).obj E))
    (hI : ∃ n : ℕ, I ^ n = ⊥) :
    ∃ P : Comp R, IsBoundedAbove P ∧
      (∀ i : ℤ, Module.Projective R (P.X i : Type u)) ∧
      Nonempty ((derivedQuotient R).obj P ≅ K) ∧
      Nonempty (baseChangeComplex (Ideal.Quotient.mk I) P ≅ E) := by
  sorry

theorem pseudoCoherent_modulo_nilpotent_iff
    {R' R : Type u} [CommRing R'] [CommRing R]
    [HasDerivedCategory.{w} (Mod R')] [HasDerivedCategory.{w} (Mod R)]
    (f : R' →+* R) (hsurj : Function.Surjective f)
    (hker : Unit67.NilpotentKernel f) (K' : D R') :
    IsPseudoCoherent R' K' ↔
      IsPseudoCoherent R ((derivedBaseChange f).obj K') := by
  sorry

theorem lift_complex_finite_stably_free
    (R : Type u) [CommRing R] (I : Ideal R)
    [HasDerivedCategory.{w} (Mod R)]
    [HasDerivedCategory.{w} (Mod (R ⧸ I))]
    (K : D R) (E : Comp (R ⧸ I))
    (hE : IsBoundedAbove E ∧ ∀ i : ℤ,
      IsFiniteStablyFreeModule (R ⧸ I) (E.X i))
    (hrep : Nonempty ((derivedBaseChange (Ideal.Quotient.mk I)).obj K ≅
      (derivedQuotient (R ⧸ I)).obj E))
    (hunit : ∀ x : R, x ∈ 1 + I → IsUnit x)
    (hK : IsPseudoCoherent R K) :
    ∃ P : Comp R, IsBoundedAbove P ∧
      (∀ i : ℤ, IsFiniteStablyFreeModule R (P.X i)) ∧
      Nonempty ((derivedQuotient R).obj P ≅ K) ∧
      Nonempty (baseChangeComplex (Ideal.Quotient.mk I) P ≅ E) := by
  sorry

def FiniteFreeRanked (R : Type u) [CommRing R]
    (M : Mod R) (n : ℕ) : Prop :=
  FiniteFreeModule R M ∧
    Nonempty (M ≅ ModuleCat.of R (Fin n → R))

def FiberRankedComplex
    (R : Type u) [CommRing R] (E : Comp R) (d : ℤ → ℕ) : Prop :=
  IsBoundedAbove E ∧ ∀ i : ℤ, FiniteFreeRanked R (E.X i) (d i)

theorem lift_pseudoCoherent_from_residue_field
    (R : Type u) [CommRing R] [IsLocalRing R]
    [HasDerivedCategory.{w} (Mod R)]
    (K : D R) (d : ℤ → ℕ)
    (hfinite : ∃ b : ℤ, ∀ i : ℤ, b < i → d i = 0)
    (hK : IsPseudoCoherent R K) :
    ∃ E : Comp R, FiberRankedComplex R E d ∧
      Nonempty ((derivedQuotient R).obj E ≅ K) := by
  sorry

theorem lift_perfect_from_residue_field
    (R : Type u) [CommRing R] (p : PrimeSpectrum R)
    [HasDerivedCategory.{w} (Mod R)]
    (K : D R) (d : ℤ → ℕ)
    (hfinite : ∃ a b : ℤ, ∀ i : ℤ, i < a ∨ b < i → d i = 0)
    (hlocalDC : ∀ f : R, HasDerivedCategory.{w}
      (Mod (Localization.Away f)))
    (hK : Perfect R K) :
    ∃ f : R, f ∉ p.asIdeal ∧ letI := hlocalDC f
      ∃ E : Comp (Localization.Away f),
        FiberRankedComplex (Localization.Away f) E d ∧
          Nonempty ((derivedQuotient (Localization.Away f)).obj E ≅
            (derivedBaseChange (algebraMap R (Localization.Away f))).obj K) := by
  sorry

def TrivialComplex {R : Type u} [CommRing R] (E : Comp R) : Prop :=
  ∃ n : ℕ, ∃ s : Fin n → ℤ, ∀ i : ℤ,
    IsZero (E.X i) ∨ ∃ j : Fin n, s j = i

theorem compare_perfect_representatives
    (R : Type u) [CommRing R] (p : PrimeSpectrum R)
    [HasDerivedCategory.{w} (Mod R)]
    (M N : Comp R) (hM : BoundedFiniteProjectiveComplex R M)
    (hN : BoundedFiniteProjectiveComplex R N)
    (heq : Nonempty ((derivedQuotient R).obj M ≅
      (derivedQuotient R).obj N)) :
    ∃ f : R, f ∉ p.asIdeal ∧ ∃ P Q : Comp (Localization.Away f),
      TrivialComplex P ∧ TrivialComplex Q ∧
      Nonempty (baseChangeComplex (algebraMap R (Localization.Away f)) M ⊞ P ≅
        baseChangeComplex (algebraMap R (Localization.Away f)) N ⊞ Q) := by
  sorry

theorem lift_complex_finite_projectives_henselian
    (R : Type u) [CommRing R] (I : Ideal R)
    [HasDerivedCategory.{w} (Mod R)]
    [HasDerivedCategory.{w} (Mod (R ⧸ I))]
    (K : D R) (E : Comp (R ⧸ I))
    (hE : IsBoundedAbove E ∧ ∀ i : ℤ,
      FiniteProjectiveModule (R ⧸ I) (E.X i))
    (hrep : Nonempty ((derivedBaseChange (Ideal.Quotient.mk I)).obj K ≅
      (derivedQuotient (R ⧸ I)).obj E))
    (hK : IsPseudoCoherent R K)
    (hI : IsHenselianPairIdeal I) :
    ∃ P : Comp R, IsBoundedAbove P ∧
      (∀ i : ℤ, FiniteProjectiveModule R (P.X i)) ∧
      Nonempty ((derivedQuotient R).obj P ≅ K) ∧
      Nonempty (baseChangeComplex (Ideal.Quotient.mk I) P ≅ E) := by
  sorry

end Formalization.Books.MoreAlgebra.Unit75
