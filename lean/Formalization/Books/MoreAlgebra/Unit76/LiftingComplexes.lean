import Formalization.Books.MoreAlgebra.Unit75.PerfectComplexes
import Formalization.Books.MoreAlgebra.Unit03.StablyFree
import Formalization.Books.MoreAlgebra.Unit13
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.RingTheory.LocalRing.ResidueField.Ideal

/-!
# More on Algebra, Chapter 76: lifting complexes

The source asks when a complex over `R / I` can be lifted to a complex over
`R`.  Complexes and derived categories below are the canonical ones from the
preceding chapters; the declarations only package the source's hypotheses
and conclusions.
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
open Formalization.Books.MoreAlgebra.Unit67
open Formalization.Books.MoreAlgebra.Unit75

universe w u

namespace Formalization.Books.MoreAlgebra.Unit76

abbrev Mod (R : Type u) [CommRing R] := ModuleCat.{u} R

abbrev Comp (R : Type u) [CommRing R] := Unit75.Comp R

abbrev D (R : Type u) [CommRing R]
    [HasDerivedCategory.{w} (Mod R)] := Unit75.D R

noncomputable abbrev derivedQuotient (R : Type u) [CommRing R]
    [HasDerivedCategory.{w} (Mod R)] : Comp R ⥤ D R :=
  Unit75.derivedQuotient R

noncomputable abbrev derivedBaseChange
    {A B : Type u} [CommRing A] [CommRing B]
    [HasDerivedCategory.{w} (Mod A)] [HasDerivedCategory.{w} (Mod B)]
    (f : A →+* B) : D A ⥤ D B :=
  Unit75.derivedBaseChange f

/-! ## The two lifting lemmas -/

def SurjectiveModuloIdeal {R : Type u} [CommRing R] {M N : Mod R}
    (I : Ideal R) (f : M ⟶ N) : Prop :=
  ∀ y : (N : Type u), ∃ x : (M : Type u),
    f.hom x - y ∈ I • (⊤ : Submodule R (N : Type u))

/- The class used for lifting an acyclic complex. -/
def LiftingClass {R : Type u} [CommRing R] (I : Ideal R)
    (PClass : Set (Mod R)) : Prop :=
  (∀ P : Mod R, P ∈ PClass → Module.Projective R (P : Type u)) ∧
    (∀ P₁ P₂ : Mod R, P₁ ∈ PClass → (P₁ ⊞ P₂) ∈ PClass → P₂ ∈ PClass) ∧
    (∀ P₁ P₂ : Mod R, P₁ ∈ PClass → P₂ ∈ PClass →
      ∀ f : P₁ ⟶ P₂, SurjectiveModuloIdeal I f → Function.Surjective f.hom)

/- The stronger closure condition required by the second lifting lemma. -/
def LiftingClassWithBiproducts {R : Type u} [CommRing R] (I : Ideal R)
    (PClass : Set (Mod R)) : Prop :=
  (∀ P : Mod R, P ∈ PClass → Module.Projective R (P : Type u)) ∧
    (∀ P₁ P₂ : Mod R,
      (P₁ ∈ PClass ∧ (P₁ ⊞ P₂) ∈ PClass) ↔
        (P₁ ∈ PClass ∧ P₂ ∈ PClass)) ∧
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
    (PClass : Set (Mod R)) (hPClass : LiftingClassWithBiproducts I PClass)
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

/-! ## Nilpotent and stably-free lifting -/

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
      Nonempty (baseChangeComplex (Ideal.Quotient.mk I) P ≅ E) ∧
      ((∀ i : ℤ, Module.Free (R ⧸ I) (E.X i : Type u)) →
        ∀ i : ℤ, Module.Free R (P.X i : Type u)) := by
  sorry

/-! ## Minimal complexes over a local ring -/

noncomputable def LocalResidueCohomology
    (R : Type u) [CommRing R] [IsLocalRing R]
    [HasDerivedCategory.{w} (Mod R)]
    [HasDerivedCategory.{w} (Mod (IsLocalRing.ResidueField R))]
    (K : D R) (i : ℤ) : Mod (IsLocalRing.ResidueField R) :=
  (derivedCohomologyFunctor (Mod (IsLocalRing.ResidueField R)) i).obj
    ((derivedBaseChange (algebraMap R (IsLocalRing.ResidueField R))).obj K)

noncomputable def LocalResidueCohomologyRank
    (R : Type u) [CommRing R] [IsLocalRing R]
    [HasDerivedCategory.{w} (Mod R)]
    [HasDerivedCategory.{w} (Mod (IsLocalRing.ResidueField R))]
    (K : D R) (i : ℤ) : ℕ :=
  Module.finrank (IsLocalRing.ResidueField R)
    (LocalResidueCohomology R K i : Type u)

def LocalResidueCohomologyFinite
    (R : Type u) [CommRing R] [IsLocalRing R]
    [HasDerivedCategory.{w} (Mod R)]
    [HasDerivedCategory.{w} (Mod (IsLocalRing.ResidueField R))]
    (K : D R) (i : ℤ) : Prop :=
  Module.Finite (IsLocalRing.ResidueField R)
    (LocalResidueCohomology R K i : Type u)

def FiniteFreeRanked (R : Type u) [CommRing R]
    (M : Mod R) (n : ℕ) : Prop :=
  FiniteFreeModule R M ∧
    Nonempty (M ≅ ModuleCat.of R (Fin n → R))

def FiberRankedComplex
    (R : Type u) [CommRing R] (E : Comp R) (d : ℤ → ℕ) : Prop :=
  IsBoundedAbove E ∧ ∀ i : ℤ, FiniteFreeRanked R (E.X i) (d i)

def BoundedFiberRankedComplex
    (R : Type u) [CommRing R] (E : Comp R) (d : ℤ → ℕ) : Prop :=
  IsBounded E ∧ ∀ i : ℤ, FiniteFreeRanked R (E.X i) (d i)

def IsMinimalAtResidueField
    (R : Type u) [CommRing R] [IsLocalRing R]
    (E : Comp R) : Prop :=
  ∀ i : ℤ,
    (baseChangeComplex (Ideal.Quotient.mk (IsLocalRing.maximalIdeal R)) E).d i (i + 1) = 0

theorem lift_pseudoCoherent_from_residue_field
    (R : Type u) [CommRing R] [IsLocalRing R]
    [HasDerivedCategory.{w} (Mod R)]
    [HasDerivedCategory.{w} (Mod (IsLocalRing.ResidueField R))]
    (K : D R) (hK : IsPseudoCoherent R K) :
    let d : ℤ → ℕ := fun i => LocalResidueCohomologyRank R K i
    (∀ i : ℤ, LocalResidueCohomologyFinite R K i) ∧
      (∃ b : ℤ, ∀ i : ℤ, b < i → d i = 0) ∧
      ∃ E : Comp R, FiberRankedComplex R E d ∧
        Nonempty ((derivedQuotient R).obj E ≅ K) := by
  sorry

theorem minimal_complex_unique
    (R : Type u) [CommRing R] [IsLocalRing R]
    [HasDerivedCategory.{w} (Mod R)]
    (K : D R) (d : ℤ → ℕ) (F G : Comp R)
    (hF : FiberRankedComplex R F d) (hG : FiberRankedComplex R G d)
    (hFminimal : IsMinimalAtResidueField R F)
    (hGminimal : IsMinimalAtResidueField R G)
    (hFrep : Nonempty ((derivedQuotient R).obj F ≅ K))
    (hGrep : Nonempty ((derivedQuotient R).obj G ≅ K)) :
    Nonempty (F ≅ G) := by
  sorry

/-! ## Perfect complexes near a prime -/

noncomputable def FiberCohomology
    (R : Type u) [CommRing R] (p : PrimeSpectrum R)
    [HasDerivedCategory.{w} (Mod R)]
    [HasDerivedCategory.{w} (Mod p.asIdeal.ResidueField)]
    (K : D R) (i : ℤ) : Mod p.asIdeal.ResidueField :=
  (derivedCohomologyFunctor (Mod p.asIdeal.ResidueField) i).obj
    ((derivedBaseChange (algebraMap R p.asIdeal.ResidueField)).obj K)

noncomputable def FiberCohomologyRank
    (R : Type u) [CommRing R] (p : PrimeSpectrum R)
    [HasDerivedCategory.{w} (Mod R)]
    [HasDerivedCategory.{w} (Mod p.asIdeal.ResidueField)]
    (K : D R) (i : ℤ) : ℕ :=
  Module.finrank p.asIdeal.ResidueField
    (FiberCohomology R p K i : Type u)

def FiberCohomologyFinite
    (R : Type u) [CommRing R] (p : PrimeSpectrum R)
    [HasDerivedCategory.{w} (Mod R)]
    [HasDerivedCategory.{w} (Mod p.asIdeal.ResidueField)]
    (K : D R) (i : ℤ) : Prop :=
  Module.Finite p.asIdeal.ResidueField
    (FiberCohomology R p K i : Type u)

theorem lift_perfect_from_residue_field
    (R : Type u) [CommRing R] (p : PrimeSpectrum R)
    [HasDerivedCategory.{w} (Mod R)]
    [HasDerivedCategory.{w} (Mod p.asIdeal.ResidueField)]
    (K : D R)
    (hlocalDC : ∀ f : R, HasDerivedCategory.{w}
      (Mod (Localization.Away f)))
    (hK : Perfect R K) :
    (∀ i : ℤ, FiberCohomologyFinite R p K i) ∧
      (∃ a b : ℤ, ∀ i : ℤ, i < a ∨ b < i →
        FiberCohomologyRank R p K i = 0) ∧
      ∃ f : R, f ∉ p.asIdeal ∧ letI := hlocalDC f
        ∃ E : Comp (Localization.Away f),
          BoundedFiberRankedComplex (Localization.Away f) E
            (FiberCohomologyRank R p K) ∧
            Nonempty ((derivedQuotient (Localization.Away f)).obj E ≅
              (derivedBaseChange (algebraMap R (Localization.Away f))).obj K) := by
  sorry

/-! ## Comparison after localization -/

noncomputable def TrivialSummand (R : Type u) [CommRing R] (n : ℤ) : Comp R :=
  CochainComplex.mappingCone
    (𝟙 ((CochainComplex.singleFunctor (Mod R) n).obj (ModuleCat.of R R)))

def TrivialComplex {R : Type u} [CommRing R] (E : Comp R) : Prop :=
  ∃ n : ℕ, ∃ s : Fin n → ℤ,
    Nonempty (E ≅ ∐ fun j : Fin n => TrivialSummand R (s j))

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

/-! ## Henselian lifting of finite projectives -/

theorem lift_complex_finite_projectives_henselian
    (R : Type u) [CommRing R] (I : Ideal R)
    [HasDerivedCategory.{w} (Mod R)]
    [HasDerivedCategory.{w} (Mod (R ⧸ I))]
    (K : D R) (E : Comp (R ⧸ I))
    (hE : IsBoundedAbove E ∧ ∀ i : ℤ,
      Unit65.FiniteProjectiveModule (R ⧸ I) (E.X i))
    (hrep : Nonempty ((derivedBaseChange (Ideal.Quotient.mk I)).obj K ≅
      (derivedQuotient (R ⧸ I)).obj E))
    (hK : IsPseudoCoherent R K)
    (hI : IsHenselianPairIdeal I) :
    ∃ P : Comp R, IsBoundedAbove P ∧
      (∀ i : ℤ, Unit65.FiniteProjectiveModule R (P.X i)) ∧
      Nonempty ((derivedQuotient R).obj P ≅ K) ∧
      Nonempty (baseChangeComplex (Ideal.Quotient.mk I) P ≅ E) ∧
      ((∀ i : ℤ, Module.Free (R ⧸ I) (E.X i : Type u)) →
        ∀ i : ℤ, Module.Free R (P.X i : Type u)) := by
  sorry

end Formalization.Books.MoreAlgebra.Unit76
