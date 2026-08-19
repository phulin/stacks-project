import Formalization.Books.MoreAlgebra.Unit75.CharacterizingPerfectComplexes
import Formalization.Books.Algebra.Unit110.RegularRingsAndGlobalDimension
import Formalization.Books.Derived.Unit36.GeneratorsOfTriangulatedCategories

/-!
# More on Algebra, Chapter 75: strong generators and regular rings

The ghost argument is indexed by a natural number and uses an explicit
recursive composite for the chain of maps.  The regularity statements use
Mathlib's `IsRegularRing` and the existing strong-generator stages.
-/

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open Formalization.Books.Derived.Unit08
open Formalization.Books.Derived.Unit11
open Formalization.Books.Derived.Unit36
open Formalization.Books.MoreAlgebra.Unit65
open Formalization.Books.MoreAlgebra.Unit67
open Formalization.Books.MoreAlgebra.Unit75

universe w u

namespace Formalization.Books.MoreAlgebra.Unit75

def chainComposite
    (R : Type u) [CommRing R]
    [HasDerivedCategory.{w} (Mod R)]
    (n : ℕ) (E : ℕ → D R)
    (f : ∀ j : ℕ, j < n → ((E j) ⟶ (E (j + 1)))) : (E 0) ⟶ (E n) :=
  match n with
  | 0 => 𝟙 _
  | n + 1 =>
      f 0 (Nat.zero_lt_succ n) ≫
        chainComposite R n (fun j => E (j + 1))
          (fun j hj => f (j + 1) (Nat.succ_lt_succ hj))

def IsGhostMap
    (R : Type u) [CommRing R]
    [HasDerivedCategory.{w} (Mod R)] {K L : D R}
    (f : K ⟶ L) : Prop :=
  ∀ i : ℤ, (derivedCohomologyFunctor (Mod R) i).map f = 0

def IsStrongGeneratorForPerfect
    (R : Type u) [CommRing R]
    [HasDerivedCategory.{w} (Mod R)] (E : D R) : Prop :=
  Perfect R E ∧ ∃ n : ℕ, 1 ≤ n ∧
    ∀ K : D R, Perfect R K → generatedSubcategoryIter E n K

def HasStrongGeneratorForPerfect
    (R : Type u) [CommRing R]
    [HasDerivedCategory.{w} (Mod R)] : Prop :=
  ∃ E : D R, IsStrongGeneratorForPerfect R E

theorem ghost_lemma
    (R : Type u) [CommRing R]
    [HasDerivedCategory.{w} (Mod R)] (n : ℕ) (hn : 1 ≤ n)
    (G : D R) (E : ℕ → D R) (hE : generatedSubcategoryIter G n (E 0))
    (f : ∀ j : ℕ, j < n → ((E j) ⟶ (E (j + 1))))
    (hghost : ∀ j : ℕ, ∀ hj : j < n, IsGhostMap R (f j hj)) :
    chainComposite R n E f = 0 := by
  sorry

theorem not_regular_not_strong
    (R : Type u) [CommRing R] [IsNoetherianRing R]
    [HasDerivedCategory.{w} (Mod R)]
    (hstrong : HasStrongGeneratorForPerfect R) :
    IsRegularRing R ∧ ∃ d : ℕ, ringKrullDim R = d := by
  sorry

theorem ext_regular
    (R : Type u) [CommRing R] [IsNoetherianRing R]
    [HasDerivedCategory.{w} (Mod R)] (d : ℕ)
    (hreg : IsRegularRing R) (hdim : ringKrullDim R = d)
    (K L : D R) (hK : IsInDMinus R K) (hL : IsInDMinus R L)
    (k : ℤ)
    (hKvanish : ∀ i : ℤ, i ≤ k →
      IsZero ((derivedCohomologyFunctor (Mod R) i).obj K))
    (hLvanish : ∀ i : ℤ, k - (d : ℤ) + 1 ≤ i →
      IsZero ((derivedCohomologyFunctor (Mod R) i).obj L)) :
    ∀ f : K ⟶ L, f = 0 := by
  sorry

theorem split_complex_regular
    (R : Type u) [CommRing R] [IsNoetherianRing R]
    [HasDerivedCategory.{w} (Mod R)] (d : ℕ)
    (hreg : IsRegularRing R) (hdim : 1 ≤ d ∧ ringKrullDim R = d)
    (K : D R) (hK : Perfect R K) (k : ℤ)
    (hvanish : ∀ i : ℤ, k - (d : ℤ) + 2 ≤ i → i ≤ k →
      IsZero ((derivedCohomologyFunctor (Mod R) i).obj K)) :
    ∃ T : CanonicalTruncation R K (k - (d : ℤ) + 1),
      Nonempty (K ≅ T.lower ⊞ T.upper) := by
  sorry

theorem regular_strong_generator
    (R : Type u) [CommRing R] [IsNoetherianRing R]
    [HasDerivedCategory.{w} (Mod R)]
    (hreg : IsRegularRing R) (hdim : ∃ d : ℕ, ringKrullDim R = d) :
    IsStrongGeneratorForPerfect R (moduleInDerived R (ModuleCat.of R R)) := by
  sorry

theorem regular_strong_generator_iff
    (R : Type u) [CommRing R] [IsNoetherianRing R]
    [HasDerivedCategory.{w} (Mod R)] :
    List.TFAE [
      IsRegularRing R ∧ ∃ d : ℕ, ringKrullDim R = d,
      HasStrongGeneratorForPerfect R,
      IsStrongGeneratorForPerfect R (moduleInDerived R (ModuleCat.of R R))] := by
  sorry

end Formalization.Books.MoreAlgebra.Unit75
