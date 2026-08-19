import Formalization.Books.MoreAlgebra.Unit75.StrongGenerators
import Formalization.Books.MoreAlgebra.Unit79.CharacterizingPerfectComplexes

/-!
# More on Algebra, Chapter 80: Strong generators and regular rings

This chapter records the ghost lemma, the regularity obstruction, the
Ext-vanishing and splitting interfaces, and the characterization of regular
Noetherian rings by strong generation of perfect complexes.  The derived
category and regular-ring constructions are reused from earlier chapters.
-/

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open Formalization.Books.Derived.Unit08
open Formalization.Books.Derived.Unit11
open Formalization.Books.Derived.Unit36
open Formalization.Books.Derived.Unit37
open Formalization.Books.MoreAlgebra.Unit65
open Formalization.Books.MoreAlgebra.Unit75
open Formalization.Books.MoreAlgebra.Unit79
open scoped CategoryTheory.Preadditive CategoryTheory.Pretriangulated.Opposite

universe w u

namespace Formalization.Books.MoreAlgebra.Unit80

abbrev Mod (R : Type u) [CommRing R] := Unit75.Mod R

abbrev D (R : Type u) [CommRing R]
    [HasDerivedCategory.{w} (Mod R)] := Unit75.D R

abbrev derivedObject (R : Type u) [CommRing R]
    [HasDerivedCategory.{w} (Mod R)] : D R :=
  Unit75.moduleInDerived R (ModuleCat.of R R)

abbrev PerfectObjects (R : Type u) [CommRing R]
    [HasDerivedCategory.{w} (Mod R)] : ObjectProperty (D R) :=
  Unit79.PerfectObjects R

/-! The introductory identification `⟨R⟩ = D_perf(R) = D(R)_c`. -/
theorem perfect_eq_generated_eq_compact
    (R : Type u) [CommRing R]
    [HasDerivedCategory.{w} (Mod R)]
    [HasCoproducts (D R)] :
    generatedSubcategory (derivedObject R) = PerfectObjects R ∧
      PerfectObjects R = compactObjects := by
  constructor
  · exact (Unit79.perfect_ring_classical_generator R).1.symm
  · funext K
    exact propext (Unit79.perfect_is_compact R K)

/-! The source's cohomology-zero maps. -/
abbrev IsGhostMap
    (R : Type u) [CommRing R]
    [HasDerivedCategory.{w} (Mod R)] {K L : D R}
    (f : K ⟶ L) : Prop :=
  ∀ i : ℤ, (derivedCohomologyFunctor (Mod R) i).map f = 0

abbrev chainComposite
    (R : Type u) [CommRing R]
    [HasDerivedCategory.{w} (Mod R)]
    (n : ℕ) (E : ℕ → D R)
    (f : ∀ j : ℕ, j < n → ((E j) ⟶ (E (j + 1)))) : (E 0) ⟶ (E n) :=
  Unit75.chainComposite R n E f

abbrev IsStrongGeneratorForPerfect
    (R : Type u) [CommRing R]
    [HasDerivedCategory.{w} (Mod R)] (E : D R) : Prop :=
  Unit75.IsStrongGeneratorForPerfect R E

abbrev HasStrongGeneratorForPerfect
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
  exact Unit75.ghost_lemma R n hn G E hE f hghost

theorem not_regular_not_strong
    (R : Type u) [CommRing R] [IsNoetherianRing R]
    [HasDerivedCategory.{w} (Mod R)]
    (hstrong : IsStrongGeneratorForPerfect R (derivedObject R)) :
    IsRegularRing R ∧ ∃ d : ℕ, ringKrullDim R = d := by
  exact Unit75.not_regular_not_strong R ⟨derivedObject R, hstrong⟩

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
  exact Unit75.ext_regular R d hreg hdim K L hK hL k hKvanish hLvanish

theorem split_complex_regular
    (R : Type u) [CommRing R] [IsNoetherianRing R]
    [HasDerivedCategory.{w} (Mod R)] (d : ℕ)
    (hreg : IsRegularRing R) (hdim : 1 ≤ d ∧ ringKrullDim R = d)
    (K : D R) (hK : Perfect R K) (k : ℤ)
    (hvanish : ∀ i : ℤ, k - (d : ℤ) + 2 ≤ i → i ≤ k →
      IsZero ((derivedCohomologyFunctor (Mod R) i).obj K)) :
    ∃ T : CanonicalTruncation R K (k - (d : ℤ) + 1),
      Nonempty (K ≅ T.lower ⊞ T.upper) := by
  exact Unit75.split_complex_regular R d hreg hdim K hK k hvanish

theorem regular_strong_generator
    (R : Type u) [CommRing R] [IsNoetherianRing R]
    [HasDerivedCategory.{w} (Mod R)]
    (hreg : IsRegularRing R) (hdim : ∃ d : ℕ, ringKrullDim R = d) :
    IsStrongGeneratorForPerfect R (derivedObject R) := by
  exact Unit75.regular_strong_generator R hreg hdim

theorem regular_strong_generator_iff
    (R : Type u) [CommRing R] [IsNoetherianRing R]
    [HasDerivedCategory.{w} (Mod R)] :
    List.TFAE [
      IsRegularRing R ∧ ∃ d : ℕ, ringKrullDim R = d,
      HasStrongGeneratorForPerfect R,
      IsStrongGeneratorForPerfect R (derivedObject R)] := by
  exact Unit75.regular_strong_generator_iff R

end Formalization.Books.MoreAlgebra.Unit80
