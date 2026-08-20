import Formalization.Books.MoreAlgebra.Unit74.DerivedHom
import Formalization.Books.MoreAlgebra.Unit75.PerfectComplexes
import Formalization.Books.MoreAlgebra.Unit67.TorDimension
import Formalization.Books.MoreAlgebra.Unit70.InjectiveDimension
import Formalization.Books.Derived.Unit11.DerivedCategories
import Formalization.Books.Derived.Unit12.CanonicalDeltaFunctor

/-!
# More on Algebra, Chapter 99: Some evaluation maps

The source proves four criteria for the canonical derived evaluation maps.  The
derived operations and finiteness predicates below are the canonical interfaces
from earlier chapters; this file records the chapter-specific hypotheses and
conclusions without reproving the results.
-/

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open Formalization.Books.Derived.Unit08
open Formalization.Books.Derived.Unit11
open Formalization.Books.Derived.Unit12
open Formalization.Books.MoreAlgebra.Unit59
open Formalization.Books.MoreAlgebra.Unit65
open Formalization.Books.MoreAlgebra.Unit67
open Formalization.Books.MoreAlgebra.Unit70
open Formalization.Books.MoreAlgebra.Unit74
open Formalization.Books.MoreAlgebra.Unit75
open Formalization.Books.MoreAlgebra.Unit73

universe w u

namespace Formalization.Books.MoreAlgebra.Unit99

abbrev Comp (R : Type u) [CommRing R] := Unit74.Comp R

abbrev D (R : Type u) [CommRing R]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)] := Unit74.D R

/- The first source lemma gives two sufficient hypotheses for the evaluation
map `RHom(L, M) ⊗ᴸ K → RHom(RHom(K, L), M)`. -/
theorem internalHom_evaluate_isIso_of_perfect_or_pseudoCoherent
    {R : Type u} [CommRing R]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)]
    (K L M : D R)
    (h : Perfect R K ∨
      (IsPseudoCoherent R K ∧
        derivedPlusProperty (ModuleCat.{u} R) L ∧
          HasFiniteInjectiveDimension (R := R) (K := M))) :
    IsIso (internalHomEvaluationMap (R := R) K L M) := by
  sorry

/- The second source lemma uses the canonical lower truncation `τ ≤ n K` in
the derived category. -/
theorem internalHom_evaluate_isIso_of_finite_dimensions
    {R : Type u} [CommRing R]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)]
    (K L M : D R)
    (hL : HasFiniteInjectiveDimension (R := R) (K := L))
    (hM : HasFiniteInjectiveDimension (R := R) (K := M))
    (hLM : HasFiniteTorDimension R (RHom (R := R) L M))
    (hK : ∀ n : ℤ,
      IsPseudoCoherent R
        (((canonicalTStructure (ModuleCat.{u} R)).truncLE n).obj K)) :
    IsIso (internalHomEvaluationMap (R := R) K L M) := by
  sorry

/- The third source lemma is the corresponding criterion for
`K ⊗ᴸ RHom(M, L) → RHom(M, K ⊗ᴸ L)`. -/
theorem internalHom_diagonal_isIso_of_cases
    {R : Type u} [CommRing R]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)]
    (K L M : D R) (a : ℤ)
    (h : Perfect R M ∨ Perfect R K ∨
      (IsPseudoCoherent R M ∧
        derivedPlusProperty (ModuleCat.{u} R) L ∧
          TorAmplitudeBelow R K a)) :
    IsIso (internalHomDiagonalBetterMap (R := R) K L M) := by
  sorry

/- The final source lemma records both conclusions about the ordinary Hom
complex of a bounded-above projective representative. -/
theorem homComplex_isKFlat_and_represents_RHom
    {R : Type u} [CommRing R]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)]
    (P K : Comp R)
    (hP : IsBoundedAbove P)
    (hPprojective : IsTermwiseProjective P)
    (hPperfect : Perfect R ((Unit74.derivedQuotient R).obj P))
    (hK : Unit59.IsKFlat K) :
    Unit59.IsKFlat (homComplex P K) ∧
      Nonempty
        (RHom (R := R) ((Unit74.derivedQuotient R).obj P)
            ((Unit74.derivedQuotient R).obj K) ≅
          (Unit74.derivedQuotient R).obj (homComplex P K)) := by
  sorry

end Formalization.Books.MoreAlgebra.Unit99
