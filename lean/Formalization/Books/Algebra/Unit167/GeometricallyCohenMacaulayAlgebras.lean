import Formalization.Books.Algebra.Unit31.NoetherianRings
import Formalization.Books.Algebra.Unit163.AscendingProperties
import Mathlib.RingTheory.TensorProduct.Basic

/-!
# Commutative Algebra, Chapter 167: Geometrically Cohen-Macaulay algebras

This file records the two precise lemmas in the source section.  The source
does not introduce a separate predicate for “geometrically Cohen-Macaulay”;
the second lemma is the stated invariance of the Cohen–Macaulay local
condition after a finitely generated field extension.
-/

namespace Formalization.Books.Algebra.Unit167

open Formalization.Books.Algebra.Unit104
open Formalization.Books.Algebra.Unit31
open Formalization.Books.Algebra.Unit163
open scoped TensorProduct

universe u v w

noncomputable section

/- The first source lemma assumes that one of the two field extensions is of
finite type and concludes that their tensor product is a Noetherian
Cohen–Macaulay ring.  The existential form packages the Noetherian instance
needed by the canonical global Cohen–Macaulay predicate. -/
theorem tensorProduct_fields_isNoetherian_and_isCohenMacaulay
    {k : Type u} {K : Type v} {L : Type w} [Field k] [Field K] [Field L]
    [Algebra k K] [Algebra k L]
    (hfinite : Algebra.FiniteType k K ∨ Algebra.FiniteType k L) :
    ∃ hT : IsNoetherianRing (K ⊗[k] L),
      letI : IsNoetherianRing (K ⊗[k] L) := hT
      IsCohenMacaulayRing (K ⊗[k] L) := by
  sorry

/- The second source lemma is stated at a prime and its chosen prime after
base change.  The displayed “lying over” condition is the canonical
prime-spectrum comap condition for the right tensor-product inclusion. -/
theorem isCohenMacaulayLocalRing_iff_tensorProduct
    {k : Type u} {S : Type v} {K : Type w} [Field k] [CommRing S] [Field K]
    [Algebra k S] [Algebra k K] [Algebra.FiniteType k K]
    [IsNoetherianRing S]
    (q : PrimeSpectrum S)
    (qK : PrimeSpectrum (K ⊗[k] S))
    (hqK : PrimeSpectrum.comap Algebra.TensorProduct.includeRight.toRingHom qK = q) :
    letI : IsNoetherianRing (K ⊗[k] S) :=
      tensorProduct_isNoetherian_of_finiteType_fieldExtension (R := S) (K := K)
    IsCohenMacaulayLocalRing (Localization.AtPrime q.asIdeal) ↔
      IsCohenMacaulayLocalRing (Localization.AtPrime qK.asIdeal) := by
  sorry

end
end Formalization.Books.Algebra.Unit167
