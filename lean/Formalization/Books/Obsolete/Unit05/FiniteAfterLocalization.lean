import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.RingHom.Finite

namespace Formalization.Books.Obsolete.Unit05

universe u

noncomputable section

/-- The solid part of the localization diagram used in the finite-after-localization lemma.

The two localization targets are represented by Mathlib's canonical `Localization.Away`
constructions.  The map from `R_f` to `S_f` is retained as data so that the commutativity
conditions describe the source diagram without relying on a particular normal form for its
induced map.
-/
structure FiniteAfterLocalizationDiagram
    (R S S' : Type u) [CommRing R] [CommRing S] [CommRing S'] (f : R) where
  rS : R →+* S
  rfS' : Localization.Away f →+* S'
  s'Sf : S' →+* Localization.Away (rS f)
  rfSf : Localization.Away f →+* Localization.Away (rS f)
  commute_lower : s'Sf.comp rfS' = rfSf
  commute_outer :
    (algebraMap S (Localization.Away (rS f))).comp rS =
      rfSf.comp (algebraMap R (Localization.Away f))
  finite : RingHom.Finite rfS'

/-- A finite map over `R_f` extends to a finite `R`-algebra whose localization is `S'`. -/
theorem finite_after_localization
    {R S S' : Type u} [CommRing R] [CommRing S] [CommRing S']
    (f : R) (D : FiniteAfterLocalizationDiagram R S S' f) :
    ∃ (S'' : Type u) (hS'' : CommRing S''),
      letI : CommRing S'' := hS''
      ∃ (rS'' : R →+* S''),
        RingHom.Finite rS'' ∧
          ∃ (s''S : S'' →+* S) (s''S' : S'' →+* S'),
            s''S.comp rS'' = D.rS ∧
              s''S'.comp rS'' = D.rfS'.comp (algebraMap R (Localization.Away f)) ∧
                (algebraMap S (Localization.Away (D.rS f))).comp s''S =
                  D.s'Sf.comp s''S' ∧
                    (letI : Algebra S'' S' := s''S'.toAlgebra
                     IsLocalization.Away (rS'' f) S') := by
  sorry

end
end Formalization.Books.Obsolete.Unit05
