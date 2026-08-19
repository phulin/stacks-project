import Formalization.Books.MoreAlgebra.Unit11
import Formalization.Books.Algebra.Unit97.CompletionForNoetherianRings
import Formalization.Books.Algebra.Unit155.Henselization
import Formalization.Books.Algebra.Unit154.FilteredColimitsEtale
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.CategoryTheory.Filtered.Basic
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.RingHom.Etale
import Mathlib.RingTheory.TensorProduct.Basic

/-!
# More on Algebra, Chapter 12: Henselization of pairs

This file records the source-facing construction and theorem interfaces for
henselizations of pairs.  The pair and henselian-pair predicates are reused
from Chapter 11; quotient maps, adic completions, filtered étale colimits,
and local-ring henselizations are the canonical declarations from earlier
chapters and Mathlib.
-/

namespace Formalization.Books.MoreAlgebra.Unit12

open CategoryTheory
open CategoryTheory.Limits
open Formalization.Books.Algebra.Unit96
open Formalization.Books.Algebra.Unit154
open Formalization.Books.MoreAlgebra.Unit11
open scoped TensorProduct

noncomputable section

universe u

abbrev Pair (A : Type u) [CommRing A] :=
  Formalization.Books.MoreAlgebra.Unit11.Pair A

abbrev PairHom {A B : Type u} [CommRing A] [CommRing B]
    (P : Pair A) (Q : Pair B) (f : A →+* B) : Prop :=
  Formalization.Books.MoreAlgebra.Unit11.PairHom P Q f

abbrev HenselianPair {A : Type u} [CommRing A] (P : Pair A) : Prop :=
  Formalization.Books.MoreAlgebra.Unit11.HenselianPair P

/-! ## The directed étale system and its universal object -/

/-- A filtered colimit of the étale stages used to construct a henselization. -/
structure EtalePairColimit {A H : Type u} [CommRing A] [CommRing H]
    (P : Pair A) (f : A →+* H)
    extends Formalization.Books.Algebra.Unit154.FilteredColimitData f where
  etale : ∀ i, RingHom.Etale (diagram.obj i).hom.hom
  reduction : ∀ i, Function.Bijective
    (Formalization.Books.Algebra.Unit138.quotientBaseChangeRingMap
      (diagram.obj i).hom.hom P.ideal)

/-- A henselization of a pair, bundled with its filtered-étale construction
and its universal property among henselian pairs. -/
structure HenselizationData {A : Type u} [CommRing A] (P : Pair A) where
  carrier : Type u
  [commRingCarrier : CommRing carrier]
  map : A →+* carrier
  henselian : HenselianPair
    ({ ideal := Ideal.map map P.ideal } : Pair carrier)
  etaleColimit : Nonempty (EtalePairColimit P map)
  universal :
    ∀ {B : Type u} [CommRing B] (Q : Pair B), HenselianPair Q →
      ∀ (f : A →+* B), PairHom P Q f →
        ∃! g : carrier →+* B,
          PairHom ({ ideal := Ideal.map map P.ideal } : Pair carrier) Q g ∧
            g.comp map = f

instance {A : Type u} [CommRing A] (P : Pair A)
    (D : HenselizationData P) : CommRing D.carrier :=
  D.commRingCarrier

/-- The distinguished ideal on the henselization represented by `D`. -/
def henselizedPair {A : Type u} [CommRing A] (P : Pair A)
    (D : HenselizationData P) : Pair D.carrier :=
  { ideal := Ideal.map D.map P.ideal }

/-- The left-adjoint assertion from the source, expressed by the existence of
a universal henselian pair over every pair. -/
theorem henselization_left_adjoint
    {A : Type u} [CommRing A] (P : Pair A) :
    Nonempty (HenselizationData P) := by
  sorry

/-! ## Flatness and quotients -/

theorem henselization_flat
    {A : Type u} [CommRing A] (P : Pair A)
    (D : HenselizationData P) :
    RingHom.Flat D.map ∧
      (henselizedPair P D).ideal = Ideal.map D.map P.ideal ∧
      ∀ n : ℕ,
        Function.Bijective
          (Formalization.Books.Algebra.Unit138.quotientBaseChangeRingMap
            D.map (P.ideal ^ n)) := by
  sorry

/-! ## Local rings -/

/-- The canonical local-ring henselization interface, with the target local
ring structure existentially supplied because a pair henselization is only
bundled with a commutative-ring structure. -/
def LocalRingHenselizationMap
    {A H : Type u} [CommRing A] [IsLocalRing A] [CommRing H]
    (f : A →+* H) : Prop :=
  ∃ hH : IsLocalRing H,
    @Formalization.Books.Algebra.Unit155.IsHenselizationMap
      A H _ _ _ hH f

theorem henselization_local_ring
    {A : Type u} [CommRing A] [IsLocalRing A]
    (D : HenselizationData
      ({ ideal := IsLocalRing.maximalIdeal A } : Pair A)) :
    LocalRingHenselizationMap D.map := by
  sorry

/-! ## Noetherian pairs and completion -/

theorem henselization_noetherian_pair
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    (P : Pair A) (D : HenselizationData P) :
    (∃ e : ringCompletion P.ideal ≃+*
        ringCompletion (Ideal.map D.map P.ideal),
      e.toRingHom.comp (algebraMap A (ringCompletion P.ideal)) =
        (algebraMap D.carrier
          (ringCompletion (Ideal.map D.map P.ideal))).comp D.map) ∧
      IsNoetherianRing D.carrier ∧
      RingHom.Flat D.map ∧
      RingHom.Flat
        (algebraMap D.carrier
          (ringCompletion (Ideal.map D.map P.ideal))) ∧
      RingHom.FaithfullyFlat
        (algebraMap D.carrier
          (ringCompletion (Ideal.map D.map P.ideal))) := by
  sorry

/-! ## Filtered colimits -/

/-- A filtered system of pairs with a specified colimit pair.  The ideal
condition uses the canonical span of the extended stage ideals. -/
structure FilteredPairSystem {A : Type u} [CommRing A] (P : Pair A) where
  index : Type u
  [indexCategory : Category index]
  [indexFiltered : IsFiltered index]
  diagram : index ⥤ CommRingCat
  ideals : ∀ i, Ideal (diagram.obj i)
  compatible : ∀ {i j : index} (f : i ⟶ j),
    Ideal.map (diagram.map f).hom (ideals i) ≤ ideals j
  cocone : Cocone diagram
  isColimit : IsColimit cocone
  targetIso : cocone.pt ≅ CommRingCat.of A
  ideal_eq : P.ideal = Ideal.span (⋃ i,
    (Ideal.map
      (targetIso.hom.hom.comp (cocone.ι.app i).hom) (ideals i) : Set A))

instance {A : Type u} [CommRing A] {P : Pair A}
    (S : FilteredPairSystem P) : Category S.index :=
  S.indexCategory

instance {A : Type u} [CommRing A] {P : Pair A}
    (S : FilteredPairSystem P) : IsFiltered S.index :=
  S.indexFiltered

/-- Stage henselizations together with their filtered colimit diagram. -/
structure FilteredHenselizationData
    {A : Type u} [CommRing A] {P : Pair A}
    (S : FilteredPairSystem P) where
  stage : ∀ i, HenselizationData ({ ideal := S.ideals i } :
    Pair (S.diagram.obj i))
  stageDiagram : S.index ⥤ CommRingCat
  [stageHasColimit : HasColimit stageDiagram]
  stageObjectIso : ∀ i,
    stageDiagram.obj i ≅ CommRingCat.of (stage i).carrier
  target : HenselizationData P

instance {A : Type u} [CommRing A] {P : Pair A}
    {S : FilteredPairSystem P} (D : FilteredHenselizationData S) :
    HasColimit D.stageDiagram :=
  D.stageHasColimit

/-- The ideal obtained by extending the distinguished stage ideals to the
filtered colimit of the stage henselizations. -/
def stageColimitIdeal
    {A : Type u} [CommRing A] {P : Pair A}
    {S : FilteredPairSystem P} (D : FilteredHenselizationData S) :
    Ideal ((colimit D.stageDiagram : CommRingCat) : Type u) :=
  Ideal.span (⋃ i : S.index,
    (Ideal.map
      ((colimit.ι D.stageDiagram i).hom.comp
        ((D.stageObjectIso i).inv.hom.comp (D.stage i).map))
      (S.ideals i) : Set ((colimit D.stageDiagram : CommRingCat) : Type u)))

theorem henselization_filtered_colimit
    {A : Type u} [CommRing A] {P : Pair A}
    (S : FilteredPairSystem P) (D : FilteredHenselizationData S) :
    ∃ e : (colimit D.stageDiagram : CommRingCat) ≃+* D.target.carrier,
      Ideal.map e.toRingHom (stageColimitIdeal D) =
        Ideal.map D.target.map P.ideal := by
  sorry

/-- The non-filtered-colimit warning is witnessed by the existing
Moret--Bailly example from Chapter 11. -/
theorem henselization_nonfiltered_colimit_warning
    (p : ℕ) [Fact p.Prime] (hp : 2 < p) :
    ¬ HenselianPair
        ({ ideal := Formalization.Books.MoreAlgebra.Unit11.moretBaillyIdeal p } :
          Pair (Formalization.Books.MoreAlgebra.Unit11.moretBaillyRing p)) ∧
      ∃ e : Formalization.Books.MoreAlgebra.Unit11.moretBaillyRing p,
        IsIdempotentElem e ∧ e ≠ 0 ∧ e ≠ 1 := by
  exact Formalization.Books.MoreAlgebra.Unit11.moret_bailly_example p hp

/-! ## Change of ideal -/

theorem henselization_change_ideal
    {A : Type u} [CommRing A] (I J : Ideal A)
    (hV : PrimeSpectrum.zeroLocus (I : Set A) =
      PrimeSpectrum.zeroLocus (J : Set A))
    (DI : HenselizationData ({ ideal := I } : Pair A))
    (DJ : HenselizationData ({ ideal := J } : Pair A)) :
    ∃ e : DI.carrier ≃+* DJ.carrier,
      e.toRingHom.comp DI.map = DJ.map := by
  sorry

/-! ## Integral base change -/

theorem henselization_integral_base_change
    {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    (P : Pair A) (Q : Pair B)
    (hpair : PairHom P Q (algebraMap A B))
    (hV : PrimeSpectrum.zeroLocus (Q.ideal : Set B) =
      PrimeSpectrum.zeroLocus
        (Ideal.map (algebraMap A B) P.ideal : Set B))
    (DP : HenselizationData P) (DQ : HenselizationData Q)
    (hIntegral : RingHom.IsIntegral (algebraMap A B)) :
    letI : Algebra A DP.carrier := DP.map.toAlgebra
    Nonempty (DP.carrier ⊗[A] B ≃+* DQ.carrier) := by
  sorry

/-! ## Chinese remainder decomposition -/

theorem henselization_chinese_remainder
    {A : Type u} [CommRing A] (n : ℕ) (hn : 0 < n)
    (I : Fin n → Ideal A)
    (hI : ∀ i j, i ≠ j → I i + I j = ⊤)
    (D : HenselizationData ({ ideal := ⨅ i, I i } : Pair A))
    (Di : ∀ i, HenselizationData ({ ideal := I i } : Pair A)) :
    letI : ∀ i, CommRing (Di i).carrier :=
      fun i => (Di i).commRingCarrier
    ∃ e : D.carrier ≃+* (∀ i, (Di i).carrier),
      ∀ (a : A) (i : Fin n), e (D.map a) i = (Di i).map a := by
  sorry

end

end Formalization.Books.MoreAlgebra.Unit12
