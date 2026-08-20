import Formalization.Books.Smoothing.Unit01.Introduction
import Formalization.Books.Algebra.Unit155.Henselization
import Formalization.Books.MoreAlgebra.Unit109.BranchesOfCompletion

/-!
# Smoothing Ring Maps, Chapter 13: The approximation property for G-rings

The chapter uses the canonical G-ring, completion, henselization, étale, and
polynomial-solution interfaces from earlier chapters.  The approximation
witnesses retain the comparison maps implicit in the source's completion
notation.
-/

namespace Formalization.Books.Smoothing.Unit13

open Formalization.Books.Algebra.Unit96
open Formalization.Books.Algebra.Unit155
open Formalization.Books.MoreAlgebra.Unit50
open Formalization.Books.MoreAlgebra.Unit41
open Formalization.Books.MoreAlgebra.Unit45
open Formalization.Books.MoreAlgebra.Unit109
open Formalization.Books.Smoothing.Unit01

noncomputable section

universe u

/-! ## G-rings and polynomial solutions -/

/- The source says “algebraic over `K`” for an element of a completion.  The
   coefficient-ring formulation is the precise one available without choosing
   a map from the fraction field into the completion. -/
/-- An element satisfies a nonzero polynomial over the source ring. -/
def SatisfiesNonzeroPolynomial
    {R A : Type u} [CommRing R] [CommRing A]
    (ρ : R →+* A) (x : A) : Prop :=
  ∃ P : Polynomial R, P ≠ 0 ∧ 0 < P.natDegree ∧
    Polynomial.eval₂ ρ x P = 0

/-- For a Noetherian local ring, the G-ring condition is equivalent to
regularity of the map to its local completion. -/
theorem isGRing_iff_localCompletion_regular
    {R : Type u} [CommRing R] [IsNoetherianRing R] [IsLocalRing R] :
    IsGRing R ↔
      IsRegularRingMap
        (algebraMap R (ringCompletion (IsLocalRing.maximalIdeal R))) := by
  sorry

/-- Henselizations and strict henselizations of G-rings are G-rings. -/
theorem henselization_and_strictHenselization_isGRing
    {R K : Type u} [CommRing R] [IsLocalRing R]
    [Field K] [Algebra (IsLocalRing.ResidueField R) K]
    (D : StrictHenselizationData R K) (hR : IsGRing R) :
    IsGRing D.henselization ∧ IsGRing D.strictHenselization := by
  exact isGRing_henselization_and_strictHenselization D hR

/-- Fields, complete local rings, `ℤ`, characteristic-zero Dedekind domains,
and their finite-type extensions supply the standard G-rings in the source. -/
theorem source_gRing_ubiquity :
    (∀ (K : Type u) [Field K], IsGRing K) ∧
    (∀ (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
      [IsAdicComplete (IsLocalRing.maximalIdeal A) A], IsGRing A) ∧
    IsGRing ℤ ∧
    (∀ (R : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R]
      [IsDedekindDomain R] [CharZero (FractionRing R)], IsGRing R) ∧
    (∀ (R S : Type u) [CommRing R] [CommRing S] (f : R →+* S),
      IsGRing R → RingHom.FiniteType f → IsGRing S) := by
  exact isGRing_ubiquity

/-- G-rings ascend along essentially finite type ring maps. -/
theorem gRing_of_essentiallyFiniteType
    {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) (hR : IsGRing R)
    (hfinite : RingHom.EssFiniteType f) : IsGRing S := by
  exact isGRing_of_essentiallyFiniteType f hR hfinite

/-- The four essentially-finite-type G-ring examples listed in the source. -/
theorem source_essentiallyFiniteType_gRing_examples :
    (∀ (k S : Type u) [Field k] [CommRing S] (f : k →+* S),
      RingHom.EssFiniteType f → IsGRing S) ∧
    (∀ (A S : Type u) [CommRing A] [IsNoetherianRing A]
      [IsLocalRing A] [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
      [CommRing S] (f : A →+* S),
      RingHom.EssFiniteType f → IsGRing S) ∧
    (∀ (S : Type u) [CommRing S] (f : ℤ →+* S),
      RingHom.EssFiniteType f → IsGRing S) ∧
    (∀ (R S : Type u) [CommRing R] [IsDomain R]
      [IsNoetherianRing R] [IsDedekindDomain R]
      [CharZero (FractionRing R)] [CommRing S] (f : R →+* S),
      RingHom.EssFiniteType f → IsGRing S) := by
  sorry

/-! ## Approximation in a henselian G-ring -/

/- The source's `R^∧` and `m^N R^∧` are written using the canonical local
   completion and the ideal map into it. -/
/-- Artin approximation with a prescribed completion-order of accuracy for a
finite polynomial system over a henselian G-ring. -/
theorem approximation_property_for_gRing
    {R : Type u} [CommRing R] [IsNoetherianRing R]
    [HenselianLocalRing R]
    {n m : ℕ} (F : Fin m → MvPolynomial (Fin n) R)
    (a : Fin n → ringCompletion (IsLocalRing.maximalIdeal R))
    (ha : SolvesPolynomialSystem
      (algebraMap R (ringCompletion (IsLocalRing.maximalIdeal R))) F a)
    (hR : IsGRing R) :
    ∀ N : ℕ, ∃ b : Fin n → R,
      SolvesPolynomialSystem (RingHom.id R) F b ∧
        ∀ i, a i - algebraMap R
          (ringCompletion (IsLocalRing.maximalIdeal R)) (b i) ∈
          Ideal.map (algebraMap R
            (ringCompletion (IsLocalRing.maximalIdeal R)))
            ((IsLocalRing.maximalIdeal R) ^ N) := by
  sorry

/- The étale variant needs a map from the étale ring into the completion in
   order for `aᵢ - bᵢ` to be a well-typed expression. -/
/-- An étale solution over a point with trivial residue-field extension,
together with its comparison map into the original completion. -/
structure EtaleCompletionApproximation
    {R : Type u} [CommRing R] [IsLocalRing R]
    {n m : ℕ} (F : Fin m → MvPolynomial (Fin n) R)
    (a : Fin n → ringCompletion (IsLocalRing.maximalIdeal R))
    (N : ℕ) where
  carrier : Type u
  [commRingCarrier : CommRing carrier]
  map : R →+* carrier
  point : MaximalSpectrum carrier
  toCompletion : carrier →+*
    ringCompletion (IsLocalRing.maximalIdeal R)
  etale : RingHom.Etale map
  point_over : point.asIdeal.comap map = IsLocalRing.maximalIdeal R
  residue_equiv :
    Nonempty (IsLocalRing.ResidueField R ≃+* point.asIdeal.ResidueField)
  completion_over :
    toCompletion.comp map = algebraMap R
      (ringCompletion (IsLocalRing.maximalIdeal R))
  solution : Fin n → carrier
  solves : SolvesPolynomialSystem map F solution
  approximation : ∀ i,
    a i - toCompletion (solution i) ∈
      Ideal.map toCompletion (point.asIdeal ^ N)

instance EtaleCompletionApproximation.carrierCommRing
    {R : Type u} [CommRing R] [IsLocalRing R]
    {n m : ℕ} {F : Fin m → MvPolynomial (Fin n) R}
    {a : Fin n → ringCompletion (IsLocalRing.maximalIdeal R)} {N : ℕ}
    (W : EtaleCompletionApproximation F a N) : CommRing W.carrier :=
  W.commRingCarrier

/-- Approximation over an étale extension with a maximal point over the
original maximal ideal and unchanged residue field. -/
theorem approximation_property_etale_variant
    {R : Type u} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    {n m : ℕ} (F : Fin m → MvPolynomial (Fin n) R)
    (a : Fin n → ringCompletion (IsLocalRing.maximalIdeal R))
    (ha : SolvesPolynomialSystem
      (algebraMap R (ringCompletion (IsLocalRing.maximalIdeal R))) F a)
    (hR : IsGRing R) :
    ∀ N : ℕ, Nonempty (EtaleCompletionApproximation F a N) := by
  sorry

/-! ## The étale stages inside the henselization -/

/- This structure makes the displayed chain
   `R ⊆ R_{m'} ⊆ Rʰ ⊆ R^∧` precise as compatible ring maps and injective
   embeddings. -/
/-- Compatible maps witnessing the étale-localization-henselization-
completion chain attached to a point over a local ring. -/
structure EtaleHenselizationChain
    {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (D : HenselizationData R)
    (M : HenselizationCompletionMap R D)
    {A : Type u} [CommRing A]
    (f : R →+* A) (q : MaximalSpectrum A) where
  etale : RingHom.Etale f
  point_over : q.asIdeal.comap f = IsLocalRing.maximalIdeal R
  residue_equiv :
    Nonempty (IsLocalRing.ResidueField R ≃+* q.asIdeal.ResidueField)
  injective_map : Function.Injective f
  injective_localization : Function.Injective
    (algebraMap A (Localization.AtPrime q.asIdeal))
  toHenselization : A →+* D.carrier
  toHenselization_over : toHenselization.comp f = D.map
  localizationMap : Localization.AtPrime q.asIdeal →+* D.carrier
  localizationMap_comp : localizationMap.comp
      (algebraMap A (Localization.AtPrime q.asIdeal)) = toHenselization
  completionMap : D.carrier →+*
    ringCompletion (IsLocalRing.maximalIdeal R)
  completionMap_eq : completionMap = M.toRingHom
  injective_toHenselization : Function.Injective toHenselization
  injective_localizationMap : Function.Injective localizationMap
  injective_completionMap : Function.Injective completionMap

/-- An étale point over the closed point occurs in the henselization, giving
the displayed inclusion chain into the completion. -/
theorem exists_etale_henselization_chain
    {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (D : HenselizationData R)
    (M : HenselizationCompletionMap R D)
    {A : Type u} [CommRing A] (f : R →+* A)
    (q : MaximalSpectrum A)
    (hf : RingHom.Etale f)
    (hq : q.asIdeal.comap f = IsLocalRing.maximalIdeal R)
    (hres : Nonempty
      (IsLocalRing.ResidueField R ≃+* q.asIdeal.ResidueField)) :
    Nonempty (EtaleHenselizationChain D M f q) := by
  sorry

/-! ## The henselization example -/

/-- The completion of a Noetherian local ring and the completion of its
henselization are canonically isomorphic. -/
theorem henselization_completion_isomorphism
    {R K : Type u} [CommRing R] [IsLocalRing R]
    [Field K] [Algebra (IsLocalRing.ResidueField R) K]
    (D : StrictHenselizationData R K) [IsNoetherianRing R] :
    ∃ e : ringCompletion (IsLocalRing.maximalIdeal R) ≃+*
        ringCompletion (IsLocalRing.maximalIdeal D.henselization),
      e.toRingHom.comp (algebraMap R
        (ringCompletion (IsLocalRing.maximalIdeal R))) =
        (algebraMap D.henselization
          (ringCompletion (IsLocalRing.maximalIdeal D.henselization))).comp
          D.henselizationMap := by
  exact henselization_completion_equiv D

/-- The henselization-to-completion map is injective in the Noetherian local
case, so the henselization may be regarded as a subring of its completion. -/
theorem henselization_completion_map_injective
    {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (D : HenselizationData R)
    (M : HenselizationCompletionMap R D) :
    Function.Injective M.toRingHom := by
  sorry

/-- Every element of the henselization of a Noetherian local domain satisfies
a nonzero polynomial over the original domain. -/
theorem henselization_elements_satisfy_nonzero_polynomial
    {R : Type u} [CommRing R] [IsLocalRing R] [IsDomain R]
    [IsNoetherianRing R] (D : HenselizationData R) :
    ∀ y : D.carrier, SatisfiesNonzeroPolynomial D.map y := by
  sorry

/-- A root in the completion of a polynomial with nonzero leading coefficient
can be approximated by roots in the henselization at every positive order. -/
theorem algebraic_completion_element_approximation
    {R : Type u} [CommRing R] [IsLocalRing R] [IsDomain R]
    [IsNoetherianRing R] (D : HenselizationData R)
    (M : HenselizationCompletionMap R D) (hR : IsGRing R)
    (x : ringCompletion (IsLocalRing.maximalIdeal R))
    (P : Polynomial R) (hP : P ≠ 0)
    (hx : Polynomial.eval₂ (algebraMap R
      (ringCompletion (IsLocalRing.maximalIdeal R))) x P = 0) :
    ∀ N : ℕ, 0 < N → ∃ y : D.carrier,
      Polynomial.eval₂ D.map y P = 0 ∧
        x - M.toRingHom y ∈
          Ideal.map (algebraMap R
            (ringCompletion (IsLocalRing.maximalIdeal R)))
            ((IsLocalRing.maximalIdeal R) ^ N) := by
  sorry

/-- The henselization inside the completion is exactly the set of elements
satisfying a nonzero polynomial over the base domain. -/
theorem henselization_image_eq_algebraic_completion_elements
    {R : Type u} [CommRing R] [IsLocalRing R] [IsDomain R]
    [IsNoetherianRing R] (D : HenselizationData R)
    (M : HenselizationCompletionMap R D) (hR : IsGRing R) :
    ∀ x : ringCompletion (IsLocalRing.maximalIdeal R),
      (∃ y : D.carrier, M.toRingHom y = x) ↔
        SatisfiesNonzeroPolynomial
          (algebraMap R (ringCompletion (IsLocalRing.maximalIdeal R))) x := by
  sorry

/-! ## Localization at a prime -/

/-- The completion used after localizing a ring at a prime. -/
noncomputable abbrev localizedCompletion
    (A : Type u) [CommRing A] (p : PrimeSpectrum A) : Type u :=
  ringCompletion
    (IsLocalRing.maximalIdeal (Localization.AtPrime p.asIdeal))

/-- The canonical map from a ring to the completion of its localization at a
prime. -/
noncomputable def localizedCompletionMap
    (A : Type u) [CommRing A] (p : PrimeSpectrum A) :
    A →+* localizedCompletion A p :=
  (algebraMap (Localization.AtPrime p.asIdeal)
    (localizedCompletion A p)).comp
    (algebraMap A (Localization.AtPrime p.asIdeal))

/-- An étale solution after localizing at a prime, including the comparison
map from the original localized completion. -/
structure LocalizedEtaleApproximation
    {R : Type u} [CommRing R]
    (p : PrimeSpectrum R)
    {n m : ℕ} (F : Fin m → MvPolynomial (Fin n) R)
    (a : Fin n → ringCompletion
      (IsLocalRing.maximalIdeal (Localization.AtPrime p.asIdeal)))
    (N : ℕ) where
  carrier : Type u
  [commRingCarrier : CommRing carrier]
  map : R →+* carrier
  point : PrimeSpectrum carrier
  etale : RingHom.Etale map
  point_over : point.asIdeal.comap map = p.asIdeal
  residue_equiv :
    Nonempty (p.asIdeal.ResidueField ≃+* point.asIdeal.ResidueField)
  localizedMap : Localization.AtPrime p.asIdeal →+*
    Localization.AtPrime point.asIdeal
  localizedMap_over : localizedMap.comp
      (algebraMap R (Localization.AtPrime p.asIdeal)) =
      (algebraMap carrier (Localization.AtPrime point.asIdeal)).comp map
  completionMap : ringCompletion
      (IsLocalRing.maximalIdeal (Localization.AtPrime p.asIdeal)) →+*
      localizedCompletion carrier point
  completionMap_comp : completionMap.comp
      (algebraMap (Localization.AtPrime p.asIdeal)
        (ringCompletion
          (IsLocalRing.maximalIdeal (Localization.AtPrime p.asIdeal)))) =
      (algebraMap (Localization.AtPrime point.asIdeal)
        (localizedCompletion carrier point)).comp localizedMap
  solution : Fin n → carrier
  solves : SolvesPolynomialSystem map F solution
  approximation : ∀ i,
    completionMap (a i) - localizedCompletionMap carrier point (solution i) ∈
      Ideal.map (localizedCompletionMap carrier point) (point.asIdeal ^ N)

instance LocalizedEtaleApproximation.carrierCommRing
    {R : Type u} [CommRing R] {p : PrimeSpectrum R}
    {n m : ℕ} {F : Fin m → MvPolynomial (Fin n) R}
    {a : Fin n → ringCompletion
      (IsLocalRing.maximalIdeal (Localization.AtPrime p.asIdeal))} {N : ℕ}
    (W : LocalizedEtaleApproximation p F a N) : CommRing W.carrier :=
  W.commRingCarrier

/-- The localized approximation property for a G-ring. -/
theorem approximation_property_localized
    {R : Type u} [CommRing R] [IsNoetherianRing R]
    (p : PrimeSpectrum R)
    {n m : ℕ} (F : Fin m → MvPolynomial (Fin n) R)
    (a : Fin n → ringCompletion
      (IsLocalRing.maximalIdeal (Localization.AtPrime p.asIdeal)))
    (ha : SolvesPolynomialSystem
      (algebraMap (Localization.AtPrime p.asIdeal)
        (ringCompletion
          (IsLocalRing.maximalIdeal (Localization.AtPrime p.asIdeal))))
      (fun i => (F i).map (algebraMap R (Localization.AtPrime p.asIdeal))) a)
    (hR : IsGRing (Localization.AtPrime p.asIdeal)) :
    ∀ N : ℕ, Nonempty (LocalizedEtaleApproximation p F a N) := by
  sorry

end

end Formalization.Books.Smoothing.Unit13
