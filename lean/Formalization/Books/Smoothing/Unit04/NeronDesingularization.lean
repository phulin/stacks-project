import Formalization.Books.Smoothing.Unit03
import Formalization.Books.Algebra.Unit70.BlowUpAlgebras
import Formalization.Books.Algebra.Unit127.ColimitsAndFinitePresentation
import Formalization.Books.MoreAlgebra.Unit112
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Localization.AtPrime.Basic

/-!
# Smoothing Ring Maps, Chapter 4: Néron desingularization

This file records the situation, affine blowup chart, functoriality, smooth
blowup calculation, defect-decreasing argument, and filtered-colimit
conclusion from the Néron desingularization intermezzo.  The affine chart and
its power-torsion quotient use the canonical constructions from Algebra,
Chapter 70; the remaining source proofs are theorem interfaces for the
proving stage.
-/

namespace Formalization.Books.Smoothing.Unit04

open Set
open Formalization.Books.Algebra.Unit127
open Formalization.Books.Algebra.Unit131
open Formalization.Books.Algebra.Unit137
open Formalization.Books.MoreAlgebra.Unit112
open Formalization.Books.Algebra.Unit70
open scoped BigOperators TensorProduct

noncomputable section

universe u v

/-! ## The Néron situation -/

/- A uniformizer is expressed by the canonical maximal ideal of a DVR.  This
is the ring-theoretic formulation needed by the affine chart and avoids
introducing a second valuation object. -/
def IsUniformizer (R : Type u) [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] (π : R) : Prop :=
  Ideal.span ({π} : Set R) = IsLocalRing.maximalIdeal R

/-- The factorization and finiteness data in Situation 4. -/
structure NeronSituation
    (R A Λ : Type u) [CommRing R] [CommRing A] [CommRing Λ]
    [IsDomain R] [IsDomain Λ]
    [IsDiscreteValuationRing R] [IsDiscreteValuationRing Λ]
    [Algebra R A] [Algebra R Λ] where
  extension : DVRMap R Λ
  extension_eq_algebraMap : extension.hom = algebraMap R Λ
  weaklyUnramified : WeaklyUnramified extension
  mapToLambda : A →+* Λ
  factorization : mapToLambda.comp (algebraMap R A) = algebraMap R Λ
  flat : RingHom.Flat (algebraMap R A)
  finiteType : RingHom.FiniteType (algebraMap R A)

/-- The kernel prime and the prime above the maximal ideal in the situation. -/
def NeronSituation.q
    {R A Λ : Type u} [CommRing R] [CommRing A] [CommRing Λ]
    [IsDomain R] [IsDomain Λ]
    [IsDiscreteValuationRing R] [IsDiscreteValuationRing Λ]
    [Algebra R A] [Algebra R Λ]
    (S : NeronSituation R A Λ) : Ideal A :=
  RingHom.ker S.mapToLambda

def NeronSituation.p
    {R A Λ : Type u} [CommRing R] [CommRing A] [CommRing Λ]
    [IsDomain R] [IsDomain Λ]
    [IsDiscreteValuationRing R] [IsDiscreteValuationRing Λ]
    [Algebra R A] [Algebra R Λ]
    (S : NeronSituation R A Λ) : Ideal A :=
  (IsLocalRing.maximalIdeal Λ).comap S.mapToLambda

/-- The canonical affine Néron blowup chart `A[p/π]`. -/
abbrev neronBlowupAlgebra
    {R A Λ : Type u} [CommRing R] [CommRing A] [CommRing Λ]
    [IsDomain R] [IsDomain Λ]
    [IsDiscreteValuationRing R] [IsDiscreteValuationRing Λ]
    [Algebra R A] [Algebra R Λ]
    (S : NeronSituation R A Λ) (π : R) : Type u :=
  affineBlowup S.p (algebraMap R A π)

/-- The induced map from the affine Néron chart to `Λ`, including its
factorization through `A` and the defining fraction formula. -/
structure NeronBlowupData
    {R A Λ : Type u} [CommRing R] [CommRing A] [CommRing Λ]
    [IsDomain R] [IsDomain Λ]
    [IsDiscreteValuationRing R] [IsDiscreteValuationRing Λ]
    [Algebra R A] [Algebra R Λ]
    (S : NeronSituation R A Λ) (π : R) where
  denominator_mem : algebraMap R A π ∈ S.p
  mapToLambda : neronBlowupAlgebra S π →+* Λ
  map_comp : mapToLambda.comp (algebraMap A (neronBlowupAlgebra S π)) =
    S.mapToLambda
  pPrime : PrimeSpectrum (neronBlowupAlgebra S π)
  pPrime_asIdeal : pPrime.asIdeal =
    (IsLocalRing.maximalIdeal Λ).comap mapToLambda
  qPrime : PrimeSpectrum (neronBlowupAlgebra S π)
  qPrime_asIdeal : qPrime.asIdeal = RingHom.ker mapToLambda
  map_generator : ∀ (x : A) (hx : x ∈ S.p),
    mapToLambda (affineBlowupGenerator S.p (algebraMap R A π) ⟨x, hx⟩) *
        S.mapToLambda (algebraMap R A π) = S.mapToLambda x

def NeronBlowupData.q'
    {R A Λ : Type u} [CommRing R] [CommRing A] [CommRing Λ]
    [IsDomain R] [IsDomain Λ]
    [IsDiscreteValuationRing R] [IsDiscreteValuationRing Λ]
    [Algebra R A] [Algebra R Λ]
    {S : NeronSituation R A Λ} {π : R} (D : NeronBlowupData S π) :
    Ideal (neronBlowupAlgebra S π) :=
  RingHom.ker D.mapToLambda

def NeronBlowupData.p'
    {R A Λ : Type u} [CommRing R] [CommRing A] [CommRing Λ]
    [IsDomain R] [IsDomain Λ]
    [IsDiscreteValuationRing R] [IsDiscreteValuationRing Λ]
    [Algebra R A] [Algebra R Λ]
    {S : NeronSituation R A Λ} {π : R} (D : NeronBlowupData S π) :
    Ideal (neronBlowupAlgebra S π) :=
  (IsLocalRing.maximalIdeal Λ).comap D.mapToLambda

/-- The affine blowup is regular in the selected denominator. -/
theorem neronBlowup_denominator_isRegular
    {R A Λ : Type u} [CommRing R] [CommRing A] [CommRing Λ]
    [IsDomain R] [IsDomain Λ]
    [IsDiscreteValuationRing R] [IsDiscreteValuationRing Λ]
    [Algebra R A] [Algebra R Λ]
    (S : NeronSituation R A Λ) (π : R) (hπ : algebraMap R A π ∈ S.p) :
    IsRegular (algebraMap R (neronBlowupAlgebra S π) π) := by
  exact affineBlowup_isRegular S.p hπ

/-- Flatness over the DVR makes a uniformizer a nonzerodivisor on the
algebra. -/
theorem flat_map_uniformizer_isRegular
    {R A Λ : Type u} [CommRing R] [CommRing A] [CommRing Λ]
    [IsDomain R] [IsDomain Λ]
    [IsDiscreteValuationRing R] [IsDiscreteValuationRing Λ]
    [Algebra R A] [Algebra R Λ]
    (S : NeronSituation R A Λ) {π : R} (hπ : IsUniformizer R π) :
    IsRegular (algebraMap R A π) := by
  sorry

/-- A uniformizer of `R` maps to a uniformizer of `Λ` in the weakly
unramified extension. -/
theorem map_uniformizer_isUniformizer
    {R Λ : Type u} [CommRing R] [CommRing Λ]
    [IsDomain R] [IsDomain Λ]
    [IsDiscreteValuationRing R] [IsDiscreteValuationRing Λ]
    (E : DVRMap R Λ) (hE : WeaklyUnramified E)
    {π : R} (hπ : IsUniformizer R π) :
    IsUniformizer Λ (E.hom π) := by
  sorry

/-- The affine chart carries the induced map to `Λ` whenever the denominator
belongs to the prime pulled back from `Λ`. -/
theorem exists_neronBlowupData
    {R A Λ : Type u} [CommRing R] [CommRing A] [CommRing Λ]
    [IsDomain R] [IsDomain Λ]
    [IsDiscreteValuationRing R] [IsDiscreteValuationRing Λ]
    [Algebra R A] [Algebra R Λ]
    (S : NeronSituation R A Λ) (π : R)
    (hπ : algebraMap R A π ∈ S.p) :
    Nonempty (NeronBlowupData S π) := by
  sorry

/-- The isomorphism class of the chart is independent of the chosen
uniformizer; the two chart maps are compared over `A`. -/
theorem neronBlowup_independent_of_uniformizer
    {R A Λ : Type u} [CommRing R] [CommRing A] [CommRing Λ]
    [IsDomain R] [IsDomain Λ]
    [IsDiscreteValuationRing R] [IsDiscreteValuationRing Λ]
    [Algebra R A] [Algebra R Λ]
    (S : NeronSituation R A Λ) {π π' : R}
    (hπ : algebraMap R A π ∈ S.p) (hπ' : algebraMap R A π' ∈ S.p)
    (hπu : IsUniformizer R π) (hπ'u : IsUniformizer R π') :
    Nonempty (neronBlowupAlgebra S π ≃ₐ[A] neronBlowupAlgebra S π') := by
  sorry

/-! ## Functoriality -/

/-- The localization form of functoriality for an element outside the
center. -/
theorem neronBlowup_localization_baseChange
    {R A Λ : Type u} [CommRing R] [CommRing A] [CommRing Λ]
    [IsDomain R] [IsDomain Λ]
    [IsDiscreteValuationRing R] [IsDiscreteValuationRing Λ]
    [Algebra R A] [Algebra R Λ]
    (S : NeronSituation R A Λ) (π : R)
    (hπ : algebraMap R A π ∈ S.p) (a : A) (ha : a ∉ S.p) :
    Nonempty (Localization.Away
        (algebraMap A (neronBlowupAlgebra S π) a) ≃+*
      affineBlowup (Ideal.map (algebraMap A (Localization.Away a)) S.p)
        (algebraMap A (Localization.Away a) (algebraMap R A π))) := by
  sorry

/-- The quotient form of functoriality for a surjective presentation. -/
structure NeronBlowupQuotientData
    {R A B Λ : Type u} [CommRing R] [CommRing A] [CommRing B] [CommRing Λ]
    [IsDomain R] [IsDomain Λ]
    [IsDiscreteValuationRing R] [IsDiscreteValuationRing Λ]
    [Algebra R A] [Algebra R B] [Algebra R Λ]
    (S : NeronSituation R A Λ) (g : B →+* A) (pB : Ideal B)
    (hmap : Ideal.map g pB = S.p) (π : R) where
  denominator_mem : algebraMap R B π ∈ pB
  quotientIso :
    let B' := affineBlowup pB (algebraMap R B π)
    let Q := B' ⧸ Ideal.map (algebraMap B B') (RingHom.ker g)
    Q ⧸ powerTorsionIdeal Q
        (algebraMap B' Q (algebraMap R B' π)) ≃+*
      neronBlowupAlgebra S π

theorem exists_neronBlowup_quotientData
    {R A B Λ : Type u} [CommRing R] [CommRing A] [CommRing B] [CommRing Λ]
    [IsDomain R] [IsDomain Λ]
    [IsDiscreteValuationRing R] [IsDiscreteValuationRing Λ]
    [Algebra R A] [Algebra R B] [Algebra R Λ]
    (S : NeronSituation R A Λ) (g : B →+* A) (hg : Function.Surjective g)
    (hflatB : RingHom.Flat (algebraMap R B))
    (hfiniteB : RingHom.FiniteType (algebraMap R B))
    (pB : Ideal B) (hmap : Ideal.map g pB = S.p) (π : R)
    (hπ : algebraMap R B π ∈ pB) :
    Nonempty (NeronBlowupQuotientData S g pB hmap π) := by
  sorry

theorem neronBlowup_functorial
    {R A B Λ : Type u} [CommRing R] [CommRing A] [CommRing B] [CommRing Λ]
    [IsDomain R] [IsDomain Λ]
    [IsDiscreteValuationRing R] [IsDiscreteValuationRing Λ]
    [Algebra R A] [Algebra R B] [Algebra R Λ]
    (S : NeronSituation R A Λ) (g : B →+* A) (hg : Function.Surjective g)
    (hflatB : RingHom.Flat (algebraMap R B))
    (hfiniteB : RingHom.FiniteType (algebraMap R B))
    (pB : Ideal B) (hmap : Ideal.map g pB = S.p) (π : R)
    (hπ : algebraMap R B π ∈ pB) (a : A) (ha : a ∉ S.p) :
    Nonempty (NeronBlowupQuotientData S g pB hmap π) ∧
      (Nonempty (Localization.Away
          (algebraMap A (neronBlowupAlgebra S π) a) ≃+*
        affineBlowup (Ideal.map (algebraMap A (Localization.Away a)) S.p)
          (algebraMap A (Localization.Away a) (algebraMap R A π)))) := by
  sorry

/-! ## Smoothness of one blowup -/

/-- A short exact sequence of modules, retaining the zero, injective, exact,
and surjective assertions in the displayed source sequence. -/
structure ShortExactSequence
    {M N P : Type u} [AddCommMonoid M] [AddCommMonoid N]
    [AddCommMonoid P] where
  left : M →+ N
  right : N →+ P
  left_injective : Function.Injective left
  exact : Function.Exact left right
  right_surjective : Function.Surjective right

abbrev neronLocalizedRing
    {R A Λ : Type u} [CommRing R] [CommRing A] [CommRing Λ]
    [IsDomain R] [IsDomain Λ]
    [IsDiscreteValuationRing R] [IsDiscreteValuationRing Λ]
    [Algebra R A] [Algebra R Λ]
    {S : NeronSituation R A Λ} {π : R}
    (D : NeronBlowupData S π) : Type u :=
  Localization.AtPrime D.pPrime.asIdeal

/-- The localized quotient used for the `(A'/πA')_{p'}` term. -/
abbrev neronPiQuotient
    {R A Λ : Type u} [CommRing R] [CommRing A] [CommRing Λ]
    [IsDomain R] [IsDomain Λ]
    [IsDiscreteValuationRing R] [IsDiscreteValuationRing Λ]
    [Algebra R A] [Algebra R Λ]
    {S : NeronSituation R A Λ} {π : R}
    (D : NeronBlowupData S π) : Type u :=
  neronBlowupAlgebra S π ⧸
    Ideal.span ({algebraMap R (neronBlowupAlgebra S π) π} :
      Set (neronBlowupAlgebra S π))

abbrev neronPiLocalizedRing
    {R A Λ : Type u} [CommRing R] [CommRing A] [CommRing Λ]
    [IsDomain R] [IsDomain Λ]
    [IsDiscreteValuationRing R] [IsDiscreteValuationRing Λ]
    [Algebra R A] [Algebra R Λ]
    {S : NeronSituation R A Λ} {π : R}
    (D : NeronBlowupData S π)
    (qbar : PrimeSpectrum (neronPiQuotient D)) : Type u :=
  Localization.AtPrime qbar.asIdeal

structure NeronBlowupDifferentialSequence
    {R A Λ : Type u} [CommRing R] [CommRing A] [CommRing Λ]
    [IsDomain R] [IsDomain Λ]
    [IsDiscreteValuationRing R] [IsDiscreteValuationRing Λ]
    [Algebra R A] [Algebra R Λ]
    {S : NeronSituation R A Λ} {π : R}
    (D : NeronBlowupData S π) (c : ℕ) where
  quotientPrime : PrimeSpectrum (neronPiQuotient D)
  quotientPrime_comap :
    (Ideal.comap (Ideal.Quotient.mk _) quotientPrime.asIdeal) = D.p'
  sequence : ShortExactSequence
    (M := TensorProduct A (ModuleOfDifferentials R A) (neronLocalizedRing D))
    (N := TensorProduct (neronBlowupAlgebra S π)
      (ModuleOfDifferentials R (neronBlowupAlgebra S π)) (neronLocalizedRing D))
    (P := Fin c → neronLocalizedRing D)

/-- If the original map is smooth at the center and the residue extension is
separable, the Néron chart is smooth at the induced center and has the
displayed short exact differential sequence. -/
theorem neronBlowup_smooth
    {R A Λ : Type u} [CommRing R] [CommRing A] [CommRing Λ]
    [IsDomain R] [IsDomain Λ]
    [IsDiscreteValuationRing R] [IsDiscreteValuationRing Λ]
    [Algebra R A] [Algebra R Λ]
    (S : NeronSituation R A Λ) (π : R)
    (hπ : algebraMap R A π ∈ S.p)
    (D : NeronBlowupData S π)
    (hq : IsSmoothAt R A ⟨S.p, by sorry⟩)
    (hres : letI := residueFieldAlgebra S.extension
      Algebra.IsSeparable (DVRResidueField R) (DVRResidueField Λ)) :
      IsSmoothAt R (neronBlowupAlgebra S π) D.pPrime ∧
      ∃ c : ℕ, Nonempty (NeronBlowupDifferentialSequence D c) := by
  sorry

/-! ## The smoothness criterion and the defect calculation -/

/-- The source's ``when smooth'' criterion: freeness of the cokernel after
the map to `Λ` forces smoothness at the chosen prime. -/
def IsFreeCokernel
    {R M N : Type u} [CommRing R] [AddCommGroup M] [AddCommGroup N]
    [Module R M] [Module R N] (d : M →ₗ[R] N) : Prop :=
  Module.Free R (N ⧸ LinearMap.range d)

theorem neron_when_smooth
    {R A B Λ : Type u} [CommRing R] [CommRing A] [CommRing B] [CommRing Λ]
    [IsDomain R] [IsDomain Λ]
    [IsDiscreteValuationRing R] [IsDiscreteValuationRing Λ]
    [Algebra R A] [Algebra R B] [Algebra R Λ]
    (S : NeronSituation R A Λ) (g : B →+* A) (hg : Function.Surjective g)
    (I : Ideal B) (hI : I = RingHom.ker g)
    (pB : PrimeSpectrum B) (hpB : pB.asIdeal = S.p.comap g)
    (hB : IsSmoothAt R B pB)
    (hAq : IsSmoothAt R A ⟨S.q, by sorry⟩)
    {M N : Type u} [AddCommGroup M] [AddCommGroup N]
    [Module Λ M] [Module Λ N] (d : M →ₗ[Λ] N)
    (hfree : IsFreeCokernel (R := Λ) d) :
    IsSmoothAt R A ⟨S.p, by sorry⟩ := by
  sorry

/-- One blowup does not increase the defect, and it decreases it strictly when
the original algebra is not smooth at the closed center. -/
def NeronDefectChange (e e' : ℕ) : Prop := e' < e

theorem neron_defect_decreases
    {R A Λ : Type u} [CommRing R] [CommRing A] [CommRing Λ]
    [IsDomain R] [IsDomain Λ]
    [IsDiscreteValuationRing R] [IsDiscreteValuationRing Λ]
    [Algebra R A] [Algebra R Λ]
    (S : NeronSituation R A Λ) (π : R)
    (hπ : algebraMap R A π ∈ S.p)
    (D : NeronBlowupData S π)
    (hres : letI := residueFieldAlgebra S.extension
      Algebra.IsSeparable (DVRResidueField R) (DVRResidueField Λ))
    (hnot : ¬ IsSmoothAt R A ⟨S.p, by sorry⟩) :
    ∃ e e' : ℕ, NeronDefectChange e e' := by
  sorry

/-! ## Néron desingularization -/

/-- A finite sequence of affine Néron blowups, with its terminal map to the
original DVR and its terminal smoothness assertion. -/
structure NeronBlowupIteration
    {R A Λ : Type u} [CommRing R] [CommRing A] [CommRing Λ]
    [IsDomain R] [IsDomain Λ]
    [IsDiscreteValuationRing R] [IsDiscreteValuationRing Λ]
    [Algebra R A] [Algebra R Λ]
    (S : NeronSituation R A Λ) (π : R) where
  length : ℕ
  terminal : Type u
  [terminalCommRing : CommRing terminal]
  [terminalAlgebra : Algebra R terminal]
  terminalMap : terminal →+* Λ
  factorization : terminalMap.comp (algebraMap R terminal) = algebraMap R Λ
  isFiniteSequenceOfAffineNeronBlowups : Prop
  terminalPrime : PrimeSpectrum terminal
  terminalSmooth : IsSmoothAt R terminal terminalPrime

theorem neron_desingularization
    {R A Λ : Type u} [CommRing R] [CommRing A] [CommRing Λ]
    [IsDomain R] [IsDomain Λ]
    [IsDiscreteValuationRing R] [IsDiscreteValuationRing Λ]
    [Algebra R A] [Algebra R Λ]
    (S : NeronSituation R A Λ) (π : R) (hπ : IsUniformizer R π)
    (hq : IsSmoothAt R A ⟨S.q, by sorry⟩)
    (hres : letI := residueFieldAlgebra S.extension
      Algebra.IsSeparable (DVRResidueField R) (DVRResidueField Λ)) :
    Nonempty (NeronBlowupIteration S π) := by
  sorry

/-! ## The filtered-colimit conclusion -/

/-- The regularity condition for a DVR extension, expressed through the
canonical formal-smoothness criterion and separability on fraction fields. -/
def IsRegularDVRExtension
    {R Λ K L : Type u} [CommRing R] [CommRing Λ] [Field K] [Field L]
    [IsDomain R] [IsDomain Λ]
    [IsDiscreteValuationRing R] [IsDiscreteValuationRing Λ]
    [Algebra R K] [Algebra R L] [Algebra Λ L] [Algebra K L]
    (E : DVRMap R Λ) (_F : FractionFieldExtension (K := K) (L := L) E) : Prop :=
  RingHom.FormallySmooth E.hom ∧ Algebra.IsSeparable K L

/-- For DVR extensions, regularity is equivalent to ramification index one,
separability of the residue extension, and separability of the fraction-field
extension. -/
theorem dvr_extension_regular_iff
    {R Λ K L : Type u} [CommRing R] [CommRing Λ] [Field K] [Field L]
    [IsDomain R] [IsDomain Λ]
    [IsDiscreteValuationRing R] [IsDiscreteValuationRing Λ]
    [Algebra R K] [Algebra R L] [Algebra Λ L] [Algebra K L]
    (E : DVRMap R Λ) (F : FractionFieldExtension (K := K) (L := L) E) :
    IsRegularDVRExtension E F ↔
      WeaklyUnramified E ∧
        (letI := residueFieldAlgebra E;
          Algebra.IsSeparable (DVRResidueField R) (DVRResidueField Λ) ∧
            Algebra.IsSeparable K L) := by
  sorry

/-- A ring map is an ind-smooth map when it is a filtered colimit of smooth
finite-type stages, expressed with the canonical under-category colimit data.
-/
def IsFilteredColimitOfSmoothAlgebras
    {R A : Type u} [CommRing R] [CommRing A] (f : R →+* A) : Prop :=
  Nonempty (FilteredAlgebraColimitIn f
    {X | RingHom.Smooth X.hom.hom})

/-- Unramified extensions of DVRs are filtered colimits of smooth algebras. -/
theorem neron_colimit
    {R Λ K L : Type u} [CommRing R] [CommRing Λ] [Field K] [Field L]
    [IsDomain R] [IsDomain Λ]
    [IsDiscreteValuationRing R] [IsDiscreteValuationRing Λ]
    [Algebra R Λ] [Algebra R K] [Algebra R L] [Algebra Λ L] [Algebra K L]
    (E : DVRMap R Λ) (F : FractionFieldExtension (K := K) (L := L) E)
    (hweak : WeaklyUnramified E)
    (hres : letI := residueFieldAlgebra E
      Algebra.IsSeparable (DVRResidueField R) (DVRResidueField Λ))
    (hfrac : Algebra.IsSeparable K L) :
    IsFilteredColimitOfSmoothAlgebras (algebraMap R Λ) := by
  sorry

end
end Formalization.Books.Smoothing.Unit04
