import Formalization.Books.Algebra.Unit37.NormalRings
import Formalization.Books.Algebra.Unit97.CompletionForNoetherianRings
import Formalization.Books.Algebra.Unit104.CohenMacaulayRings
import Formalization.Books.Algebra.Unit162.NagataRings
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.RegularLocalRing.Defs

/-!
# More on Algebra, Chapter 43: Permanence of properties under completion

The local completion is Mathlib's `AdicCompletion` at the maximal ideal.
Completion maps between local rings use the canonical `completedLocalMap` from
Algebra, Chapter 97.  The statements below retain the source's Noetherian,
local, flatness, residue-field, Nagata, reducedness, and normality hypotheses.
-/

namespace Formalization.Books.MoreAlgebra.Unit43

open Formalization.Books.Algebra.Unit96
open Formalization.Books.Algebra.Unit97
open Formalization.Books.Algebra.Unit72
open Formalization.Books.Algebra.Unit104
open Formalization.Books.Algebra.Unit37
open Formalization.Books.Algebra.Unit162

universe u v

noncomputable section

/-! ## The local completion -/

/-- The standard properties of the completion of a Noetherian local ring. -/
theorem localCompletion_properties
    {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A] :
    IsNoetherianRing (ringCompletion (IsLocalRing.maximalIdeal A)) ∧
      IsLocalRing (ringCompletion (IsLocalRing.maximalIdeal A)) ∧
      IsAdicComplete
        (IsLocalRing.maximalIdeal
          (ringCompletion (IsLocalRing.maximalIdeal A)))
        (ringCompletion (IsLocalRing.maximalIdeal A)) ∧
      IsLocalRing.maximalIdeal
          (ringCompletion (IsLocalRing.maximalIdeal A)) =
        (IsLocalRing.maximalIdeal A).map
          (algebraMap A (ringCompletion (IsLocalRing.maximalIdeal A))) ∧
      RingHom.FaithfullyFlat
        (algebraMap A (ringCompletion (IsLocalRing.maximalIdeal A))) := by
  refine ⟨completion_is_noetherian (IsLocalRing.maximalIdeal A), inferInstance,
    inferInstance, ?_, ?_⟩
  · exact AdicCompletion.maximalIdeal_eq_map
  · exact local_completion_faithfully_flat

/-! ## Dimension, depth, Cohen--Macaulayness, regularity, and DVRs -/

/-- Krull dimension is unchanged by completion. -/
theorem completion_dimension
    {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A] :
    ringKrullDim A =
      ringKrullDim (ringCompletion (IsLocalRing.maximalIdeal A)) := by
  sorry

/-- Local depth is unchanged by completion. -/
theorem completion_depth
    {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A] :
    localDepth A A =
      localDepth (ringCompletion (IsLocalRing.maximalIdeal A))
        (ringCompletion (IsLocalRing.maximalIdeal A)) := by
  sorry

/-- Cohen--Macaulayness is preserved and reflected by completion. -/
theorem completion_cohenMacaulay
    {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A] :
    letI : IsNoetherianRing (ringCompletion (IsLocalRing.maximalIdeal A)) :=
      completion_is_noetherian (IsLocalRing.maximalIdeal A)
    IsCohenMacaulayLocalRing A ↔
      IsCohenMacaulayLocalRing
        (ringCompletion (IsLocalRing.maximalIdeal A)) := by
  sorry

/-- Regularity is preserved and reflected by completion. -/
theorem completion_regular
    {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A] :
    letI : IsNoetherianRing (ringCompletion (IsLocalRing.maximalIdeal A)) :=
      completion_is_noetherian (IsLocalRing.maximalIdeal A)
    IsRegularLocalRing A ↔
      IsRegularLocalRing (ringCompletion (IsLocalRing.maximalIdeal A)) := by
  sorry

/-- The discrete-valuation-ring property is preserved and reflected by
completion.  The existential domain witnesses expose Mathlib's canonical
domain-indexed DVR class. -/
theorem completion_discreteValuationRing
    {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A] :
    letI : IsNoetherianRing (ringCompletion (IsLocalRing.maximalIdeal A)) :=
      completion_is_noetherian (IsLocalRing.maximalIdeal A)
    (∃ hA : IsDomain A, @IsDiscreteValuationRing A _ hA) ↔
      (∃ hA' : IsDomain (ringCompletion (IsLocalRing.maximalIdeal A)),
        @IsDiscreteValuationRing
          (ringCompletion (IsLocalRing.maximalIdeal A)) _ hA') := by
  sorry

/-! ## Reduced and normal completions -/

/-- Reducedness descends from the completion. -/
theorem reduced_of_completion_reduced
    {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    (hA : IsReduced (ringCompletion (IsLocalRing.maximalIdeal A))) :
    IsReduced A := by
  sorry

/-- Reducedness need not ascend to the completion in general. -/
theorem completion_reduced_not_of_reduced_in_general :
    ¬ ∀ (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A],
      IsReduced A →
        IsReduced (ringCompletion (IsLocalRing.maximalIdeal A)) := by
  sorry

/-- For a Nagata local ring, reducedness is preserved and reflected by
completion. -/
theorem completion_reduced_iff_of_nagata
    {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    (hA : IsNagataRing A) :
    IsReduced A ↔
      IsReduced (ringCompletion (IsLocalRing.maximalIdeal A)) := by
  sorry

/-- Normality descends from the completion. -/
theorem normal_of_completion_normal
    {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    (hA : IsNormalRing (ringCompletion (IsLocalRing.maximalIdeal A))) :
    IsNormalRing A := by
  sorry

/-! ## Flatness of maps after completion -/

/-- A local homomorphism of Noetherian local rings is flat exactly when its
induced map on completions is flat. -/
theorem flat_completion_iff
    {A B : Type u} [CommRing A] [CommRing B]
    [IsNoetherianRing A] [IsNoetherianRing B]
    [IsLocalRing A] [IsLocalRing B]
    (f : A →+* B) [IsLocalHom f] :
    letI : Algebra A B := f.toAlgebra
    letI : IsLocalHom (algebraMap A B) := by
      change IsLocalHom f
      infer_instance
    RingHom.Flat (completedLocalMap A B) ↔ RingHom.Flat f := by
  sorry

/-- A flat local map inducing an isomorphism on maximal ideals and residue
fields induces a bijective map on completions. -/
theorem completion_map_bijective_of_flat_unramified
    {A B : Type u} [CommRing A] [CommRing B]
    [IsNoetherianRing A] [IsNoetherianRing B]
    [IsLocalRing A] [IsLocalRing B]
    (f : A →+* B) [IsLocalHom f]
    (hflat : RingHom.Flat f)
    (hmax : (IsLocalRing.maximalIdeal A).map f =
      IsLocalRing.maximalIdeal B)
    (hres : Function.Bijective (IsLocalRing.ResidueField.map f)) :
    letI : Algebra A B := f.toAlgebra
    letI : IsLocalHom (algebraMap A B) := by
      change IsLocalHom f
      infer_instance
    Function.Bijective (completedLocalMap A B) := by
  sorry

end

end Formalization.Books.MoreAlgebra.Unit43
