import Formalization.Books.Algebra.Unit78.FiniteProjectiveModules
import Mathlib.RingTheory.Ideal.Pure
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.Support
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.Topology.Inseparable

/-!
# Commutative Algebra, Chapter 108: Pure ideals

The source's pure ideals use Mathlib's canonical `Ideal.Pure` predicate.  The
vanishing locus and support statements use `PrimeSpectrum.zeroLocus` and
`Module.support`, and finite locally free modules use the interface from
Chapter 78.
-/

namespace Formalization.Books.Algebra.Unit108

open Set

universe u v

noncomputable section

/-! ## Characterizations of pure ideals -/

/- The multiplicative subset `1 + I` in the source is not a separate Mathlib
   object, so we record its canonical submonoid presentation here. -/

/-- The multiplicative subset consisting of the elements `1 + x` with `x ∈ I`. -/
def onePlusIdealSubmonoid {R : Type u} [CommRing R] (I : Ideal R) : Submonoid R :=
  { carrier := {x : R | ∃ y : R, y ∈ I ∧ x = 1 + y}
    one_mem' := by
      exact ⟨0, I.zero_mem, by simp⟩
    mul_mem' := by
      rintro _ _ ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩
      refine ⟨a + b + a * b, ?_, ?_⟩
      · exact I.add_mem (I.add_mem ha hb) (I.mul_mem_left a hb)
      · simp [mul_add, add_mul, add_assoc, add_left_comm, add_comm] }

/-- The eleven conditions in the source's characterization of pure ideals.

Ideal products and intersections are written with Mathlib's lattice and ideal
operations.  The finite-family condition uses a function on `Fin n`, and the
source's multiplicative subset `1 + I` is `onePlusIdealSubmonoid I`. -/
def pureIdealConditions {R : Type u} [CommRing R] (I : Ideal R) : List Prop :=
  [ Ideal.Pure I,
    ∀ J : Ideal R, J ⊓ I = I * J,
    ∀ J : Ideal R, J.FG → J ⊓ I = I * J,
    ∀ x : R, Ideal.span ({x} : Set R) ⊓ I = Ideal.span ({x} : Set R) * I,
    ∀ x : R, x ∈ I → ∃ y : R, y ∈ I ∧ x = y * x,
    ∀ (n : ℕ) (x : Fin n → R),
      (∀ i : Fin n, x i ∈ I) → ∃ y : R, y ∈ I ∧ ∀ i : Fin n, x i = y * x i,
    ∀ p : PrimeSpectrum R,
      I.map (algebraMap R (Localization.AtPrime p.asIdeal)) = ⊥ ∨
        I.map (algebraMap R (Localization.AtPrime p.asIdeal)) = ⊤,
    Module.support R I = (PrimeSpectrum.zeroLocus (I : Set R))ᶜ,
    RingHom.ker (algebraMap R (Localization (onePlusIdealSubmonoid I))) = I,
    ∃ S : Submonoid R, Nonempty ((R ⧸ I) ≃ₐ[R] Localization S),
    Nonempty ((R ⧸ I) ≃ₐ[R] Localization (onePlusIdealSubmonoid I)) ]

/-- The source's eleven equivalent characterizations of a pure ideal. -/
theorem pure_ideal_characterization
    {R : Type u} [CommRing R] (I : Ideal R) :
    List.TFAE (pureIdealConditions I) := by
  sorry

/-! ## Vanishing loci and pure ideals -/

/- This is the forward part of the source's bijection, made explicit so the
   source-facing map below has a precise codomain. -/

/-- The vanishing locus of a pure ideal is closed and stable under generalization. -/
theorem pure_ideal_zeroLocus_isClosed_and_stableUnderGeneralization
    {R : Type u} [CommRing R] (I : Ideal R) (hI : Ideal.Pure I) :
    IsClosed (PrimeSpectrum.zeroLocus (I : Set R)) ∧
      StableUnderGeneralization (PrimeSpectrum.zeroLocus (I : Set R)) := by
  sorry

/-- The source's assertion that a pure ideal is determined by its vanishing locus. -/
theorem pure_ideal_eq_of_zeroLocus_eq
    {R : Type u} [CommRing R] {I J : Ideal R}
    (hI : Ideal.Pure I) (hJ : Ideal.Pure J)
    (h : PrimeSpectrum.zeroLocus (I : Set R) =
      PrimeSpectrum.zeroLocus (J : Set R)) :
    I = J := by
  exact (@Ideal.zeroLocus_inj_of_pure R _ I J hI hJ).mp h

/- The subtype map records the source's rule `I ↦ V(I)` with the stated
   codomain of closed sets stable under generalization. -/

/-- The vanishing-locus map from pure ideals to closed generalization-stable sets. -/
def pureIdealZeroLocusMap {R : Type u} [CommRing R] :
    {I : Ideal R // Ideal.Pure I} →
      {Z : Set (PrimeSpectrum R) // IsClosed Z ∧ StableUnderGeneralization Z} :=
  fun I =>
    ⟨PrimeSpectrum.zeroLocus (I.1 : Set R),
      pure_ideal_zeroLocus_isClosed_and_stableUnderGeneralization I.1 I.2⟩

/-- The rule `I ↦ V(I)` is a bijection onto closed sets stable under generalization. -/
theorem pure_ideal_zeroLocus_bijective
    {R : Type u} [CommRing R] :
    Function.Bijective (pureIdealZeroLocusMap (R := R)) := by
  sorry

/-! ## Finitely generated pure ideals -/

/-- The four conditions characterizing finitely generated pure ideals. -/
def finitelyGeneratedPureIdealConditions
    {R : Type u} [CommRing R] (I : Ideal R) : List Prop :=
  [ Ideal.Pure I ∧ I.FG,
    ∃ e : R, IsIdempotentElem e ∧ I = R ∙ e,
    Ideal.Pure I ∧ IsOpen (PrimeSpectrum.zeroLocus (I : Set R)),
    Module.Projective R (R ⧸ I) ]

/-- The source's four equivalent characterizations of a finitely generated pure ideal. -/
theorem finitely_generated_pure_ideal_characterization
    {R : Type u} [CommRing R] (I : Ideal R) :
    List.TFAE (finitelyGeneratedPureIdealConditions I) := by
  sorry

/-! ## Finite flat modules -/

/- `FiniteLocallyFree` is the earlier chapter's source-facing formulation of
   being finite locally free on a standard-open cover. -/

/-- A ring has the source's finite-flat finiteness property exactly when finite
flat modules are finite locally free. -/
theorem finite_flat_module_finiteLocallyFree_characterization
    {R : Type u} [CommRing R] :
    List.TFAE
      [ ∀ Z : Set (PrimeSpectrum R),
          IsClosed Z → StableUnderGeneralization Z → IsOpen Z,
        ∀ (M : Type v) [AddCommGroup M] [Module R M],
          Module.Finite R M → Module.Flat R M →
            Formalization.Books.Algebra.Unit78.FiniteLocallyFree R M ] := by
  sorry

end

end Formalization.Books.Algebra.Unit108
