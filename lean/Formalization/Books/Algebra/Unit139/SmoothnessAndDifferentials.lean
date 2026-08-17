import Formalization.Books.Algebra.Unit138.FormallySmoothMaps
import Mathlib.RingTheory.MvPowerSeries.Equiv
import Mathlib.RingTheory.Smooth.AdicCompletion

/-!
# Commutative Algebra, Chapter 139: Smoothness and differentials

The differential sequences use the canonical Kähler-differential maps and the
split-sequence interfaces from Chapter 138.  For a smooth retraction, the
conormal module is the canonical cotangent module of the associated
surjective extension, and its completion is Mathlib's `AdicCompletion`.
-/

namespace Formalization.Books.Algebra.Unit139

open scoped TensorProduct

noncomputable section

/-! ## Smooth differential sequences -/

/- The source's first sequence is short exact.  The stronger split statement
   is already available for formally smooth maps in Chapter 138; this
   declaration records the short exact consequence in the source's order. -/
theorem triangle_differentials_smooth
    {A B C : Type*} [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra A C] [Algebra B C] [IsScalarTower A B C]
    [Algebra.Smooth B C] :
    Function.Injective (KaehlerDifferential.mapBaseChange A B C) ∧
      Function.Exact (KaehlerDifferential.mapBaseChange A B C)
        (KaehlerDifferential.map A B C C) ∧
      Function.Surjective (KaehlerDifferential.map A B C C) := by
  have hformal : Algebra.FormallySmooth B C := inferInstance
  have h := Formalization.Books.Algebra.Unit138.ses_formallySmooth
    (A := A) (B := B) (C := C) hformal
  exact ⟨h.1, h.2.1, h.2.2.1⟩

/- The conormal and differential maps in the source's second sequence are the
   cotangent complex and `toKaehler` of the extension induced by the
   surjection `B → C`. -/
theorem differential_seq_smooth
    {A B C : Type*} [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra A C] [Algebra B C] [IsScalarTower A B C]
    [Algebra.Smooth A C]
    (hBC : Function.Surjective (algebraMap B C)) :
    Formalization.Books.Algebra.Unit138.extensionDifferentialSplitExact
      (Formalization.Books.Algebra.Unit138.surjectiveExtensionOver
        (A := A) hBC) := by
  have hformal : Algebra.FormallySmooth A C := inferInstance
  exact Formalization.Books.Algebra.Unit138.differential_seq_formallySmooth
    (A := A) (B := B) (C := C) hformal hBC

/- The quotient `B/J` in the source is represented by `C` through the given
   surjection.  Chapter 138's canonical surjective-extension interface then
   exposes the sequence `I/I² → J/J² → C ⊗[B] Ω[B/A]`. -/
theorem application_NL_smooth
    {A B C : Type*} [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra A C] [Algebra B C] [IsScalarTower A B C]
    (hAC : Function.Surjective (algebraMap A C))
    [Algebra.Smooth A B] :
    ∃ d :
        (Formalization.Books.Algebra.Unit134.surjectiveExtension
            (Formalization.Books.Algebra.Unit138.surjective_of_composite_algebraMap
              (B := B) hAC)).Cotangent →ₗ[C]
          C ⊗[B] Formalization.Books.Algebra.Unit131.ModuleOfDifferentials A B,
      Formalization.Books.Algebra.Unit138.IsSplitExactLinearSequence
        (Algebra.Extension.Cotangent.map
          (Formalization.Books.Algebra.Unit134.surjectiveExtensionHom hAC
            (Formalization.Books.Algebra.Unit138.surjective_of_composite_algebraMap
              (B := B) hAC))) d := by
  have hformal : Algebra.FormallySmooth A B := inferInstance
  exact Formalization.Books.Algebra.Unit138.application_NL_formallySmooth
    (A := A) (B := B) (C := C) hAC hformal

/-! ## A smooth retraction and its conormal module -/

/- The source's `φ : R → S` is the canonical algebra map.  An `R`-algebra map
   `σ : S →ₐ[R] R` is its retraction; the left-inverse identity is automatic
   from `AlgHom.commutes`. -/
noncomputable def sectionExtension
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    (σ : S →ₐ[R] R) : Algebra.Extension R R := by
  apply Algebra.Extension.ofSurjective σ
  intro r
  refine ⟨algebraMap R S r, ?_⟩
  exact σ.commutes r

def sectionIdeal
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    (σ : S →ₐ[R] R) : Ideal S :=
  RingHom.ker σ.toRingHom

abbrev sectionConormal
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    (σ : S →ₐ[R] R) : Type _ :=
  (sectionExtension σ).Cotangent

theorem section_smooth_conormal_finiteLocallyFree
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.Smooth R S] (σ : S →ₐ[R] R) :
    Formalization.Books.Algebra.Unit78.FiniteLocallyFree R
      (sectionConormal σ) := by
  sorry

/- The finite free case of the source's completion statement is expressed by
   a finite index `Fin d`; `MvPowerSeries (Fin d) R` is the canonical Lean
   type for `R[[t₁, ..., t_d]]`. -/
theorem section_smooth_completion_eq_powerSeries
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.Smooth R S] (σ : S →ₐ[R] R)
    (hfree : Module.Free R (sectionConormal σ)) :
    ∃ d : ℕ,
      Nonempty
        (AdicCompletion (sectionIdeal σ) S ≃ₐ[R]
          MvPowerSeries (Fin d) R) := by
  sorry

end

end Formalization.Books.Algebra.Unit139
