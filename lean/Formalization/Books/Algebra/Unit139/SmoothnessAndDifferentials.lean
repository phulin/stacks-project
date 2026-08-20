import Formalization.Books.Algebra.Unit138.FormallySmoothMaps
import Formalization.Books.Algebra.Unit78.FiniteProjectiveModules
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
   exposes the exact sequence `0 → I/I² → J/J² →
   C ⊗[B] Ω[B/A] → 0` with its canonical differential map. -/
theorem application_NL_smooth
    {A B C : Type*} [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra A C] [Algebra B C] [IsScalarTower A B C]
    (hAC : Function.Surjective (algebraMap A C))
    [Algebra.Smooth A B] :
    Function.Injective
        (Algebra.Extension.Cotangent.map
          (Formalization.Books.Algebra.Unit138.surjectiveExtensionOverHom hAC
            (Formalization.Books.Algebra.Unit138.surjective_of_composite_algebraMap
              (B := B) hAC))) ∧
      Function.Exact
        (Algebra.Extension.Cotangent.map
          (Formalization.Books.Algebra.Unit138.surjectiveExtensionOverHom hAC
            (Formalization.Books.Algebra.Unit138.surjective_of_composite_algebraMap
              (B := B) hAC)))
        (Formalization.Books.Algebra.Unit138.surjectiveExtensionOver
          (A := A)
          (Formalization.Books.Algebra.Unit138.surjective_of_composite_algebraMap
            (B := B) hAC)).cotangentComplex ∧
      Function.Surjective
        (Formalization.Books.Algebra.Unit138.surjectiveExtensionOver
          (A := A)
          (Formalization.Books.Algebra.Unit138.surjective_of_composite_algebraMap
            (B := B) hAC)).cotangentComplex := by
  have hformal : Algebra.FormallySmooth A B := inferInstance
  have h := Formalization.Books.Algebra.Unit138.application_NL_formallySmooth_canonical
    (A := A) (B := B) (C := C) hAC hformal
  exact ⟨h.1, h.2.1, h.2.2.1⟩

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
  let P := sectionExtension σ
  have hσ : Function.Surjective σ := by
    intro r
    exact ⟨algebraMap R S r, σ.commutes r⟩
  have hker : P.ker.FG := by
    change (RingHom.ker σ.toRingHom).FG
    exact Algebra.FinitePresentation.ker_fG_of_surjective σ hσ
  let oldAlg : Algebra R S := inferInstance
  let oldFormal : @Algebra.FormallySmooth R S _ _ oldAlg := by
    letI : Algebra R S := oldAlg
    exact inferInstance
  have alg_eq : oldAlg = P.algebra₁ := by
    apply Algebra.algebra_ext
    intro r
    rfl
  let : Algebra R P.Ring := P.algebra₁
  let : @Algebra.FormallySmooth R P.Ring _ _ P.algebra₁ := by
    exact alg_eq ▸ oldFormal
  letI : Algebra S R := P.algebra₂
  have hfinite : Module.Finite R P.Cotangent :=
    Algebra.Extension.Cotangent.finite hker
  letI : Module.Projective R P.CotangentSpace := by
    change Module.Projective R (R ⊗[S]
      Formalization.Books.Algebra.Unit131.ModuleOfDifferentials R S)
    infer_instance
  have hsplit : ∃ l : P.CotangentSpace →ₗ[R] P.Cotangent,
      l.comp P.cotangentComplex = LinearMap.id :=
    (Algebra.Extension.formallySmooth_iff_split_injection P).mp inferInstance
  obtain ⟨l, hl⟩ := hsplit
  have hprojective : Module.Projective R P.Cotangent :=
    Module.Projective.of_split P.cotangentComplex l hl
  have hfiniteProjective :
      Formalization.Books.Algebra.Unit78.FiniteProjective R P.Cotangent :=
    ⟨hfinite, hprojective⟩
  simpa [P, sectionConormal] using
    ((Formalization.Books.Algebra.Unit78.finite_projective_characterization
      (R := R) (M := P.Cotangent)).out 1 6).mp hfiniteProjective

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
