import Formalization.Books.Algebra.Unit131.Differentials
import Formalization.Books.Algebra.Unit75.TorGroups
import Mathlib.RingTheory.Extension.Cotangent.BaseChange
import Mathlib.RingTheory.Extension.Cotangent.LocalizationAway
import Mathlib.RingTheory.Extension.Presentation.Basic
import Mathlib.RingTheory.Kaehler.JacobiZariski
import Mathlib.RingTheory.Localization.Basic
import Mathlib.LinearAlgebra.Basis.Basic

/-!
# Commutative Algebra, Chapter 134: The naive cotangent complex

The current Mathlib API already contains the canonical presentation-independent
construction used by this chapter.  `Algebra.Extension.Cotangent` is the
conormal module `I/I²`, `Extension.CotangentSpace` is
`S ⊗[P] Ω[P/R]`, and `Extension.cotangentComplex` is the degree-one to
degree-zero differential of the two-term complex.  The declarations below
keep the source order while exposing the source notation and recording the
statements which are not single Mathlib declarations.
-/

namespace Formalization.Books.Algebra.Unit134

open scoped TensorProduct
open MvPolynomial
open Module
open CategoryTheory CategoryTheory.Limits

attribute [local instance] SMulCommClass.of_commMonoid

noncomputable section

universe u v w u' v' w'

/-! ## The canonical presentation -/

abbrev PolynomialRing (R S : Type*) [CommRing R] [CommRing S] : Type _ :=
  MvPolynomial S R

noncomputable def canonicalPresentation
    (R S : Type*) [CommRing R] [CommRing S] [Algebra R S] :
    PolynomialRing R S →ₐ[R] S :=
  MvPolynomial.aeval (R := R) (fun s : S => s)

@[simp]
theorem canonicalPresentation_variable
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] (s : S) :
    canonicalPresentation R S (MvPolynomial.X s) = s := by
  simp [canonicalPresentation]

/- The canonical generators are Mathlib's `Generators.self`, whose designated
   section sends `s : S` to the variable `X s`. -/
abbrev CanonicalGenerators (R S : Type*) [CommRing R] [CommRing S]
    [Algebra R S] : Algebra.Generators R S S :=
  Algebra.Generators.self R S

abbrev CanonicalExtension (R S : Type*) [CommRing R] [CommRing S]
    [Algebra R S] : Algebra.Extension R S :=
  (CanonicalGenerators R S).toExtension

abbrev CanonicalConormal (R S : Type*) [CommRing R] [CommRing S]
    [Algebra R S] : Type _ :=
  (CanonicalExtension R S).Cotangent

abbrev CanonicalCotangentSpace (R S : Type*) [CommRing R] [CommRing S]
    [Algebra R S] : Type _ :=
  (CanonicalExtension R S).CotangentSpace

/- The source's `NL` is encoded by its canonical differential.  This is the
   representation used by Mathlib for a two-term complex. -/
abbrev NaiveCotangentComplex (R S : Type*) [CommRing R] [CommRing S]
    [Algebra R S] : CanonicalConormal R S →ₗ[S] CanonicalCotangentSpace R S :=
  (CanonicalExtension R S).cotangentComplex

abbrev NaiveCotangentH1 (R S : Type*) [CommRing R] [CommRing S]
    [Algebra R S] : Type _ :=
  Algebra.H1Cotangent R S

/- The source's simplicial polynomial resolution and its actual cotangent
   complex are the motivation for the naive object.  Mathlib exposes their
   degree-one invariant through `Algebra.H1Cotangent` and the degree-zero
   invariant through the exact conormal--cotangent--Kähler sequence below;
   it has no separate simplicial-resolution object in this API. -/

abbrev NaiveCotangentCokernel (R S : Type*) [CommRing R] [CommRing S]
    [Algebra R S] : Type _ :=
  CanonicalCotangentSpace R S ⧸ LinearMap.range (NaiveCotangentComplex R S)

def canonicalRelations
    (R S : Type*) [CommRing R] [CommRing S] [Algebra R S] :
    Set (PolynomialRing R S) :=
  Set.range (fun st : S × S =>
      X (st.1 + st.2) - X st.1 - X st.2) ∪
    Set.range (fun st : S × S =>
      X st.1 * X st.2 - X (st.1 * st.2)) ∪
    Set.range (fun r : R => X (algebraMap R S r) - C r)

theorem canonical_kernel_is_generated_by_relations
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] :
    Ideal.span (canonicalRelations R S) = (CanonicalGenerators R S).ker := by
  apply le_antisymm
  · rw [Algebra.Generators.ker_eq_ker_aeval_val, Ideal.span_le]
    intro p hp
    simp only [canonicalRelations, Set.mem_union, Set.mem_range] at hp
    rcases hp with (⟨⟨s, t⟩, rfl⟩ | ⟨⟨s, t⟩, rfl⟩) | ⟨r, rfl⟩
    · simp [CanonicalGenerators, Algebra.Generators.self]
    · simp [CanonicalGenerators, Algebra.Generators.self]
    · simp [CanonicalGenerators, Algebra.Generators.self]
  · intro p hp
    have hnormal : ∀ p : PolynomialRing R S,
        p - X ((canonicalPresentation R S) p) ∈ Ideal.span (canonicalRelations R S) := by
      intro q
      induction q using MvPolynomial.induction_on with
      | C r =>
          have hrel : X (algebraMap R S r) - C r ∈ canonicalRelations R S := by
            simp [canonicalRelations]
          have hm := neg_mem (Ideal.subset_span hrel)
          simpa [canonicalPresentation] using hm
      | add p q hp hq =>
          have hrel : X ((canonicalPresentation R S) p) +
                X ((canonicalPresentation R S) q) -
                X ((canonicalPresentation R S) p + (canonicalPresentation R S) q) ∈
                Ideal.span (canonicalRelations R S) := by
            have hm := Ideal.subset_span (show
                X ((canonicalPresentation R S) p + (canonicalPresentation R S) q) -
                  X ((canonicalPresentation R S) p) -
                  X ((canonicalPresentation R S) q) ∈ canonicalRelations R S by
                    simp [canonicalRelations])
            simpa [sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using
              neg_mem hm
          rw [map_add]
          have hm := add_mem (add_mem hp hq) hrel
          convert hm using 1; abel
      | mul_X p s hp =>
          have hrel : X ((canonicalPresentation R S) p) * X s -
                X ((canonicalPresentation R S) p * s) ∈
                Ideal.span (canonicalRelations R S) := by
            exact Ideal.subset_span (show
                X ((canonicalPresentation R S) p) * X s -
                  X ((canonicalPresentation R S) p * s) ∈ canonicalRelations R S by
                    simp [canonicalRelations])
          rw [map_mul, canonicalPresentation_variable]
          have hm := add_mem
            (Ideal.mul_mem_right (X s) (Ideal.span (canonicalRelations R S)) hp) hrel
          convert hm using 1; ring_nf
    rw [Algebra.Generators.ker_eq_ker_aeval_val] at hp
    have hval : canonicalPresentation R S p = 0 := RingHom.mem_ker.mp hp
    have hz : X (0 : S) ∈ Ideal.span (canonicalRelations R S) := by
      apply Ideal.subset_span
      unfold canonicalRelations
      exact Or.inr ⟨0, by simp⟩
    have hm := add_mem (hnormal p) hz
    rw [hval] at hm
    convert hm using 1; abel

theorem canonical_cotangentComplex_on_conormal
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    (x : (CanonicalExtension R S).ker) :
    (CanonicalExtension R S).cotangentComplex
        (Algebra.Extension.Cotangent.mk x) =
      1 ⊗ₜ[(CanonicalExtension R S).Ring]
        KaehlerDifferential.D R (CanonicalExtension R S).Ring x.1 := by
  exact (CanonicalExtension R S).cotangentComplex_mk x

theorem canonical_exact_cotangentComplex_to_differentials
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] :
    Function.Exact (NaiveCotangentComplex R S)
      (CanonicalExtension R S).toKaehler := by
  exact (CanonicalExtension R S).exact_cotangentComplex_toKaehler

theorem canonical_to_differentials_surjective
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] :
    Function.Surjective (CanonicalExtension R S).toKaehler := by
  exact (CanonicalExtension R S).toKaehler_surjective

theorem canonical_cokernel_equiv_differentials
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] :
    Nonempty (NaiveCotangentCokernel R S ≃ₗ[S]
      Formalization.Books.Algebra.Unit131.ModuleOfDifferentials R S) := by
  let f : CanonicalCotangentSpace R S →ₗ[S]
      Formalization.Books.Algebra.Unit131.ModuleOfDifferentials R S :=
    (CanonicalExtension R S).toKaehler
  have hf : Function.Surjective f :=
    canonical_to_differentials_surjective (R := R) (S := S)
  have hExact := canonical_exact_cotangentComplex_to_differentials (R := R) (S := S)
  have hker : LinearMap.range (NaiveCotangentComplex R S) = LinearMap.ker f := by
    simpa [f] using (LinearMap.exact_iff.mp hExact).symm
  refine ⟨(Submodule.quotEquivOfEq (R := S) (M := CanonicalCotangentSpace R S) _ _ hker).trans (f.quotKerEquivOfSurjective hf)⟩

/-! ## Presentations and their naive cotangent complexes -/

/- A presentation is Mathlib's family of polynomial generators together with
   its chosen section.  A presentation with named relations is the stronger
   `Algebra.Presentation` structure from `Extension.Presentation.Basic`. -/
abbrev Presentation (R S : Type*) [CommRing R] [CommRing S] [Algebra R S]
    (ι : Type*) := Algebra.Generators R S ι

abbrev PresentationExtension
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    {ι : Type*} (P : Presentation R S ι) : Algebra.Extension R S :=
  P.toExtension

noncomputable def presentationFromSurjective
    {R S ι : Type*} [CommRing R] [CommRing S] [Algebra R S]
    (f : MvPolynomial ι R →ₐ[R] S) (hf : Function.Surjective f) :
    Presentation R S ι :=
  Algebra.Generators.ofAlgHom f hf

abbrev PresentationConormal
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    {ι : Type*} (P : Presentation R S ι) : Type _ :=
  P.toExtension.Cotangent

abbrev PresentationCotangentSpace
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    {ι : Type*} (P : Presentation R S ι) : Type _ :=
  P.toExtension.CotangentSpace

abbrev PresentationNaiveCotangentComplex
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    {ι : Type*} (P : Presentation R S ι) :
    PresentationConormal P →ₗ[S] PresentationCotangentSpace P :=
  P.toExtension.cotangentComplex

abbrev PresentationNaiveH1
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    {ι : Type*} (P : Presentation R S ι) : Type _ :=
  P.toExtension.H1Cotangent

noncomputable def presentationCotangentBasis
    {R S ι : Type*} [CommRing R] [CommRing S] [Algebra R S]
    (P : Presentation R S ι) :
    Basis ι S (PresentationCotangentSpace P) :=
  P.cotangentSpaceBasis

theorem presentation_exact_cotangentComplex_to_differentials
    {R S ι : Type*} [CommRing R] [CommRing S] [Algebra R S]
    (P : Presentation R S ι) :
    Function.Exact (PresentationNaiveCotangentComplex P) P.toExtension.toKaehler := by
  exact P.toExtension.exact_cotangentComplex_toKaehler

theorem presentation_to_differentials_surjective
    {R S ι : Type*} [CommRing R] [CommRing S] [Algebra R S]
    (P : Presentation R S ι) :
    Function.Surjective P.toExtension.toKaehler := by
  exact P.toExtension.toKaehler_surjective

theorem presentation_cokernel_equiv_differentials
    {R S ι : Type*} [CommRing R] [CommRing S] [Algebra R S]
    (P : Presentation R S ι) :
    Nonempty ((PresentationCotangentSpace P ⧸
        LinearMap.range (PresentationNaiveCotangentComplex P)) ≃ₗ[S]
      Formalization.Books.Algebra.Unit131.ModuleOfDifferentials R S) := by
  let f : PresentationCotangentSpace P →ₗ[S]
      Formalization.Books.Algebra.Unit131.ModuleOfDifferentials R S :=
    P.toExtension.toKaehler
  have hf : Function.Surjective f :=
    presentation_to_differentials_surjective (R := R) (S := S) (ι := ι) P
  have hExact :=
    presentation_exact_cotangentComplex_to_differentials (R := R) (S := S) (ι := ι) P
  have hker : LinearMap.range (PresentationNaiveCotangentComplex P) = LinearMap.ker f := by
    simpa [f] using (LinearMap.exact_iff.mp hExact).symm
  exact ⟨(Submodule.quotEquivOfEq (R := S) (M := PresentationCotangentSpace P) _ _ hker).trans (f.quotKerEquivOfSurjective hf)⟩

theorem presentation_cotangentComplex_on_conormal
    {R S ι : Type*} [CommRing R] [CommRing S] [Algebra R S]
    (P : Presentation R S ι) (x : P.toExtension.ker) :
    P.toExtension.cotangentComplex (Algebra.Extension.Cotangent.mk x) =
      1 ⊗ₜ[P.Ring] KaehlerDifferential.D R P.Ring x.1 := by
  exact P.toExtension.cotangentComplex_mk x

theorem finite_type_has_finite_generator_presentation
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.FiniteType R S] :
    ∃ n : ℕ, Nonempty (Presentation R S (Fin n)) := by
  simpa using (Algebra.FiniteType.iff_exists_generators (R := R) (S := S)).mp inferInstance

/-! ## Functoriality and homotopy independence -/

/- `Generators.Hom` is the source's morphism of presentations.  Its
   `toExtensionHom` supplies the induced maps on conormal modules and
   cotangent spaces. -/
abbrev PresentationHom
    {R R' S S' ι ι' : Type*} [CommRing R] [CommRing R'] [CommRing S] [CommRing S']
    [Algebra R S] [Algebra R' S'] [Algebra R R'] [Algebra S S']
    [Algebra R S'] [IsScalarTower R R' S'] [IsScalarTower R S S']
    (P : Presentation R S ι) (P' : Presentation R' S' ι') := P.Hom P'

noncomputable def defaultPresentationHom
    {R R' S S' ι ι' : Type*} [CommRing R] [CommRing R'] [CommRing S] [CommRing S']
    [Algebra R S] [Algebra R' S'] [Algebra R R'] [Algebra S S']
    [Algebra R S'] [IsScalarTower R R' S'] [IsScalarTower R S S']
    (P : Presentation R S ι) (P' : Presentation R' S' ι') : P.Hom P' :=
  Algebra.Generators.defaultHom P P'

noncomputable def presentationCotangentSpaceMap
    {R R' S S' ι ι' : Type*} [CommRing R] [CommRing R'] [CommRing S] [CommRing S']
    [Algebra R S] [Algebra R' S'] [Algebra R R'] [Algebra S S']
    [Algebra R S'] [IsScalarTower R R' S'] [IsScalarTower R S S']
    (P : Presentation R S ι) (P' : Presentation R' S' ι') (f : P.Hom P') :
    P.toExtension.CotangentSpace →ₗ[S] P'.toExtension.CotangentSpace :=
  Algebra.Extension.CotangentSpace.map f.toExtensionHom

noncomputable def presentationConormalMap
    {R R' S S' ι ι' : Type*} [CommRing R] [CommRing R'] [CommRing S] [CommRing S']
    [Algebra R S] [Algebra R' S'] [Algebra R R'] [Algebra S S']
    [Algebra R S'] [IsScalarTower R R' S'] [IsScalarTower R S S']
    (P : Presentation R S ι) (P' : Presentation R' S' ι') (f : P.Hom P') :
    P.toExtension.Cotangent →ₗ[S] P'.toExtension.Cotangent :=
  Algebra.Extension.Cotangent.map f.toExtensionHom

noncomputable def presentationHomotopy
    {R R' S S' ι ι' : Type*} [CommRing R] [CommRing R'] [CommRing S] [CommRing S']
    [Algebra R S] [Algebra R' S'] [Algebra R R'] [Algebra S S']
    [Algebra R S'] [IsScalarTower R R' S'] [IsScalarTower R S S']
    (P : Presentation R S ι) (P' : Presentation R' S' ι')
    (f g : P.Hom P') :
    P.toExtension.CotangentSpace →ₗ[S] P'.toExtension.Cotangent :=
  f.toExtensionHom.sub g.toExtensionHom

theorem presentation_maps_respect_cotangentComplex
    {R R' S S' ι ι' : Type*} [CommRing R] [CommRing R'] [CommRing S] [CommRing S']
    [Algebra R S] [Algebra R' S'] [Algebra R R'] [Algebra S S']
    [Algebra R S'] [IsScalarTower R R' S'] [IsScalarTower R S S']
    (P : Presentation R S ι) (P' : Presentation R' S' ι') (f : P.Hom P') :
    presentationCotangentSpaceMap P P' f ∘ₗ P.toExtension.cotangentComplex =
      P'.toExtension.cotangentComplex.restrictScalars S ∘ₗ
        presentationConormalMap P P' f := by
  exact Algebra.Extension.CotangentSpace.map_comp_cotangentComplex f.toExtensionHom

theorem presentation_maps_are_homotopic
    {R R' S S' ι ι' : Type*} [CommRing R] [CommRing R'] [CommRing S] [CommRing S']
    [Algebra R S] [Algebra R' S'] [Algebra R R'] [Algebra S S']
    [Algebra R S'] [IsScalarTower R R' S'] [IsScalarTower R S S']
    (P : Presentation R S ι) (P' : Presentation R' S' ι') (f g : P.Hom P') :
    presentationCotangentSpaceMap P P' f - presentationCotangentSpaceMap P P' g =
      P'.toExtension.cotangentComplex.restrictScalars S ∘ₗ
        presentationHomotopy P P' f g := by
  exact Algebra.Extension.CotangentSpace.map_sub_map f.toExtensionHom g.toExtensionHom

theorem presentation_conormal_maps_are_homotopic
    {R R' S S' ι ι' : Type*} [CommRing R] [CommRing R'] [CommRing S] [CommRing S']
    [Algebra R S] [Algebra R' S'] [Algebra R R'] [Algebra S S']
    [Algebra R S'] [IsScalarTower R R' S'] [IsScalarTower R S S']
    (P : Presentation R S ι) (P' : Presentation R' S' ι') (f g : P.Hom P') :
    presentationConormalMap P P' f - presentationConormalMap P P' g =
      presentationHomotopy P P' f g ∘ₗ P.toExtension.cotangentComplex := by
  exact Algebra.Extension.Cotangent.map_sub_map f.toExtensionHom g.toExtensionHom

theorem presentation_h1_map_independent
    {R R' S S' ι ι' : Type*} [CommRing R] [CommRing R'] [CommRing S] [CommRing S']
    [Algebra R S] [Algebra R' S'] [Algebra R R'] [Algebra S S']
    [Algebra R S'] [IsScalarTower R R' S'] [IsScalarTower R S S']
    (P : Presentation R S ι) (P' : Presentation R' S' ι') (f g : P.Hom P') :
    Algebra.Extension.H1Cotangent.map f.toExtensionHom =
      Algebra.Extension.H1Cotangent.map g.toExtensionHom := by
  exact Algebra.Extension.H1Cotangent.map_eq f.toExtensionHom g.toExtensionHom

noncomputable def presentation_h1_equiv
    {R S ι ι' : Type*} [CommRing R] [CommRing S] [Algebra R S]
    (P : Presentation R S ι) (P' : Presentation R S ι') :
    P.toExtension.H1Cotangent ≃ₗ[S] P'.toExtension.H1Cotangent :=
  Algebra.Generators.H1Cotangent.equiv P P'

noncomputable def canonical_h1_presentation_independence
    {R S ι : Type*} [CommRing R] [CommRing S] [Algebra R S]
    (P : Presentation R S ι) :
    P.toExtension.H1Cotangent ≃ₗ[S] NaiveCotangentH1 R S := by
  exact P.equivH1Cotangent

/-! ## Polynomial extensions and the Jacobi--Zariski sequence -/

theorem naive_cotangent_of_polynomial_extension
    {R ι : Type*} [CommRing R] :
    Subsingleton ((Algebra.Generators.mvPolynomial R ι).toExtension.H1Cotangent) := by
  sorry

theorem jacobi_zariski_exact_sequence
    {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra R T] [Algebra S T] [IsScalarTower R S T] :
    Function.Exact (Algebra.H1Cotangent.map R S T T)
        (Algebra.H1Cotangent.δ R S T) ∧
      Function.Exact (Algebra.H1Cotangent.δ R S T)
        (KaehlerDifferential.mapBaseChange R S T) ∧
      Function.Exact (KaehlerDifferential.mapBaseChange R S T)
        (KaehlerDifferential.map R S T T) ∧
      Function.Surjective (KaehlerDifferential.map R S T T) := by
  exact ⟨Algebra.H1Cotangent.exact_map_δ R S T,
    Algebra.H1Cotangent.exact_δ_mapBaseChange R S T,
    KaehlerDifferential.exact_mapBaseChange_map R S T,
    KaehlerDifferential.map_surjective R S T⟩

theorem jacobi_zariski_conormal_exact
    {R S T ι σ : Type*} [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra R T] [Algebra S T] [IsScalarTower R S T]
    (Q : Algebra.Generators S T ι) (P : Algebra.Generators R S σ) :
    Function.Exact
      ((Algebra.Extension.Cotangent.map (Q.toComp P).toExtensionHom).liftBaseChange T)
      (Algebra.Extension.Cotangent.map (Q.ofComp P).toExtensionHom) := by
  exact Algebra.Generators.Cotangent.exact Q P

theorem jacobi_zariski_h1_base_change_of_flat
    {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra R T] [Algebra S T] [IsScalarTower R S T]
    [Module.Flat S T] :
    Function.Exact
      ((Algebra.H1Cotangent.map R R S T).liftBaseChange T)
      (Algebra.H1Cotangent.map R S T T) := by
  exact Algebra.H1Cotangent.exact_liftBaseChange_map_of_flat R S T

/- The full source hypothesis is the vanishing of `Tor₁` and `Tor₂`.  The
   Mathlib theorem above is its currently available flat-base-change
   specialization; the source-faithful Tor formulation records the same
   left-hand exactness assertion with the canonical Tor objects from Unit 75. -/
theorem jacobi_zariski_h1_base_change_of_tor_vanishing
    {R S T : Type u} [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra R T] [Algebra S T] [IsScalarTower R S T]
    (h₁ : IsZero (Formalization.Books.Algebra.Unit75.Tor
      (ModuleCat.of S (Formalization.Books.Algebra.Unit131.ModuleOfDifferentials R S))
      (ModuleCat.of S T) 1))
    (h₂ : IsZero (Formalization.Books.Algebra.Unit75.Tor
      (ModuleCat.of S (Formalization.Books.Algebra.Unit131.ModuleOfDifferentials R S))
      (ModuleCat.of S T) 2)) :
    Function.Exact ((Algebra.H1Cotangent.map R R S T).liftBaseChange T)
      (Algebra.H1Cotangent.map R S T T) := by
  sorry

theorem presentation_homotopy_on_differential_generator
    {R R' S S' ι ι' : Type*} [CommRing R] [CommRing R'] [CommRing S] [CommRing S']
    [Algebra R S] [Algebra R' S'] [Algebra R R'] [Algebra S S']
    [Algebra R S'] [IsScalarTower R R' S'] [IsScalarTower R S S']
    (P : Presentation R S ι) (P' : Presentation R' S' ι') (f g : P.Hom P')
    (r : S) (x : P.Ring) :
    presentationHomotopy P P' f g (r ⊗ₜ KaehlerDifferential.D R P.Ring x) =
      r • Algebra.Extension.Cotangent.mk (f.toExtensionHom.subToKer g.toExtensionHom x) := by
  exact Algebra.Extension.Hom.sub_tmul f.toExtensionHom g.toExtensionHom r x

abbrev surjectiveExtension
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    (h : Function.Surjective (algebraMap R S)) : Algebra.Extension R S :=
  { Ring := R
    commRing := inferInstance
    algebra₁ := Algebra.id R
    algebra₂ := inferInstance
    isScalarTower := inferInstance
    σ := fun s => Classical.choose (h s)
    algebraMap_σ := fun s => Classical.choose_spec (h s) }

theorem exists_surjectiveExtensionHom
    {A B C : Type*} [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra A C] [Algebra B C] [IsScalarTower A B C]
    (hAC : Function.Surjective (algebraMap A C))
    (hBC : Function.Surjective (algebraMap B C)) :
    Nonempty ((surjectiveExtension hAC).Hom (surjectiveExtension hBC)) := by
  sorry

noncomputable def surjectiveExtensionHom
    {A B C : Type*} [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra A C] [Algebra B C] [IsScalarTower A B C]
    (hAC : Function.Surjective (algebraMap A C))
    (hBC : Function.Surjective (algebraMap B C)) :
    (surjectiveExtension hAC).Hom (surjectiveExtension hBC) :=
  Classical.choice (exists_surjectiveExtensionHom hAC hBC)

theorem jacobi_zariski_composition_is_null_homotopic
    {R S T ι σ : Type*} [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra R T] [Algebra S T] [IsScalarTower R S T]
    (Q : Algebra.Generators S T ι) (P : Algebra.Generators R S σ)
    (f g : (Q.comp P).Hom (Algebra.Generators.self R T)) :
    ∃ h : (Q.comp P).toExtension.CotangentSpace →ₗ[T]
        (Algebra.Generators.self R T).toExtension.Cotangent,
      Algebra.Extension.CotangentSpace.map f.toExtensionHom -
          Algebra.Extension.CotangentSpace.map g.toExtensionHom =
        (Algebra.Generators.self R T).toExtension.cotangentComplex ∘ₗ h := by
  exact ⟨f.toExtensionHom.sub g.toExtensionHom,
    Algebra.Extension.CotangentSpace.map_sub_map f.toExtensionHom g.toExtensionHom⟩

/-! ## Surjections, applications, and base change -/

theorem naive_cotangent_of_surjection
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    (h : Function.Surjective (algebraMap R S)) :
    Nonempty ((surjectiveExtension h).Cotangent ≃ₗ[S] NaiveCotangentH1 R S) := by
  sorry

theorem conormal_exact_for_two_surjections
    {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra R T] [Algebra S T] [IsScalarTower R S T]
    (hRT : Function.Surjective (algebraMap R T))
    (hST : Function.Surjective (algebraMap S T)) :
    ∃ d : (surjectiveExtension hST).Cotangent →ₗ[T]
        T ⊗[S] Formalization.Books.Algebra.Unit131.ModuleOfDifferentials R S,
      Function.Exact
          (Algebra.Extension.Cotangent.map
          (surjectiveExtensionHom hRT hST)) d ∧
        Function.Surjective d := by
  sorry

noncomputable def presentation_baseChange_cotangentSpace
    {R S T ι : Type*} [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra R T] [Algebra S T] [IsScalarTower R S T]
    (P : Presentation R S ι) :
    T ⊗[R] P.toExtension.CotangentSpace ≃ₗ[T]
      (P.toExtension.baseChange (T := T)).CotangentSpace :=
  P.toExtension.tensorCotangentSpace T

noncomputable def presentation_baseChange_cotangent_of_flat
    {R S T ι : Type*} [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra R T] [Algebra S T] [IsScalarTower R S T]
    [Module.Flat R T] (P : Presentation R S ι) :
    T ⊗[R] P.toExtension.Cotangent ≃ₗ[T]
      (P.toExtension.baseChange (T := T)).Cotangent :=
  P.toExtension.tensorCotangentOfFlat T

theorem presentation_baseChange_components_of_flat
    {R S T ι : Type*} [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra R T] [Algebra S T] [IsScalarTower R S T]
    [Module.Flat R T] (P : Presentation R S ι) :
    Nonempty ((T ⊗[R] P.toExtension.Cotangent ≃ₗ[T]
        (P.toExtension.baseChange (T := T)).Cotangent) ×
      (T ⊗[R] P.toExtension.CotangentSpace ≃ₗ[T]
        (P.toExtension.baseChange (T := T)).CotangentSpace)) :=
  ⟨⟨P.toExtension.tensorCotangentOfFlat T,
    P.toExtension.tensorCotangentSpace T⟩⟩

noncomputable def presentation_baseChange_h1_of_flat
    {R S T ι : Type*} [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra R T] [Algebra S T] [IsScalarTower R S T]
    [Module.Flat R T] (P : Presentation R S ι) :
    T ⊗[R] P.toExtension.H1Cotangent ≃ₗ[T]
      (P.toExtension.baseChange (T := T)).H1Cotangent :=
  P.toExtension.tensorH1CotangentOfFlat T

noncomputable def canonical_baseChange_h1_of_flat
    {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra R T] [Algebra S T] [IsScalarTower R S T]
    [Module.Flat R T] :
    T ⊗[R] Algebra.H1Cotangent R S ≃ₗ[T]
      Algebra.H1Cotangent T (T ⊗[R] S) :=
  Algebra.tensorH1CotangentOfFlat R S T

/-! ## Colimits and localization -/

/- The source's directed-colimit line suppresses the indexing category and
   cocone maps.  The precise finite-stage content is the canonical
   `Generators` functoriality above; a categorical colimit statement would
   require those omitted data. -/

theorem naive_cotangent_localization_of_base
    {A : Type*} [CommRing A] (M : Submonoid A) :
    Subsingleton (Algebra.H1Cotangent A (Localization M)) ∧
      Subsingleton (Formalization.Books.Algebra.Unit131.ModuleOfDifferentials A
        (Localization M)) := by
  sorry

theorem naive_cotangent_localize_bottom
    {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    (M : Submonoid A) [Algebra (Localization M) B]
    [IsScalarTower A (Localization M) B] :
    Function.Bijective (Algebra.H1Cotangent.map A (Localization M) B B) ∧
      Function.Bijective (KaehlerDifferential.map A (Localization M) B B) := by
  sorry

/-! ## Principal and arbitrary localization -/

noncomputable def principalLocalizationPresentation
    {R S T ι : Type*} [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra R T] [Algebra S T] [IsScalarTower R S T]
    (g : S) [IsLocalization.Away g T] (P : Presentation R S ι) :
    Algebra.Generators R T (Sum Unit ι) :=
  (Algebra.Generators.localizationAway T g).comp P

theorem principal_localization_conormal_equiv
    {R S T ι : Type*} [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra R T] [Algebra S T] [IsScalarTower R S T]
    (g : S) [IsLocalization.Away g T] (P : Presentation R S ι)
    (f : P.Ring) (hf : algebraMap P.Ring S f = g) :
    Nonempty (((principalLocalizationPresentation (T := T) g P).toExtension.Cotangent) ≃ₗ[T]
      T ⊗[S] P.toExtension.Cotangent ×
        (Algebra.Generators.localizationAway T g).toExtension.Cotangent) := by
  sorry

theorem principal_localization_kernel_generated
    {R S T ι : Type*} [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra R T] [Algebra S T] [IsScalarTower R S T]
    (g : S) [IsLocalization.Away g T] (P : Presentation R S ι)
    (f : P.Ring) (hf : algebraMap P.Ring S f = g) :
    (principalLocalizationPresentation (T := T) g P).ker =
      Ideal.map ((Algebra.Generators.localizationAway T g).toComp P).toAlgHom P.ker ⊔
        Ideal.span {MvPolynomial.rename Sum.inr f * X (Sum.inl ()) - 1} := by
  exact Algebra.Generators.comp_localizationAway_ker g P f hf

theorem principal_localization_cotangentSpace_equiv
    {R S T ι : Type*} [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra R T] [Algebra S T] [IsScalarTower R S T]
    (g : S) [IsLocalization.Away g T] (P : Presentation R S ι) :
    Nonempty ((principalLocalizationPresentation (T := T) g P).toExtension.CotangentSpace ≃ₗ[T]
      (Algebra.Generators.localizationAway T g).toExtension.CotangentSpace ×
        (T ⊗[S] P.toExtension.CotangentSpace)) := by
  sorry

theorem naive_cotangent_localization_quasi_isomorphism
    {R B : Type*} [CommRing R] [CommRing B] [Algebra R B]
    (M : Submonoid B) :
    (∃ f : Localization M ⊗[B] Algebra.H1Cotangent R B →ₗ[Localization M]
        Algebra.H1Cotangent R (Localization M), Function.Bijective f) ∧
      (∃ g : Localization M ⊗[B]
          Formalization.Books.Algebra.Unit131.ModuleOfDifferentials R B →ₗ[
            Localization M]
          Formalization.Books.Algebra.Unit131.ModuleOfDifferentials R (Localization M),
        Function.Bijective g) := by
  sorry

/-! ## Cancellation and conormal modules -/

abbrev TwoTermSum (M N : Type*) := M × N

structure TwoTermHomotopyData
    (R A₁ A₀ B₁ B₀ : Type*) [CommRing R]
    [AddCommGroup A₁] [AddCommGroup A₀] [AddCommGroup B₁] [AddCommGroup B₀]
    [Module R A₁] [Module R A₀] [Module R B₁] [Module R B₀] where
  dA : A₁ →ₗ[R] A₀
  dB : B₁ →ₗ[R] B₀
  φ₁ : A₁ →ₗ[R] B₁
  φ₀ : A₀ →ₗ[R] B₀
  ψ₁ : B₁ →ₗ[R] A₁
  ψ₀ : B₀ →ₗ[R] A₀
  hA : A₀ →ₗ[R] A₁
  hB : B₀ →ₗ[R] B₁
  φ_chain : φ₀ ∘ₗ dA = dB ∘ₗ φ₁
  ψ_chain : ψ₀ ∘ₗ dB = dA ∘ₗ ψ₁
  left_one : LinearMap.id - ψ₁ ∘ₗ φ₁ = hA ∘ₗ dA
  left_zero : LinearMap.id - ψ₀ ∘ₗ φ₀ = dA ∘ₗ hA
  right_one : LinearMap.id - φ₁ ∘ₗ ψ₁ = hB ∘ₗ dB
  right_zero : LinearMap.id - φ₀ ∘ₗ ψ₀ = dB ∘ₗ hB

theorem two_term_homotopy_cancellation
    {R A₁ A₀ B₁ B₀ : Type*} [CommRing R]
    [AddCommGroup A₁] [AddCommGroup A₀] [AddCommGroup B₁] [AddCommGroup B₀]
    [Module R A₁] [Module R A₀] [Module R B₁] [Module R B₀]
    (H : TwoTermHomotopyData R A₁ A₀ B₁ B₀) :
    Nonempty (TwoTermSum A₁ B₀ ≃ₗ[R] TwoTermSum B₁ A₀) := by
  sorry

theorem conormal_module_equiv
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.FiniteType R S] {n m : ℕ}
    (P : Presentation R S (Fin n)) (Q : Presentation R S (Fin m)) :
    Nonempty (TwoTermSum P.toExtension.Cotangent (Fin m →₀ S) ≃ₗ[S]
      TwoTermSum Q.toExtension.Cotangent (Fin n →₀ S)) := by
  sorry

theorem conormal_module_equiv_localized
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.FiniteType R S] {n m : ℕ} (g : S)
    (P : Presentation R S (Fin n))
    (Q : Presentation R (Localization.Away g) (Fin m)) :
    Nonempty (TwoTermSum
        ((Localization.Away g) ⊗[S] P.toExtension.Cotangent)
        (Fin m →₀ (Localization.Away g)) ≃ₗ[Localization.Away g]
      TwoTermSum Q.toExtension.Cotangent (Fin n →₀ (Localization.Away g))) := by
  sorry

end
end Formalization.Books.Algebra.Unit134
