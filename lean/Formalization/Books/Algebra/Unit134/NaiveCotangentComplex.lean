import Formalization.Books.Algebra.Unit75.TorGroups
import Formalization.Books.Algebra.Unit131.Differentials
import Mathlib.RingTheory.Extension.Cotangent.BaseChange
import Mathlib.RingTheory.Extension.Cotangent.LocalizationAway
import Mathlib.RingTheory.Extension.ExtendScalars
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
  apply (Algebra.Extension.subsingleton_h1Cotangent _).2
  have hker : (Algebra.Generators.mvPolynomial R ι).toExtension.ker = ⊥ := by
    change RingHom.ker (MvPolynomial.aeval (R := R)
      (MvPolynomial.X : ι → MvPolynomial ι R)) = ⊥
    rw [← RingHom.injective_iff_ker_eq_bot]
    intro p q hpq
    simpa only [MvPolynomial.aeval_X_left_apply] using hpq
  intro x y hxy
  obtain ⟨x, rfl⟩ := Algebra.Extension.Cotangent.mk_surjective x
  obtain ⟨y, rfl⟩ := Algebra.Extension.Cotangent.mk_surjective y
  rw [Algebra.Extension.Cotangent.mk_eq_mk_iff_sub_mem]
  have hker2 : (Algebra.Generators.mvPolynomial R ι).toExtension.ker ^ 2 = ⊥ := by
    rw [hker]
    simp
  rw [hker2]
  have hx : x.1 = 0 := by
    have hx' : x.1 ∈ (⊥ : Ideal (Algebra.Generators.mvPolynomial R ι).toExtension.Ring) :=
      hker ▸ x.property
    simpa using hx'
  have hy : y.1 = 0 := by
    have hy' : y.1 ∈ (⊥ : Ideal (Algebra.Generators.mvPolynomial R ι).toExtension.Ring) :=
      hker ▸ y.property
    simpa using hy'
  simp [hx, hy]

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

/- The Tor hypotheses in the full Jacobi--Zariski statement are used on the
   two-term presentation complex.  This is the tensor-exactness bridge for
   the presentation-level maps; unlike the flatness lemma above, it only
   assumes the two stated Tor vanishings. -/
theorem exact_lTensor_h1Cotangentι_cotangentComplex_of_tor_vanishing
    {R S T ι : Type u} [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra R T] [Algebra S T] [IsScalarTower R S T]
    (P : Algebra.Generators R S ι)
    (h₁ : IsZero (Formalization.Books.Algebra.Unit75.Tor
      (ModuleCat.of S (Formalization.Books.Algebra.Unit131.ModuleOfDifferentials R S))
      (ModuleCat.of S T) 1))
    (h₂ : IsZero (Formalization.Books.Algebra.Unit75.Tor
      (ModuleCat.of S (Formalization.Books.Algebra.Unit131.ModuleOfDifferentials R S))
      (ModuleCat.of S T) 2)) :
    Function.Exact
      (LinearMap.lTensor T P.toExtension.h1Cotangentι)
      (LinearMap.lTensor T P.toExtension.cotangentComplex) := by
  let d := P.toExtension.cotangentComplex
  let i := P.toExtension.h1Cotangentι
  let q := P.toExtension.toKaehler
  have h₁id : Function.Exact i d.rangeRestrict := by
    rw [LinearMap.exact_iff, LinearMap.ker_rangeRestrict]
    exact LinearMap.exact_iff.mp P.toExtension.exact_hCotangentι_cotangentComplex
  have h₂id : Function.Exact (LinearMap.range d).subtype q := by
    intro x
    constructor
    · intro hx
      obtain ⟨y, rfl⟩ := (P.toExtension.exact_cotangentComplex_toKaehler _).mp hx
      exact ⟨⟨d y, ⟨y, rfl⟩⟩, rfl⟩
    · intro hx
      obtain ⟨y, rfl⟩ := hx
      exact (P.toExtension.exact_cotangentComplex_toKaehler _).mpr y.property
  have h₂comp : q.comp (LinearMap.range d).subtype = 0 := by
    apply LinearMap.ext
    intro x
    exact (h₂id _).mpr ⟨x, rfl⟩
  let C : ShortComplex (ModuleCat (S)) :=
    ModuleCat.shortComplexOfCompEqZero
      (M := LinearMap.range d) (N := P.toExtension.CotangentSpace)
      (LinearMap.range d).subtype q h₂comp
  have hC : C.ShortExact := by
    apply ModuleCat.shortComplex_shortExact C h₂id
    · intro x y hxy
      exact Subtype.ext hxy
    · exact P.toExtension.toKaehler_surjective
  obtain ⟨H⟩ := Formalization.Books.Algebra.Unit75.exists_tor_long_exact_sequence
    (ModuleCat.of S T) C hC
  have hTor : IsZero (Formalization.Books.Algebra.Unit75.Tor
      (ModuleCat.of S T)
      (ModuleCat.of S (Formalization.Books.Algebra.Unit131.ModuleOfDifferentials R S)) 1) :=
    h₁.of_iso (Formalization.Books.Algebra.Unit75.torLeftRightIso
      (ModuleCat.of S (Formalization.Books.Algebra.Unit131.ModuleOfDifferentials R S))
      (ModuleCat.of S T) 1).symm
  have hTorData : IsZero (Formalization.Books.Algebra.Unit75.Tor
      (ModuleCat.of S T)
      (ModuleCat.of S (Formalization.Books.Algebra.Unit131.ModuleOfDifferentials R S)) 1) ∧
      IsZero (Formalization.Books.Algebra.Unit75.Tor
        (ModuleCat.of S (Formalization.Books.Algebra.Unit131.ModuleOfDifferentials R S))
        (ModuleCat.of S T) 2) := ⟨hTor, h₂⟩
  let hSubsingleton : Subsingleton (Formalization.Books.Algebra.Unit75.Tor
      (ModuleCat.of S T) C.X₃ 1) := by
    simpa [C] using ModuleCat.subsingleton_of_isZero hTorData.1
  have hTensorInjective : Function.Injective (LinearMap.lTensor T (LinearMap.range d).subtype) := by
    intro x y hxy
    have hz : (LinearMap.lTensor T (LinearMap.range d).subtype) (x - y) = 0 := by
      rw [map_sub, hxy, sub_self]
    obtain ⟨z, hz'⟩ := (H.exact₃ _).mp hz
    have hz0 : z = 0 := @Subsingleton.elim _ hSubsingleton _ _
    rw [hz0, map_zero] at hz'
    exact sub_eq_zero.mp hz'.symm
  have hTensorExact := @lTensor_exact S P.toExtension.H1Cotangent
      P.toExtension.Cotangent (LinearMap.range d) _ _ _ _ _ _ _ i d.rangeRestrict T
      _ _ h₁id (LinearMap.surjective_rangeRestrict d)
  change Function.Exact (LinearMap.lTensor T i) (LinearMap.lTensor T d)
  intro x
  constructor
  · intro hx
    have hx' : (LinearMap.lTensor T (LinearMap.range d).subtype)
        ((LinearMap.lTensor T d.rangeRestrict) x) = 0 := by
      change ((LinearMap.lTensor T (LinearMap.range d).subtype).comp
        (LinearMap.lTensor T d.rangeRestrict)) x = 0
      rw [← LinearMap.lTensor_comp]
      change (LinearMap.lTensor T d) x = 0
      exact hx
    have hx'' : (LinearMap.lTensor T d.rangeRestrict) x = 0 :=
      by
        apply hTensorInjective
        simpa using hx'
    exact (hTensorExact _).mp hx''
  · rintro ⟨y, rfl⟩
    change ((LinearMap.lTensor T d).comp (LinearMap.lTensor T i)) y = 0
    rw [← LinearMap.lTensor_comp]
    have hzero : d.comp i = 0 := by
      apply LinearMap.ext
      intro z
      exact (P.toExtension.exact_hCotangentι_cotangentComplex _).mpr ⟨z, rfl⟩
    rw [hzero, LinearMap.lTensor_zero]
    simp

private theorem exact_liftBaseChange_map_of_tensor_exact
    {R S T ι σ : Type*} [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra R T] [Algebra S T] [IsScalarTower R S T]
    (Q : Algebra.Generators S T ι) (P : Algebra.Generators R S σ)
    (hP : Function.Exact
      (LinearMap.lTensor T P.toExtension.h1Cotangentι)
      (LinearMap.lTensor T P.toExtension.cotangentComplex)) :
    Function.Exact
      ((Algebra.Extension.H1Cotangent.map (Q.toComp P).toExtensionHom).liftBaseChange T)
      (Algebra.Extension.H1Cotangent.map (Q.ofComp P).toExtensionHom) := by
  rw [LinearMap.exact_iff]
  refine le_antisymm ?_
    (Algebra.Generators.H1Cotangent.liftBaseChange_range_le Q P)
  rintro ⟨x, x_in⟩ hx
  replace hx : Algebra.Extension.Cotangent.map (Q.ofComp P).toExtensionHom x = 0 := by
    change Algebra.Extension.H1Cotangent.map (Q.ofComp P).toExtensionHom
        ⟨x, x_in⟩ = 0 at hx
    have hx' := congrArg (fun z => Algebra.Extension.h1Cotangentι z) hx
    have hmap' := DFunLike.congr_fun
      (Algebra.Extension.Cotangent.map_comp_h1Cotangentι
        (Q.ofComp P).toExtensionHom) ⟨x, x_in⟩
    change Algebra.Extension.Cotangent.map (Q.ofComp P).toExtensionHom x =
      Algebra.Extension.h1Cotangentι
        (Algebra.Extension.H1Cotangent.map (Q.ofComp P).toExtensionHom ⟨x, x_in⟩) at hmap'
    rw [← hmap'] at hx'
    change Algebra.Extension.Cotangent.map (Q.ofComp P).toExtensionHom x = 0 at hx'
    exact hx'
  rw [← LinearMap.mem_ker,
    (Algebra.Generators.Cotangent.exact Q P).linearMap_ker_eq] at hx
  rcases hx with ⟨x, rfl⟩
  have auxMemKer : ∀ z : T ⊗[S] P.toExtension.H1Cotangent,
      LinearMap.liftBaseChange T
          (Algebra.Extension.Cotangent.map (Q.toComp P).toExtensionHom)
          ((LinearMap.lTensor T Algebra.Extension.h1Cotangentι) z) ∈
        (Q.comp P).toExtension.cotangentComplex.ker := by
    intro z
    induction z with
    | zero =>
      apply LinearMap.mem_ker.mpr
      simp
    | tmul x y =>
      have hy : P.toExtension.cotangentComplex
          (Algebra.Extension.h1Cotangentι y) = 0 :=
        (P.toExtension.exact_hCotangentι_cotangentComplex _).mpr ⟨y, rfl⟩
      simp [← Algebra.Extension.CotangentSpace.map_cotangentComplex, hy]
    | add x y hx hy => simpa using Submodule.add_mem _ hx hy
  rw [LinearMap.mem_ker, ← LinearMap.comp_apply,
    ← Algebra.Generators.H1Cotangent.map_comp_cotangentComplex_baseChange, LinearMap.comp_apply,
    ← LinearMap.mem_ker,
    LinearMap.ker_eq_bot.mpr (Algebra.Generators.CotangentSpace.map_toComp_injective Q P),
    Submodule.mem_bot, LinearMap.baseChange_eq_ltensor, ← LinearMap.mem_ker,
    hP.linearMap_ker_eq] at x_in
  rcases x_in with ⟨x, rfl⟩
  use x
  induction x with
  | zero =>
    apply Subtype.ext
    simp
  | tmul x y =>
    apply Subtype.ext
    have hmap := DFunLike.congr_fun
      (Algebra.Extension.Cotangent.map_comp_h1Cotangentι
        (Q.toComp P).toExtensionHom) y
    change Algebra.Extension.Cotangent.map (Q.toComp P).toExtensionHom
        (Algebra.Extension.h1Cotangentι y) =
      Algebra.Extension.h1Cotangentι
        (Algebra.Extension.H1Cotangent.map (Q.toComp P).toExtensionHom y) at hmap
    change x • Algebra.Extension.h1Cotangentι
        (Algebra.Extension.H1Cotangent.map (Q.toComp P).toExtensionHom y) = _
    exact congrArg (fun z => x • z) hmap.symm
  | add x y hx hy =>
    rw [map_add]
    rw [hx (auxMemKer x), hy (auxMemKer y)]
    apply Subtype.ext
    simp only [map_add]
    rfl

/- The presentation-level exactness is the input needed by the canonical
   H¹ comparison.  Keeping this step separate makes the Tor bridge reusable
   for other presentations of `S` over `R`. -/
theorem jacobi_zariski_h1_base_change_of_tensor_exact
    {R S T : Type u} [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra R T] [Algebra S T] [IsScalarTower R S T]
    (hP : Function.Exact
      (LinearMap.lTensor T
        (Algebra.Generators.self R S).toExtension.h1Cotangentι)
      (LinearMap.lTensor T
        (Algebra.Generators.self R S).toExtension.cotangentComplex)) :
    Function.Exact ((Algebra.H1Cotangent.map R R S T).liftBaseChange T)
      (Algebra.H1Cotangent.map R S T T) := by
  let Q := Algebra.Generators.self S T
  let P := Algebra.Generators.self R S
  let W := Algebra.Generators.self R T
  rw [← LinearEquiv.conj_exact_iff_exact _ _
    (Algebra.Generators.H1Cotangent.equiv W (Q.comp P))]
  convert! exact_liftBaseChange_map_of_tensor_exact Q P hP
  · change Algebra.Extension.H1Cotangent.map
        (W.defaultHom (Q.comp P)).toExtensionHom ∘ₗ _ = _
    rw [Algebra.H1Cotangent.map, LinearMap.liftBaseChange_comp,
      ← Algebra.Extension.H1Cotangent.map_comp,
      Algebra.Extension.H1Cotangent.map_eq]
  · change (Algebra.Extension.H1Cotangent.map
        (Algebra.Generators.defaultHom W Q).toExtensionHom).restrictScalars T ∘ₗ
      Algebra.Extension.H1Cotangent.map _ = _
    rw [← Algebra.Extension.H1Cotangent.map_comp,
      Algebra.Extension.H1Cotangent.map_eq]

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
  exact jacobi_zariski_h1_base_change_of_tensor_exact
    (exact_lTensor_h1Cotangentι_cotangentComplex_of_tor_vanishing
      (Algebra.Generators.self R S) h₁ h₂)

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
  refine ⟨Algebra.Extension.Hom.mk (algebraMap A B) ?_ ?_⟩
  · intro a
    simp [surjectiveExtension]
  · intro b
    change algebraMap B C (algebraMap A B b) = algebraMap A C b
    exact (IsScalarTower.algebraMap_apply A B C b).symm

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
    (Q : Algebra.Generators S T ι) (P : Algebra.Generators R S σ) :
    ∃ h : T ⊗[S] P.toExtension.CotangentSpace →ₗ[T]
        Q.toExtension.Cotangent,
      Algebra.Extension.CotangentSpace.map (Q.ofComp P).toExtensionHom ∘ₗ
          (Algebra.Extension.CotangentSpace.map (Q.toComp P).toExtensionHom).liftBaseChange T =
        Q.toExtension.cotangentComplex ∘ₗ h := by
  refine ⟨0, ?_⟩
  apply LinearMap.ext
  intro x
  simpa only [LinearMap.comp_apply, LinearMap.zero_apply, map_zero] using
    ((Algebra.Generators.CotangentSpace.exact Q P) _).mpr ⟨x, rfl⟩

/-! ## Surjections, applications, and base change -/

theorem naive_cotangent_of_surjection
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    (h : Function.Surjective (algebraMap R S)) :
    Nonempty ((surjectiveExtension h).Cotangent ≃ₗ[S] NaiveCotangentH1 R S) := by
  exact ⟨(surjectiveExtension h).h1CotangentEquivCotangent.symm⟩

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
  have hmapzero : KaehlerDifferential.map R R S T = 0 := by
    apply LinearMap.ext
    intro x
    have hspan := KaehlerDifferential.span_range_derivation R S
    have hx : x ∈ Submodule.span S (Set.range (KaehlerDifferential.D R S)) := by
      rw [hspan]
      trivial
    refine Submodule.span_induction
      (p := fun y _ => (KaehlerDifferential.map R R S T) y = 0)
      ?_ ?_ ?_ ?_ hx
    · rintro x ⟨s, rfl⟩
      obtain ⟨r, hr⟩ := hRT (algebraMap S T s)
      rw [KaehlerDifferential.map_D, ← hr]
      simp
    · simp
    · intros x y _ _ hx hy
      simp [map_add, hx, hy]
    · intros a x _ hx
      simp [map_smul, hx]
  have hbase : KaehlerDifferential.mapBaseChange R S T = 0 := by
    apply LinearMap.ext
    intro x
    induction x with
    | zero => simp
    | add x y hx hy => simp [hx, hy]
    | tmul t x =>
        obtain ⟨r, hr⟩ := hRT t
        rw [← hr]
        simp [KaehlerDifferential.mapBaseChange_tmul, hmapzero]
  have hδ : Function.Surjective (Algebra.H1Cotangent.δ R S T) := by
    intro z
    apply (Algebra.H1Cotangent.exact_δ_mapBaseChange R S T z).mp
    rw [hbase]
    simp
  let ERT := (surjectiveExtension hRT).h1CotangentEquivCotangent
  let EST := (surjectiveExtension hST).h1CotangentEquivCotangent
  let hmapidR : Algebra.H1Cotangent.map R R T T = LinearMap.id := by
    change Algebra.Extension.H1Cotangent.map
      ((Algebra.Generators.self R T).defaultHom
        (Algebra.Generators.self R T)).toExtensionHom = _
    rw [Algebra.Extension.H1Cotangent.map_eq]
    exact Algebra.Extension.H1Cotangent.map_id
  let hmapidS : Algebra.H1Cotangent.map S S T T = LinearMap.id := by
    change Algebra.Extension.H1Cotangent.map
      ((Algebra.Generators.self S T).defaultHom
        (Algebra.Generators.self S T)).toExtensionHom = _
    rw [Algebra.Extension.H1Cotangent.map_eq]
    exact Algebra.Extension.H1Cotangent.map_id
  have hRTEq :
      ERT = Algebra.Extension.h1Cotangentι ∘ₗ
        Algebra.Extension.H1Cotangent.map
          (Algebra.Extension.defaultHom R T (surjectiveExtension hRT)) := by
    have h := Algebra.Extension.h1CotangentEquivCotangent_comp_map
      (surjectiveExtension hRT)
    convert h using 1
    simp only [hmapidR, LinearMap.comp_id]
    rfl
  have hSTE :
      EST = Algebra.Extension.h1Cotangentι ∘ₗ
        Algebra.Extension.H1Cotangent.map
          (Algebra.Extension.defaultHom S T (surjectiveExtension hST)) := by
    have h := Algebra.Extension.h1CotangentEquivCotangent_comp_map
      (surjectiveExtension hST)
    convert h using 1
    simp only [hmapidS, LinearMap.comp_id]
    rfl
  have hcomp :
      Algebra.Extension.Cotangent.map (surjectiveExtensionHom hRT hST) ∘ₗ ERT.toLinearMap =
        EST.toLinearMap ∘ₗ Algebra.H1Cotangent.map R S T T := by
    rw [hRTEq, hSTE]
    rw [← LinearMap.comp_assoc, Algebra.Extension.Cotangent.map_comp_h1Cotangentι]
    rw [LinearMap.comp_assoc]
    ext x
    simp only [LinearMap.comp_apply]
    simp only [Algebra.H1Cotangent.map]
    rw [← Algebra.Extension.H1Cotangent.map_comp_apply
      (Algebra.Extension.defaultHom R T (surjectiveExtension hRT))
      (surjectiveExtensionHom hRT hST)]
    rw [← Algebra.Extension.H1Cotangent.map_comp_apply
      ((Algebra.Generators.self R T).defaultHom
        (Algebra.Generators.self S T)).toExtensionHom
      (Algebra.Extension.defaultHom S T (surjectiveExtension hST))]
    have hmapeq := Algebra.Extension.H1Cotangent.map_eq
      ((surjectiveExtensionHom hRT hST).comp
        (Algebra.Extension.defaultHom R T (surjectiveExtension hRT)))
      ((Algebra.Extension.defaultHom S T (surjectiveExtension hST)).comp
        ((Algebra.Generators.self R T).defaultHom
          (Algebra.Generators.self S T)).toExtensionHom)
    exact congrArg (fun z => Algebra.Extension.h1Cotangentι z)
      (DFunLike.congr_fun hmapeq x)
  let d := (Algebra.H1Cotangent.δ R S T).comp EST.symm.toLinearMap
  refine ⟨d, ?_, ?_⟩
  · have hcanon := (LinearEquiv.conj_exact_iff_exact
        (Algebra.H1Cotangent.map R S T T)
        (Algebra.H1Cotangent.δ R S T) EST).2
        (Algebra.H1Cotangent.exact_map_δ R S T)
    intro z
    constructor
    · intro hz
      obtain ⟨y, hy⟩ := (hcanon z).mp hz
      refine ⟨ERT y, ?_⟩
      exact (DFunLike.congr_fun hcomp y).trans hy
    · rintro ⟨y, hy⟩
      apply (hcanon z).mpr
      refine ⟨ERT.symm y, ?_⟩
      calc
        EST (Algebra.H1Cotangent.map R S T T (ERT.symm y)) =
            Algebra.Extension.Cotangent.map (surjectiveExtensionHom hRT hST)
              (ERT (ERT.symm y)) := (DFunLike.congr_fun hcomp (ERT.symm y)).symm
        _ = z := by simpa using hy
  · intro z
    obtain ⟨y, hy⟩ := hδ z
    refine ⟨EST y, ?_⟩
    dsimp [d]
    rw [EST.symm_apply_apply]
    exact hy

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
  exact ⟨Algebra.FormallyEtale.subsingleton_h1Cotangent,
    Algebra.FormallyEtale.subsingleton_kaehlerDifferential⟩

private noncomputable def naive_cotangent_localize_bottom_aux
    {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    (M : Submonoid A) [Algebra (Localization M) B]
    [IsScalarTower A (Localization M) B] :
    Σ' (_ : IsLocalization (Algebra.algebraMapSubmonoid B M) B),
      PLift (Function.Bijective (Algebra.H1Cotangent.map A (Localization M) B B) ∧
        Function.Bijective (KaehlerDifferential.map A (Localization M) B B)) := by
  have hbase := naive_cotangent_localization_of_base M
  let M' := Algebra.algebraMapSubmonoid B M
  let hLoc : IsLocalization M' B := by
    apply IsLocalization.of_le_isUnit
    rintro x ⟨a, ha, rfl⟩
    change IsUnit ((algebraMap A B) a)
    simpa only [IsScalarTower.algebraMap_apply A (Localization M) B] using
      IsUnit.map (algebraMap (Localization M) B)
        (IsLocalization.map_units (Localization M) ⟨a, ha⟩)
  letI : Subsingleton (Formalization.Books.Algebra.Unit131.ModuleOfDifferentials
      A (Localization M)) := hbase.2
  letI : IsLocalization M' B := hLoc
  refine ⟨hLoc, ?_⟩
  have hzero : KaehlerDifferential.mapBaseChange A (Localization M) B = 0 := by
    apply LinearMap.ext
    intro x
    have hx : x = 0 := Subsingleton.elim _ _
    subst x
    exact (KaehlerDifferential.mapBaseChange A (Localization M) B).map_zero
  have hex := KaehlerDifferential.exact_mapBaseChange_map A (Localization M) B
  have hinj : Function.Injective (KaehlerDifferential.map A (Localization M) B B) := by
    intro x y hxy
    have hz : KaehlerDifferential.map A (Localization M) B B (x - y) = 0 := by
      simp [map_sub, hxy]
    obtain ⟨z, hz⟩ := (hex (x - y)).mp hz
    have hzero' : x - y = 0 := by
      simpa [hzero] using hz.symm
    exact sub_eq_zero.mp hzero'
  let H := Algebra.H1Cotangent A B
  let fL : H →ₗ[Localization M] H := LinearMap.id
  have hlocL : IsLocalizedModule
      (Algebra.algebraMapSubmonoid (Localization M) M) fL := by
    constructor
    · intro m
      obtain ⟨_, ⟨a, ha, rfl⟩⟩ := m
      exact IsUnit.map (algebraMap (Localization M) (Module.End (Localization M) H))
        (IsLocalization.map_units (Localization M) ⟨a, ha⟩)
    · intro y
      exact ⟨⟨y, 1⟩, by simp [fL]⟩
    · intro x y hxy
      exact ⟨1, by simpa [fL] using hxy⟩
  have hloc : IsLocalizedModule M (fL.restrictScalars A) :=
    IsLocalizedModule.restrictScalars M fL
  let f : H →ₗ[A] H := fL.restrictScalars A
  have hbaseH' := (isLocalizedModule_iff_isBaseChange M (Localization M) f).mp hloc
  change Function.Bijective (f.liftBaseChange (Localization M)) at hbaseH'
  have hbaseH : Function.Bijective (f.liftBaseChange (Localization M)) := hbaseH'
  let eLoc : Localization M' ≃ₐ[B] B :=
    IsLocalization.algEquiv M' (Localization M') B
  let eLocL : Localization M' ≃ₐ[Localization M] B :=
    { eLoc with
      commutes' := by
        intro x
        have hmap :
            algebraMap (Localization M) (Localization M') =
              (algebraMap B (Localization M')).comp (algebraMap (Localization M) B) := by
          apply IsLocalization.ringHom_ext (R := A) (S := Localization M)
            (P := Localization M') M
          ext a
          simp only [RingHom.comp_apply]
          rw [← IsScalarTower.algebraMap_apply A (Localization M) (Localization M')]
          rw [← IsScalarTower.algebraMap_apply A (Localization M) B]
          rw [IsScalarTower.algebraMap_apply A B (Localization M')]
        rw [hmap]
        change eLoc (algebraMap B (Localization M') ((algebraMap (Localization M) B) x)) = _
        exact eLoc.commutes _ }
  let e : (Localization M) ⊗[A] B ≃ₐ[Localization M] B :=
    (Localization.tensorRightAlgEquiv M B).trans
      eLocL
  have hkaehlerSurj : Function.Surjective (KaehlerDifferential.map A (Localization M) B B) :=
    KaehlerDifferential.map_surjective A (Localization M) B
  let eH : ((Localization M) ⊗[A] H) ≃ₗ[Localization M] H :=
    LinearEquiv.ofBijective (f.liftBaseChange (Localization M)) hbaseH
  let hb := Algebra.tensorH1CotangentOfFlat A B (Localization M)
  letI : Algebra B ((Localization M) ⊗[A] B) := Algebra.TensorProduct.rightAlgebra
  letI : Algebra ((Localization M) ⊗[A] B) B := e.toRingHom.toAlgebra
  letI : IsScalarTower (Localization M) ((Localization M) ⊗[A] B) B :=
    IsScalarTower.of_algebraMap_eq' e.toAlgHom.comp_algebraMap.symm
  let eB : ((Localization M) ⊗[A] B) ≃ₐ[B] B :=
    { e with
      commutes' := by
        intro b
        change e (algebraMap B ((Localization M) ⊗[A] B) b) = b
        rw [Algebra.TensorProduct.right_algebraMap_apply]
        change eLocL (Localization.tensorRightAlgEquiv M B (1 ⊗ₜ[A] b)) = b
        rw [Localization.tensorRightAlgEquiv_apply_one_tmul]
        exact eLoc.commutes _ }
  letI : IsScalarTower B ((Localization M) ⊗[A] B) B :=
    IsScalarTower.of_algebraMap_eq' eB.toAlgHom.comp_algebraMap.symm
  refine ⟨?_⟩
  let he := Algebra.H1Cotangent.mapEquiv (Localization M)
    ((Localization M) ⊗[A] B) B e
  have hmap (x : Algebra.H1Cotangent A B) :
      he (Algebra.H1Cotangent.map A (Localization M) B ((Localization M) ⊗[A] B) x) =
        Algebra.H1Cotangent.map A (Localization M) B B x := by
    change
      Algebra.H1Cotangent.map (Localization M) (Localization M)
          ((Localization M) ⊗[A] B) B
          (Algebra.H1Cotangent.map A (Localization M) B ((Localization M) ⊗[A] B) x) = _
    simp only [Algebra.H1Cotangent.map]
    rw [← Algebra.Extension.H1Cotangent.map_comp_apply]
    rw [Algebra.Extension.H1Cotangent.map_eq]
  have hkey :
      he.toLinearMap ∘ₗ hb.toLinearMap =
        (Algebra.H1Cotangent.map A (Localization M) B B).restrictScalars (Localization M) ∘ₗ
          eH.toLinearMap := by
    ext y
    simp [eH, f, fL]
    rw [Algebra.tensorH1CotangentOfFlat_tmul]
    simp [hmap]
  have hkres :
      Function.Bijective
        ((Algebra.H1Cotangent.map A (Localization M) B B).restrictScalars (Localization M)) := by
    let ec := hb.trans he
    constructor
    · intro x y hxy
      obtain ⟨u, hu⟩ := eH.surjective x
      obtain ⟨v, hv⟩ := eH.surjective y
      have hku :
          he (hb u) =
            (Algebra.H1Cotangent.map A (Localization M) B B).restrictScalars
              (Localization M) (eH u) := by
        simpa only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe] using
          congrArg (fun F => F u) hkey
      have hkv :
          he (hb v) =
            (Algebra.H1Cotangent.map A (Localization M) B B).restrictScalars
              (Localization M) (eH v) := by
        simpa only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe] using
          congrArg (fun F => F v) hkey
      have huv : ec u = ec v := by
        calc
          ec u = he (hb u) := rfl
          _ = (Algebra.H1Cotangent.map A (Localization M) B B).restrictScalars
                (Localization M) (eH u) := hku
          _ = (Algebra.H1Cotangent.map A (Localization M) B B).restrictScalars
                (Localization M) x := by rw [hu]
          _ = (Algebra.H1Cotangent.map A (Localization M) B B).restrictScalars
                (Localization M) y := by rw [hxy]
          _ = (Algebra.H1Cotangent.map A (Localization M) B B).restrictScalars
                (Localization M) (eH v) := by rw [hv]
          _ = he (hb v) := hkv.symm
          _ = ec v := rfl
      have huv' : u = v := ec.injective huv
      calc
        x = eH u := hu.symm
        _ = eH v := congrArg eH huv'
        _ = y := hv
    · intro z
      obtain ⟨u, hu⟩ := ec.surjective z
      refine ⟨eH u, ?_⟩
      have hku :
          he (hb u) =
            (Algebra.H1Cotangent.map A (Localization M) B B).restrictScalars
              (Localization M) (eH u) := by
        simpa only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe] using
          congrArg (fun F => F u) hkey
      calc
        (Algebra.H1Cotangent.map A (Localization M) B B).restrictScalars
              (Localization M) (eH u) = he (hb u) := hku.symm
        _ = ec u := rfl
        _ = z := hu
  refine ⟨?_, ⟨hinj, hkaehlerSurj⟩⟩
  simpa only [LinearMap.coe_restrictScalars] using hkres

theorem naive_cotangent_localize_bottom
    {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    (M : Submonoid A) [Algebra (Localization M) B]
    [IsScalarTower A (Localization M) B] :
    Function.Bijective (Algebra.H1Cotangent.map A (Localization M) B B) ∧
      Function.Bijective (KaehlerDifferential.map A (Localization M) B B) := by
  exact (naive_cotangent_localize_bottom_aux M).2.down

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
  let Q := Algebra.Generators.localizationAway T g
  let rel : (Q.comp P).Ring :=
    MvPolynomial.rename Sum.inr f * MvPolynomial.X (Sum.inl ()) - 1
  let x : (Q.comp P).toExtension.Cotangent :=
    Algebra.Extension.Cotangent.mk ⟨rel, by
      change (MvPolynomial.rename Sum.inr f * MvPolynomial.X (Sum.inl ()) - 1 :
        MvPolynomial (Unit ⊕ ι) R) ∈
        ((Algebra.Generators.localizationAway T g).comp P).ker
      rw [Algebra.Generators.comp_localizationAway_ker g P f hf]
      exact Ideal.mem_sup_right (Ideal.subset_span (by simp))⟩
  have hx : Algebra.Extension.Cotangent.map (Q.ofComp P).toExtensionHom x =
      Algebra.Generators.cMulXSubOneCotangent T g := by
    rw [Algebra.Generators.cMulXSubOneCotangent_eq]
    simp only [x, Algebra.Extension.Cotangent.map_mk]
    rw [Algebra.Extension.Cotangent.mk_eq_mk_iff_sub_mem]
    change (Q.ofComp P).toAlgHom rel -
        (C g * X () - 1 : Q.Ring) ∈ Q.ker ^ 2
    dsimp [rel]
    rw [map_sub, map_mul, Algebra.Generators.toAlgHom_ofComp_rename]
    simp [hf]
  change Nonempty ((Q.comp P).toExtension.Cotangent ≃ₗ[T]
    T ⊗[S] P.toExtension.Cotangent × Q.toExtension.Cotangent)
  refine ⟨?_⟩
  exact Algebra.Generators.cotangentCompLocalizationAwayEquiv g P hx

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
  let Q := Algebra.Generators.localizationAway T g
  change Nonempty ((Q.comp P).toExtension.CotangentSpace ≃ₗ[T]
    Q.toExtension.CotangentSpace × T ⊗[S] P.toExtension.CotangentSpace)
  exact ⟨Algebra.Generators.CotangentSpace.compEquiv Q P⟩

theorem naive_cotangent_localization_quasi_isomorphism
    {R B : Type*} [CommRing R] [CommRing B] [Algebra R B]
    (M : Submonoid B) :
    Function.Bijective
        ((Algebra.H1Cotangent.map R R B (Localization M)).liftBaseChange (Localization M)) ∧
      Function.Bijective
        ((KaehlerDifferential.map R R B (Localization M)).liftBaseChange (Localization M)) := by
  have h1 : IsLocalizedModule M
      (Algebra.H1Cotangent.map R R B (Localization M)) := by
    infer_instance
  have h0 : IsLocalizedModule M
      (KaehlerDifferential.map R R B (Localization M)) := by
    infer_instance
  exact ⟨
    (isLocalizedModule_iff_isBaseChange M (Localization M)
      (Algebra.H1Cotangent.map R R B (Localization M))).mp h1,
    (isLocalizedModule_iff_isBaseChange M (Localization M)
      (KaehlerDifferential.map R R B (Localization M))).mp h0⟩

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
  let F : TwoTermSum A₁ B₀ →ₗ[R] TwoTermSum B₁ A₀ :=
    { toFun := fun x =>
        (H.φ₁ x.1 - H.hB x.2, H.dA x.1 + H.ψ₀ x.2)
      map_add' := by
        intro x y
        apply Prod.ext
        · dsimp
          rw [map_add, map_add]
          abel
        · dsimp
          rw [map_add, map_add]
          abel
      map_smul' := by
        intro c x
        apply Prod.ext
        · dsimp
          rw [map_smul, smul_sub]
        · dsimp
          rw [map_smul, smul_add] }
  let G : TwoTermSum B₁ A₀ →ₗ[R] TwoTermSum A₁ B₀ :=
    { toFun := fun x =>
        (H.ψ₁ x.1 + H.hA x.2, -H.dB x.1 + H.φ₀ x.2)
      map_add' := by
        intro x y
        apply Prod.ext
        · dsimp
          rw [map_add, map_add]
          abel
        · dsimp
          rw [map_add, map_add]
          abel
      map_smul' := by
        intro c x
        apply Prod.ext
        · dsimp
          rw [map_smul, smul_add]
        · dsimp
          rw [map_smul, smul_add] }
  have hGF (x : TwoTermSum A₁ B₀) :
      G (F x) = (x.1 + (-H.ψ₁ (H.hB x.2) + H.hA (H.ψ₀ x.2)), x.2) := by
    ext
    · simp [F, G, sub_eq_add_neg, add_assoc, add_comm]
      have h := DFunLike.congr_fun H.left_one x.1
      change x.1 - H.ψ₁ (H.φ₁ x.1) = H.hA (H.dA x.1) at h
      rw [← h]
      abel
    · simp [F, G, sub_eq_add_neg, add_assoc, add_comm]
      have hchain := DFunLike.congr_fun H.φ_chain x.1
      change H.φ₀ (H.dA x.1) = H.dB (H.φ₁ x.1) at hchain
      rw [hchain]
      have h := DFunLike.congr_fun H.right_zero x.2
      change x.2 - H.φ₀ (H.ψ₀ x.2) = H.dB (H.hB x.2) at h
      rw [← h]
      abel
  have hFG (x : TwoTermSum B₁ A₀) :
      F (G x) = (x.1 + (H.φ₁ (H.hA x.2) - H.hB (H.φ₀ x.2)), x.2) := by
    ext
    · simp [F, G, sub_eq_add_neg, add_assoc, add_comm]
      have h := DFunLike.congr_fun H.right_one x.1
      change x.1 - H.φ₁ (H.ψ₁ x.1) = H.hB (H.dB x.1) at h
      rw [← h]
      abel
    · simp [F, G, sub_eq_add_neg, add_assoc, add_comm]
      have hchain := DFunLike.congr_fun H.ψ_chain x.1
      change H.ψ₀ (H.dB x.1) = H.dA (H.ψ₁ x.1) at hchain
      rw [← hchain]
      have h := DFunLike.congr_fun H.left_zero x.2
      change x.2 - H.ψ₀ (H.φ₀ x.2) = H.dA (H.hA x.2) at h
      rw [← h]
      abel
  have hFinj : Function.Injective F := by
    intro x y hxy
    have hxy' := congrArg G hxy
    have h2 := congrArg Prod.snd hxy'
    have h1 := congrArg Prod.fst hxy'
    have h2' : x.2 = y.2 := by simpa [hGF] using h2
    have h1' : x.1 = y.1 := by
      simpa [hGF, h2'] using h1
    exact Prod.ext h1' h2'
  have hFsurj : Function.Surjective F := by
    intro z
    let y : TwoTermSum B₁ A₀ :=
      (z.1 - (H.φ₁ (H.hA z.2) - H.hB (H.φ₀ z.2)), z.2)
    refine ⟨G y, ?_⟩
    rw [hFG]
    simp [y, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
  exact ⟨LinearEquiv.ofBijective F ⟨hFinj, hFsurj⟩⟩

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
