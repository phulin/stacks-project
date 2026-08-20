import Formalization.Books.Restricted.Unit02
import Formalization.Books.Algebra.Unit134.NaiveCotangentComplex
import Formalization.Books.MoreAlgebra.Unit83.PseudoCoherentPerfectRingMaps
import Mathlib.RingTheory.FinitePresentation
import Mathlib.RingTheory.RingHom.FinitePresentation

/-!
# Algebraization of Formal Spaces, Chapter 3: A naive cotangent complex

The completed polynomial presentation in the source is represented by a
finite-variable completed polynomial algebra from Chapter 2 together with a
surjective algebra map and its finitely generated kernel.  The actual
two-term differential is Mathlib's canonical conormal-to-cotangent map for
an algebra extension.  This keeps the source's presentation-dependent
formula while reusing the presentation-independent cotangent API.
-/

namespace Formalization.Books.Restricted.Unit03

open CategoryTheory
open Formalization.Books.Restricted.Unit02
open scoped TensorProduct

noncomputable section

universe u v w

/-! ## The completed presentation and its two-term complex -/

/-- The completed polynomial algebra in `r` variables over `(A, I)`. -/
abbrev CompletedPolynomialRing (A : Type u) [CommRing A] (I : Ideal A) (r : ℕ) :
    Type u :=
  (polynomialCompletion I r : Type u)

/-- A choice of the completed polynomial presentation used in the source. -/
structure NaiveCotangentPresentation
    (A : Type u) [CommRing A] [IsNoetherianRing A]
    (I : Ideal A) (B : CompleteAlgebraCategory A I) where
  variableCount : ℕ
  relations : Ideal (CompletedPolynomialRing A I variableCount)
  presentation : CompletedPolynomialRing A I variableCount →ₐ[A] B.obj
  presentation_surjective : Function.Surjective presentation
  relations_eq_kernel : relations = RingHom.ker presentation
  relations_finite : relations.FG

/-- The extension associated to a chosen completed presentation. -/
noncomputable def NaiveCotangentPresentation.extension
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    {I : Ideal A} {B : CompleteAlgebraCategory A I}
    (P : NaiveCotangentPresentation A I B) :
    Algebra.Extension A B.obj :=
  Algebra.Extension.ofSurjective P.presentation P.presentation_surjective

/-- The degree `-1` term `J/J²` of the naive cotangent complex. -/
abbrev NaiveCotangentConormal
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    {I : Ideal A} {B : CompleteAlgebraCategory A I}
    (P : NaiveCotangentPresentation A I B) : Type _ :=
  P.extension.Cotangent

/-- The degree `0` term, represented by the canonical relative cotangent space. -/
abbrev NaiveCotangentSpace
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    {I : Ideal A} {B : CompleteAlgebraCategory A I}
    (P : NaiveCotangentPresentation A I B) : Type _ :=
  P.extension.CotangentSpace

/-- The differential in the source's two-term complex. -/
abbrev NaiveCotangentDifferential
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    {I : Ideal A} {B : CompleteAlgebraCategory A I}
    (P : NaiveCotangentPresentation A I B) :
    NaiveCotangentConormal P →ₗ[B.obj] NaiveCotangentSpace P :=
  P.extension.cotangentComplex

/-- The two terms, in the source order `(-1, 0)`. -/
abbrev NaiveCotangentTerms
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    {I : Ideal A} {B : CompleteAlgebraCategory A I}
    (P : NaiveCotangentPresentation A I B) : Type _ :=
  NaiveCotangentConormal P × NaiveCotangentSpace P

/-- The degree `-1` cohomology of a presentation complex. -/
abbrev NaiveCotangentHMinusOne
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    {I : Ideal A} {B : CompleteAlgebraCategory A I}
    (P : NaiveCotangentPresentation A I B) : Type _ :=
  P.extension.H1Cotangent

/-- The degree `0` cohomology of a presentation complex. -/
abbrev NaiveCotangentHZero
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    {I : Ideal A} {B : CompleteAlgebraCategory A I}
    (P : NaiveCotangentPresentation A I B) : Type _ :=
  NaiveCotangentSpace P ⧸ LinearMap.range (NaiveCotangentDifferential P)

/-- A homotopy equivalence relation for two-term presentation complexes.

`TwoTermHomotopyData` is the standard chain-homotopy witness used by the
earlier cotangent-complex formalization. -/
def NaiveCotangentHomotopyEquivalent
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    {I : Ideal A} {B : CompleteAlgebraCategory A I}
    (P Q : NaiveCotangentPresentation A I B) : Prop :=
  ∃ H : Formalization.Books.Algebra.Unit134.TwoTermHomotopyData.{u, u, u, u, u}
      B.obj
      (NaiveCotangentConormal P) (NaiveCotangentSpace P)
      (NaiveCotangentConormal Q) (NaiveCotangentSpace Q),
    H.dA = NaiveCotangentDifferential P ∧
      H.dB = NaiveCotangentDifferential Q

/-- The source's morphism of presentations. -/
abbrev PresentationMorphism
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    {I : Ideal A} {B : CompleteAlgebraCategory A I}
    (P Q : NaiveCotangentPresentation A I B) :=
  P.extension.Hom Q.extension

/-- The induced map on the conormal terms. -/
noncomputable def presentationConormalMap
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    {I : Ideal A} {B : CompleteAlgebraCategory A I}
    {P Q : NaiveCotangentPresentation A I B}
    (f : PresentationMorphism P Q) :
    NaiveCotangentConormal P →ₗ[B.obj] NaiveCotangentConormal Q :=
  Algebra.Extension.Cotangent.map f

/-- The induced map on the degree-zero cotangent terms. -/
noncomputable def presentationCotangentSpaceMap
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    {I : Ideal A} {B : CompleteAlgebraCategory A I}
    {P Q : NaiveCotangentPresentation A I B}
    (f : PresentationMorphism P Q) :
    NaiveCotangentSpace P →ₗ[B.obj] NaiveCotangentSpace Q :=
  Algebra.Extension.CotangentSpace.map f

/-- The degree `-1` homotopy operator for two maps of presentations. -/
noncomputable def presentationHomotopy
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    {I : Ideal A} {B : CompleteAlgebraCategory A I}
    {P Q : NaiveCotangentPresentation A I B}
    (f g : PresentationMorphism P Q) :
    NaiveCotangentSpace P →ₗ[B.obj] NaiveCotangentConormal Q :=
  Algebra.Extension.Hom.sub f g

theorem presentation_map_is_a_chain_map
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    {I : Ideal A} {B : CompleteAlgebraCategory A I}
    {P Q : NaiveCotangentPresentation A I B}
    (f : PresentationMorphism P Q) :
    presentationCotangentSpaceMap f ∘ₗ NaiveCotangentDifferential P =
      NaiveCotangentDifferential Q ∘ₗ presentationConormalMap f := by
  exact Algebra.Extension.CotangentSpace.map_comp_cotangentComplex f

theorem presentation_maps_are_homotopic
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    {I : Ideal A} {B : CompleteAlgebraCategory A I}
    {P Q : NaiveCotangentPresentation A I B}
    (f g : PresentationMorphism P Q) :
    presentationCotangentSpaceMap f - presentationCotangentSpaceMap g =
      NaiveCotangentDifferential Q ∘ₗ presentationHomotopy f g := by
  exact Algebra.Extension.CotangentSpace.map_sub_map f g

theorem presentation_conormal_maps_are_homotopic
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    {I : Ideal A} {B : CompleteAlgebraCategory A I}
    {P Q : NaiveCotangentPresentation A I B}
    (f g : PresentationMorphism P Q) :
    presentationConormalMap f - presentationConormalMap g =
      presentationHomotopy f g ∘ₗ NaiveCotangentDifferential P := by
  exact Algebra.Extension.Cotangent.map_sub_map f g

/-- The naive cotangent complex is independent of the chosen presentation
in the homotopy-category sense used by the source. -/
theorem naive_cotangent_well_defined
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    {I : Ideal A} {B : CompleteAlgebraCategory A I}
    (P Q : NaiveCotangentPresentation A I B) :
    NaiveCotangentHomotopyEquivalent P Q := by
  sorry

/-! ## Completion of an ordinary finite-type presentation -/

/-- The completed algebra used in the second lemma. -/
noncomputable def completedFiniteTypeAlgebra
    {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    [IsNoetherianRing A] [Algebra.FiniteType A B] (I : Ideal A) :
    CompleteAlgebraCategory A I :=
  ⟨adicCompletionAlgebra I (CommAlgCat.of A B),
    adicCompletionAlgebra_property I (CommAlgCat.of A B) (by infer_instance)⟩

/-- The ordinary polynomial presentation complex attached to `α`. -/
abbrev OrdinaryNaiveCotangentConormal
    {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    {n : ℕ} (α : MvPolynomial (Fin n) A →ₐ[A] B)
    (hα : Function.Surjective α) : Type _ :=
  (Algebra.Extension.ofSurjective α hα).Cotangent

/-- The degree-zero term of the ordinary polynomial presentation complex. -/
abbrev OrdinaryNaiveCotangentSpace
    {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    {n : ℕ} (α : MvPolynomial (Fin n) A →ₐ[A] B)
    (hα : Function.Surjective α) : Type _ :=
  (Algebra.Extension.ofSurjective α hα).CotangentSpace

/-- The two terms of `NL(α)`, in degrees `-1` and `0`. -/
abbrev OrdinaryNaiveCotangentTerms
    {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    {n : ℕ} (α : MvPolynomial (Fin n) A →ₐ[A] B)
    (hα : Function.Surjective α) : Type _ :=
  OrdinaryNaiveCotangentConormal α hα × OrdinaryNaiveCotangentSpace α hα

/-- The completed presentation induced by an ordinary finite-type map. -/
theorem exists_completed_naive_cotangent_presentation
    {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    [IsNoetherianRing A] [Algebra.FiniteType A B]
    (I : Ideal A) (n : ℕ)
    (α : MvPolynomial (Fin n) A →ₐ[A] B)
    (hα : Function.Surjective α) :
    Nonempty (NaiveCotangentPresentation A I
      (completedFiniteTypeAlgebra (B := B) I)) := by
  sorry

/-- Completion identifies the completed presentation complex with the base
change of the ordinary presentation complex. -/
theorem naive_cotangent_is_completion
    {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    [IsNoetherianRing A] [Algebra.FiniteType A B]
    (I : Ideal A)
    [Algebra B (completedFiniteTypeAlgebra (B := B) I).obj]
    (n : ℕ)
    (α : MvPolynomial (Fin n) A →ₐ[A] B)
    (hα : Function.Surjective α) :
    ∃ P : NaiveCotangentPresentation A I
        (completedFiniteTypeAlgebra (B := B) I),
      Nonempty (NaiveCotangentTerms P ≃ₗ[
        (completedFiniteTypeAlgebra (B := B) I).obj]
        ((completedFiniteTypeAlgebra (B := B) I).obj ⊗[B]
          OrdinaryNaiveCotangentConormal α hα) ×
        ((completedFiniteTypeAlgebra (B := B) I).obj ⊗[B]
          OrdinaryNaiveCotangentSpace α hα)) := by
  sorry

/-! ## Passage to the adic stages and the derived inverse limit -/

/-- The stage rings attached to an object of `𝓒'`. -/
abbrev BaseStage (A : Type u) [CommRing A] (I : Ideal A) (n : ℕ+) : Type u :=
  adicQuotient A I n

abbrev AlgebraStage {A : Type u} [CommRing A] (I : Ideal A)
    (B : CompleteAlgebraCategory A I) (n : ℕ+) : Type u :=
  cprimeQuotientStage I B.obj n

/-- A presentation-level inverse system of naive cotangent complexes. -/
structure NaiveCotangentStageSystem
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    {I : Ideal A} {B : CompleteAlgebraCategory A I}
    (P : NaiveCotangentPresentation A I B) where
  stage : ∀ n : ℕ+, Type u
  transition : ∀ {m n : ℕ+}, n ≤ m → stage m → stage n
  transition_id : ∀ n, transition (m := n) (n := n) le_rfl = id
  transition_comp : ∀ {l m n : ℕ+} (hlm : m ≤ l) (hmn : n ≤ m),
    (transition hmn).comp (transition hlm) = transition (hmn.trans hlm)

/-- Strict isomorphism of the completed and stagewise pro-objects. -/
structure StrictNaiveCotangentProIsomorphism
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    {I : Ideal A} {B : CompleteAlgebraCategory A I}
    (P : NaiveCotangentPresentation A I B)
    (S : NaiveCotangentStageSystem P) where
  forward : ∀ n, NaiveCotangentTerms P → S.stage n
  backward : ∀ n, S.stage n → NaiveCotangentTerms P
  forward_backward : ∀ n x, backward n (forward n x) = x
  backward_forward : ∀ n x, forward n (backward n x) = x

/-- The two pro-objects in the source are strictly isomorphic. -/
theorem naive_cotangent_is_limit_pro_isomorphic
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    {I : Ideal A} {B : CompleteAlgebraCategory A I}
    (P : NaiveCotangentPresentation A I B)
    (S : NaiveCotangentStageSystem P) :
    Nonempty (StrictNaiveCotangentProIsomorphism P S) := by
  sorry

/-- The derived-limit statement for the inverse system of stage complexes. -/
theorem naive_cotangent_is_derived_limit
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    {I : Ideal A} {B : CompleteAlgebraCategory A I}
    (P : NaiveCotangentPresentation A I B)
    (S : NaiveCotangentStageSystem P)
    (hS : Nonempty (StrictNaiveCotangentProIsomorphism P S)) :
    ∃ L : Type u,
      ∀ n, Nonempty (L ≃ S.stage n) := by
  sorry

/-! ## Base change -/

/-- The four maps and their compatibility in the base-change diagram. -/
structure NaiveCotangentBaseChangeData
    {A₁ A₂ : Type u} [CommRing A₁] [CommRing A₂]
    [IsNoetherianRing A₁] [IsNoetherianRing A₂]
    (D : AdicBaseChangeData A₁ A₂)
    {B₁ : CompleteAlgebraCategory A₁ D.I₁}
    {B₂ : CompleteAlgebraCategory A₂ D.I₂}
    (P₁ : NaiveCotangentPresentation A₁ D.I₁ B₁)
    (P₂ : NaiveCotangentPresentation A₂ D.I₂ B₂) where
  conormalMap : NaiveCotangentConormal P₁ → NaiveCotangentConormal P₂
  cotangentSpaceMap : NaiveCotangentSpace P₁ → NaiveCotangentSpace P₂

/-- The base-change map is an isomorphism on `H⁰` and an epimorphism on
`H⁻¹`. -/
structure NaiveCotangentBaseChangeConclusion
    {A₁ A₂ : Type u} [CommRing A₁] [CommRing A₂]
    [IsNoetherianRing A₁] [IsNoetherianRing A₂]
    {D : AdicBaseChangeData A₁ A₂}
    {B₁ : CompleteAlgebraCategory A₁ D.I₁}
    {B₂ : CompleteAlgebraCategory A₂ D.I₂}
    {P₁ : NaiveCotangentPresentation A₁ D.I₁ B₁}
    {P₂ : NaiveCotangentPresentation A₂ D.I₂ B₂}
    (M : NaiveCotangentBaseChangeData D P₁ P₂) where
  hZeroMap : NaiveCotangentHZero P₁ → NaiveCotangentHZero P₂
  hMinusOneMap : NaiveCotangentHMinusOne P₁ → NaiveCotangentHMinusOne P₂
  hZero_is_iso : Function.Bijective hZeroMap
  hMinusOne_surjective : Function.Surjective hMinusOneMap

theorem naive_cotangent_base_change
    {A₁ A₂ : Type u} [CommRing A₁] [CommRing A₂]
    [IsNoetherianRing A₁] [IsNoetherianRing A₂]
    (D : AdicBaseChangeData A₁ A₂)
    {B₁ : CompleteAlgebraCategory A₁ D.I₁}
    {B₂ : CompleteAlgebraCategory A₂ D.I₂}
    (P₁ : NaiveCotangentPresentation A₁ D.I₁ B₁)
    (P₂ : NaiveCotangentPresentation A₂ D.I₂ B₂)
    : ∃ M : NaiveCotangentBaseChangeData D P₁ P₂,
      Nonempty (NaiveCotangentBaseChangeConclusion M) := by
  sorry

/-! ## The six-term exact sequence -/

/-- The intrinsic degree `-1` and degree `0` terms for an arbitrary algebra
map, using the canonical presentation-independent Mathlib construction. -/
abbrev IntrinsicNaiveHMinusOne
    (R S : Type u) [CommRing R] [CommRing S] [Algebra R S] : Type _ :=
  Formalization.Books.Algebra.Unit134.NaiveCotangentH1 R S

abbrev IntrinsicNaiveHZero
    (R S : Type u) [CommRing R] [CommRing S] [Algebra R S] : Type _ :=
  Formalization.Books.Algebra.Unit134.NaiveCotangentCokernel R S

/-- The six maps and exactness assertions in the Jacobi--Zariski diagram. -/
structure SixTermNaiveCotangentExactSequence
    {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra A C] [Algebra B C]
    [IsScalarTower A B C] where
  hZeroBase :
    C ⊗[B] IntrinsicNaiveHZero A B →ₗ[C] IntrinsicNaiveHZero A C
  hZeroRelative :
    IntrinsicNaiveHZero A C →ₗ[C] IntrinsicNaiveHZero B C
  hMinusOneBase :
    C ⊗[B] IntrinsicNaiveHMinusOne A B →ₗ[C]
      IntrinsicNaiveHMinusOne A C
  hMinusOneRelative :
    IntrinsicNaiveHMinusOne A C →ₗ[C] IntrinsicNaiveHMinusOne B C
  connecting :
    IntrinsicNaiveHMinusOne B C →ₗ[C] C ⊗[B] IntrinsicNaiveHZero A B
  exact_hZero : Function.Exact hZeroBase hZeroRelative
  hZero_relative_surjective : Function.Surjective hZeroRelative
  exact_hMinusOne : Function.Exact hMinusOneBase hMinusOneRelative
  exact_connecting : Function.Exact hMinusOneRelative connecting
  exact_at_hZeroBase : Function.Exact connecting hZeroBase

theorem exact_sequence_naive_cotangent
    {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra A C] [Algebra B C]
    [IsScalarTower A B C]
    (hB : IsNoetherianRing B) :
    Nonempty (SixTermNaiveCotangentExactSequence (A := A) (B := B) (C := C)) := by
  sorry

/-! ## The transitive local-complete-intersection injection -/

theorem transitive_lci_naive_cotangent_injective
    {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra A C] [Algebra B C]
    [IsScalarTower A B C]
    (I : Ideal A) (J : Ideal B) (K : Ideal C)
    (stageMap : ∀ n : ℕ+,
      (B ⧸ J ^ (n : ℕ)) →+* (C ⧸ K ^ (n : ℕ)))
    (hlci : ∀ n : ℕ+,
      Formalization.Books.MoreAlgebra.Unit83.IsLocalCompleteIntersectionHom
        (stageMap n)) :
    ∃ f : C ⊗[B] IntrinsicNaiveHMinusOne A B →ₗ[C]
        IntrinsicNaiveHMinusOne A C,
      Function.Injective f := by
  sorry

end

end Formalization.Books.Restricted.Unit03
