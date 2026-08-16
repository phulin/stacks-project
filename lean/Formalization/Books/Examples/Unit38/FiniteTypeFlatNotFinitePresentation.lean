import Mathlib.AlgebraicGeometry.Fiber
import Mathlib.AlgebraicGeometry.Geometrically.Connected
import Mathlib.AlgebraicGeometry.Geometrically.Irreducible
import Mathlib.AlgebraicGeometry.Geometrically.Reduced
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Proper
import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.Algebra.DirectSum.Module
import Mathlib.Algebra.TrivSqZeroExt.Basic
import Mathlib.LinearAlgebra.SymmetricAlgebra.Basis
import Mathlib.RingTheory.FiniteType
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.Ideal.Pure
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.KrullDimension.Basic
import Mathlib.RingTheory.LocalRing.ResidueField.Fiber
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.RingTheory.Regular.RegularSequence

/-!
# Examples, Chapter 38: Finite type, flat and not of finite presentation

This file records the constructions and theorem interfaces in the source
section.  The quotient, tensor-product fibre, square-zero extension, symmetric
algebra, and projective-spectrum objects use Mathlib's canonical definitions.
The two relative Proj presentations are explicit interfaces for the grading
on a quotient and on a symmetric algebra; Mathlib currently does not expose a
quotient-grading or symmetric-algebra-grading constructor.
-/

noncomputable section

universe u

open CategoryTheory
open AlgebraicGeometry
open scoped DirectSum

namespace Formalization.Books.Examples.Unit38

variable {R : Type u} [CommRing R]

/-! ## The ring and ideal assumed throughout the chapter -/

/-- A ring with an ideal whose quotient is finite flat but not projective. -/
structure FiniteFlatNonProjectiveIdeal (R : Type u) [CommRing R] where
  ideal : Ideal R
  quotient_finite : Module.Finite R (R ⧸ ideal)
  quotient_flat : Module.Flat R (R ⧸ ideal)
  quotient_not_projective : ¬ Module.Projective R (R ⧸ ideal)

/-- The base scheme `S = Spec(R)`. -/
abbrev baseScheme (R : Type u) [CommRing R] : Scheme :=
  Spec (CommRingCat.of R)

/-- The ideal in the source's standing ring. -/
abbrev baseIdeal (d : FiniteFlatNonProjectiveIdeal R) : Ideal R :=
  d.ideal

/-- The quotient module is not represented by a finitely generated ideal. -/
theorem FiniteFlatNonProjectiveIdeal.ideal_not_finitely_generated
    (d : FiniteFlatNonProjectiveIdeal R) :
    ¬ d.ideal.FG := by
  sorry

/-- The source identity `I = I²`, obtained from Mathlib's pure-ideal theorem. -/
theorem FiniteFlatNonProjectiveIdeal.ideal_eq_sq
    (d : FiniteFlatNonProjectiveIdeal R) :
    d.ideal = d.ideal ^ 2 := by
  simpa [pow_two] using
    (@Ideal.isIdempotentElem_of_pure R _ d.ideal d.quotient_flat).symm

/-! ## The finite flat square-zero extension -/

/-- The trivial square-zero extension `R ⊕ (R/I)ε`, with `ε² = 0`. -/
abbrev dualNumberExtension (d : FiniteFlatNonProjectiveIdeal R) :=
  TrivSqZeroExt R (R ⧸ d.ideal)

/-- The inclusion `R → R ⊕ (R/I)ε`. -/
noncomputable def dualNumberExtensionMap
    (d : FiniteFlatNonProjectiveIdeal R) :
    R →+* dualNumberExtension d :=
  TrivSqZeroExt.inlHom R (R ⧸ d.ideal)

/-- The corresponding affine scheme morphism. -/
noncomputable def dualNumberExtensionSchemeMap
    (d : FiniteFlatNonProjectiveIdeal R) :
    Spec (CommRingCat.of (dualNumberExtension d)) ⟶ baseScheme R :=
  Spec.map (CommRingCat.ofHom (dualNumberExtensionMap d))

/-- The square-zero extension is finite and flat but not of finite presentation. -/
theorem dualNumberExtension_finite_flat_not_finite_presentation
    (d : FiniteFlatNonProjectiveIdeal R) :
    Module.Finite R (dualNumberExtension d) ∧
      Module.Flat R (dualNumberExtension d) ∧
      ¬ Module.FinitePresentation R (dualNumberExtension d) := by
  sorry

/-! ## Fibre rings and complete intersections -/

/-- A polynomial regular-sequence presentation of a commutative ring.

This is the standard presentation-level notion needed for the source's
complete-intersection fibre assertions; Mathlib has the regular-sequence API
but no standalone complete-intersection ring predicate. -/
structure CompleteIntersectionPresentation (A : Type u) [CommRing A] where
  coefficientField : Type u
  [coefficientField_field : Field coefficientField]
  variableCount : ℕ
  relations : List (MvPolynomial (Fin variableCount) coefficientField)
  ringEquiv :
    A ≃+* MvPolynomial (Fin variableCount) coefficientField ⧸
      Ideal.ofList relations
  regular :
    RingTheory.Sequence.IsRegular
      (MvPolynomial (Fin variableCount) coefficientField) relations

/-- A ring admitting a finite regular-sequence presentation over a field. -/
def IsCompleteIntersectionRing (A : Type u) [CommRing A] : Prop :=
  Nonempty (CompleteIntersectionPresentation A)

/-- The canonical residue-field-to-fibre ring map. -/
noncomputable def residueFieldToFibreMap
    (R A : Type u) [CommRing R] [CommRing A] [Algebra R A]
    (p : PrimeSpectrum R) :
    p.asIdeal.ResidueField →+* p.asIdeal.Fiber A :=
  Algebra.TensorProduct.includeLeftRingHom

/-- The affine scheme map from a canonical residue-field fibre ring. -/
noncomputable def residueFieldFibreSchemeMap
    (R A : Type u) [CommRing R] [CommRing A] [Algebra R A]
    (p : PrimeSpectrum R) :
    Spec (CommRingCat.of (p.asIdeal.Fiber A)) ⟶
      Spec (CommRingCat.of p.asIdeal.ResidueField) :=
  Spec.map (CommRingCat.ofHom (residueFieldToFibreMap R A p))

/-- The square-zero extension has complete-intersection, geometrically
irreducible fibre rings. -/
theorem dualNumberExtension_fibre_properties
    (d : FiniteFlatNonProjectiveIdeal R) :
    ∀ p : PrimeSpectrum R,
      IsCompleteIntersectionRing
          (p.asIdeal.Fiber (dualNumberExtension d)) ∧
        GeometricallyIrreducible
          (residueFieldFibreSchemeMap R (dualNumberExtension d) p) := by
  sorry

/-! ## The affine quotient example -/

/-- The ideal `(xy, a y; a ∈ I)` in `R[x,y]`. -/
def affineExampleIdeal (R : Type u) [CommRing R] (I : Ideal R) :
    Ideal (MvPolynomial (Fin 2) R) :=
  Ideal.span
    ({MvPolynomial.X (0 : Fin 2) * MvPolynomial.X (1 : Fin 2)} ∪
      Set.range (fun a : I ↦
        MvPolynomial.C (a : R) * MvPolynomial.X (1 : Fin 2)))

/-- The quotient ring `A = R[x,y]/(xy, ay; a ∈ I)`. -/
abbrev affineExampleRing (R : Type u) [CommRing R] (I : Ideal R) :=
  MvPolynomial (Fin 2) R ⧸ affineExampleIdeal R I

/-- The structure map `R → A`. -/
noncomputable def affineExampleRingMap
    (R : Type u) [CommRing R] (I : Ideal R) :
  R →+* affineExampleRing R I :=
  algebraMap R (affineExampleRing R I)

/-- The affine scheme morphism attached to `R → A`. -/
noncomputable def affineExampleSchemeMap
    (R : Type u) [CommRing R] (I : Ideal R) :
    Spec (CommRingCat.of (affineExampleRing R I)) ⟶ baseScheme R :=
  Spec.map (CommRingCat.ofHom (affineExampleRingMap R I))

/-- The module on the right side of the source's displayed decomposition.

The product of the two direct sums is the usual direct-sum decomposition
written with two named blocks. -/
abbrev affineExampleModuleDecompositionTarget
    (R : Type u) [CommRing R] (I : Ideal R) :=
  (⨁ _ : ℕ, R) ×
    (⨁ _ : {j : ℕ // 0 < j}, R ⧸ I)

/-- The source's `R`-module decomposition of `A`. -/
theorem affineExample_as_module
    (R : Type u) [CommRing R] (I : Ideal R) :
    Nonempty
      (affineExampleRing R I ≃ₗ[R]
        affineExampleModuleDecompositionTarget R I) := by
  sorry

/-- The affine quotient map is flat and of finite type, but not of finite
presentation. -/
theorem affineExample_flat_finite_type_not_finite_presentation
    (R : Type u) [CommRing R] (I : Ideal R) :
    Algebra.FiniteType R (affineExampleRing R I) ∧
      Module.Flat R (affineExampleRing R I) ∧
      ¬ Module.FinitePresentation R (affineExampleRing R I) := by
  sorry

/-- The two fibre-ring alternatives in the affine example. -/
def IsRingIsoToEither (A B C : Type u) [CommRing A] [CommRing B] [CommRing C] : Prop :=
  Nonempty (A ≃+* B) ∨ Nonempty (A ≃+* C)

/-- The scheme-level version of `IsRingIsoToEither`. -/
def IsSchemeIsoToEither (X Y Z : Scheme.{u}) : Prop :=
  Nonempty (X ≅ Y) ∨ Nonempty (X ≅ Z)

/-- The nodal and affine-line fibre rings over a field. -/
abbrev affineNodeFibreRing (k : Type u) [CommRing k] :=
  MvPolynomial (Fin 2) k ⧸
    Ideal.span
      ({MvPolynomial.X (0 : Fin 2) * MvPolynomial.X (1 : Fin 2)} :
        Set (MvPolynomial (Fin 2) k))

abbrev affineLineFibreRing (k : Type u) [CommRing k] :=
  Polynomial k

/-- Every affine fibre is `κ(p)[x,y]/(xy)` or `κ(p)[x]`. -/
theorem affineExample_fibre_ring_alternatives
    (R : Type u) [CommRing R] (I : Ideal R) :
    ∀ p : PrimeSpectrum R,
      IsRingIsoToEither
        (p.asIdeal.Fiber (affineExampleRing R I))
        (affineNodeFibreRing p.asIdeal.ResidueField)
        (affineLineFibreRing p.asIdeal.ResidueField) := by
  sorry

/-- The affine fibres are geometrically connected, geometrically reduced,
one-dimensional, and complete intersections. -/
theorem affineExample_fibre_properties
    (R : Type u) [CommRing R] (I : Ideal R) :
    ∀ p : PrimeSpectrum R,
      GeometricallyConnected
          (residueFieldFibreSchemeMap R (affineExampleRing R I) p) ∧
        GeometricallyReduced
          (residueFieldFibreSchemeMap R (affineExampleRing R I) p) ∧
        ringKrullDim (p.asIdeal.Fiber (affineExampleRing R I)) = 1 ∧
        IsCompleteIntersectionRing
          (p.asIdeal.Fiber (affineExampleRing R I)) := by
  sorry

/-! ## A projective nodal-family interface -/

/-- The ideal `(X₁X₂, aX₂; a ∈ I)` in `R[X₀,X₁,X₂]`. -/
def projectiveExampleIdeal (R : Type u) [CommRing R] (I : Ideal R) :
    Ideal (MvPolynomial (Fin 3) R) :=
  Ideal.span
    ({MvPolynomial.X (1 : Fin 3) * MvPolynomial.X (2 : Fin 3)} ∪
      Set.range (fun a : I ↦
        MvPolynomial.C (a : R) * MvPolynomial.X (2 : Fin 3)))

/-- The projective coordinate ring
`B = R[X₀,X₁,X₂]/(X₁X₂, aX₂; a ∈ I)`. -/
abbrev projectiveExampleRing (R : Type u) [CommRing R] (I : Ideal R) :=
  MvPolynomial (Fin 3) R ⧸ projectiveExampleIdeal R I

/-- A graded presentation whose degree-zero part is identified with `R`.

The extra grading data is the precise interface needed to apply Mathlib's
canonical `Proj` construction. -/
structure RelativeProjPresentation (R A : Type u) [CommRing R] [CommRing A]
    [Algebra R A] where
  gradedPieces : ℕ → Submodule R A
  graded : GradedRing gradedPieces
  degreeZeroEquiv : (gradedPieces 0) ≃ₐ[R] R

/-- The projective spectrum of a relative Proj presentation. -/
noncomputable def relativeProjScheme
    {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
    (P : RelativeProjPresentation R A) : Scheme :=
  letI : GradedRing P.gradedPieces := P.graded
  AlgebraicGeometry.«Proj» P.gradedPieces

/-- The relative Proj morphism to `Spec(R)`. -/
noncomputable def relativeProjMap
    {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
    (P : RelativeProjPresentation R A) :
    relativeProjScheme P ⟶ baseScheme R :=
  letI : GradedRing P.gradedPieces := P.graded
  AlgebraicGeometry.Proj.toSpecZero P.gradedPieces ≫
    Spec.map (CommRingCat.ofHom P.degreeZeroEquiv.symm.toRingEquiv.toRingHom)

/-- Existence of the natural grading on the projective nodal quotient.

This is a bridge theorem for the missing quotient-grading constructor in the
current Mathlib API. -/
theorem projectiveExample_presentation_exists
    (R : Type u) [CommRing R] (I : Ideal R) :
    Nonempty (RelativeProjPresentation R (projectiveExampleRing R I)) := by
  sorry

/-- A chosen natural graded presentation of the projective nodal quotient. -/
noncomputable def projectiveExamplePresentation
    (R : Type u) [CommRing R] (I : Ideal R) :
    RelativeProjPresentation R (projectiveExampleRing R I) :=
  Classical.choice (projectiveExample_presentation_exists R I)

/-- The projective nodal family `X = Proj(B) → Spec(R)`. -/
noncomputable def projectiveExampleScheme
    (R : Type u) [CommRing R] (I : Ideal R) : Scheme :=
  relativeProjScheme (projectiveExamplePresentation R I)

noncomputable def projectiveExampleSchemeMap
    (R : Type u) [CommRing R] (I : Ideal R) :
    projectiveExampleScheme R I ⟶ baseScheme R :=
  relativeProjMap (projectiveExamplePresentation R I)

/-- The projective nodal family is proper and flat but not of finite
presentation. -/
theorem projectiveExample_proper_flat_not_finite_presentation
    (R : Type u) [CommRing R] (I : Ideal R) :
    IsProper (projectiveExampleSchemeMap R I) ∧
      Flat (projectiveExampleSchemeMap R I) ∧
      ¬ LocallyOfFinitePresentation (projectiveExampleSchemeMap R I) := by
  sorry

/-! ## Projective fibre models -/

/-- The projective spectrum of `k[X₀,…,Xₙ]` with its standard grading. -/
noncomputable def projectiveSpace (k : Type u) [Field k] (n : ℕ) : Scheme :=
  letI : GradedAlgebra (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k) :=
    MvPolynomial.gradedAlgebra
  AlgebraicGeometry.«Proj»
    (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k)

abbrev projectiveLine (k : Type u) [Field k] : Scheme :=
  projectiveSpace k 1

abbrev projectivePlane (k : Type u) [Field k] : Scheme :=
  projectiveSpace k 2

/-- The fibre ring for the projective nodal curve, with equation `X₁X₂ = 0`. -/
abbrev projectiveNodeFibreRing (k : Type u) [Field k] :=
  MvPolynomial (Fin 3) k ⧸
    Ideal.span
      ({MvPolynomial.X (1 : Fin 3) * MvPolynomial.X (2 : Fin 3)} :
        Set (MvPolynomial (Fin 3) k))

/-- Existence of the standard grading on the projective nodal fibre ring. -/
theorem projectiveNodeFibre_presentation_exists
    (k : Type u) [Field k] :
    Nonempty (RelativeProjPresentation k (projectiveNodeFibreRing k)) := by
  sorry

noncomputable def projectiveNodeFibrePresentation
    (k : Type u) [Field k] :
    RelativeProjPresentation k (projectiveNodeFibreRing k) :=
  Classical.choice (projectiveNodeFibre_presentation_exists k)

/-- The closed subscheme of `P²` defined by `X₁X₂ = 0`. -/
noncomputable def projectiveNodeFibreScheme (k : Type u) [Field k] : Scheme :=
  relativeProjScheme (projectiveNodeFibrePresentation k)

/-- A source-facing nodal-curve predicate.  Its displayed model is the
projective equation `X₁X₂ = 0`; this is the chapter's arithmetic-genus-zero
nodal curve description. -/
def IsProjectiveNodalCurve (X : Scheme.{u}) : Prop :=
  ∃ (k : Type u) (h : Field k),
    Nonempty (X ≅ @projectiveNodeFibreScheme k h)

/-- The explicit projective nodal model satisfies the nodal-curve predicate. -/
theorem projectiveNodeFibre_is_nodal_curve
    (k : Type u) [Field k] :
    IsProjectiveNodalCurve (projectiveNodeFibreScheme k) := by
  exact ⟨k, inferInstance, ⟨Iso.refl _⟩⟩

/-- Every fibre of the projective nodal family is `P¹` or the projective nodal
curve cut out by `X₁X₂`. -/
theorem projectiveExample_fibre_alternatives
    (R : Type u) [CommRing R] (I : Ideal R) :
    ∀ s : baseScheme R,
      IsSchemeIsoToEither
        ((projectiveExampleSchemeMap R I).fiber s)
        (projectiveLine ((baseScheme R).residueField s))
        (projectiveNodeFibreScheme ((baseScheme R).residueField s)) := by
  sorry

/-! ## The symmetric-algebra projective example -/

/-- The module `M = R ⊕ R ⊕ R/I`. -/
abbrev symmetricExampleModule (R : Type u) [CommRing R] (I : Ideal R) :=
  R × R × (R ⧸ I)

/-- The symmetric algebra `B = Sym_R(M)`. -/
abbrev symmetricExampleAlgebra (R : Type u) [CommRing R] (I : Ideal R) :=
  SymmetricAlgebra R (symmetricExampleModule R I)

/-- Existence of the standard grading on the symmetric algebra.

Mathlib provides the symmetric algebra and its universal map, but currently
does not expose its canonical internal grading as a `GradedAlgebra`; this
named interface records that missing construction. -/
theorem symmetricExample_presentation_exists
    (R : Type u) [CommRing R] (I : Ideal R) :
    Nonempty (RelativeProjPresentation R (symmetricExampleAlgebra R I)) := by
  sorry

noncomputable def symmetricExamplePresentation
    (R : Type u) [CommRing R] (I : Ideal R) :
    RelativeProjPresentation R (symmetricExampleAlgebra R I) :=
  Classical.choice (symmetricExample_presentation_exists R I)

/-- The symmetric-algebra projective family `Proj(Sym_R(M)) → Spec(R)`. -/
noncomputable def symmetricExampleScheme
    (R : Type u) [CommRing R] (I : Ideal R) : Scheme :=
  relativeProjScheme (symmetricExamplePresentation R I)

noncomputable def symmetricExampleSchemeMap
    (R : Type u) [CommRing R] (I : Ideal R) :
    symmetricExampleScheme R I ⟶ baseScheme R :=
  relativeProjMap (symmetricExamplePresentation R I)

/-- The symmetric-algebra projective family is proper and flat but not of
finite presentation. -/
theorem symmetricExample_proper_flat_not_finite_presentation
    (R : Type u) [CommRing R] (I : Ideal R) :
    IsProper (symmetricExampleSchemeMap R I) ∧
      Flat (symmetricExampleSchemeMap R I) ∧
      ¬ LocallyOfFinitePresentation (symmetricExampleSchemeMap R I) := by
  sorry

/-- Each residue-field fibre is `P¹` or `P²`. -/
theorem symmetricExample_fibre_alternatives
    (R : Type u) [CommRing R] (I : Ideal R) :
    ∀ s : baseScheme R,
      IsSchemeIsoToEither
        ((symmetricExampleSchemeMap R I).fiber s)
        (projectiveLine ((baseScheme R).residueField s))
        (projectivePlane ((baseScheme R).residueField s)) := by
  sorry

/-- The residue-field fibres of the symmetric-algebra family are smooth. -/
theorem symmetricExample_fibres_smooth
    (R : Type u) [CommRing R] (I : Ideal R) :
    ∀ s : baseScheme R,
      Smooth ((symmetricExampleSchemeMap R I).fiberToSpecResidueField s) := by
  sorry

/-- The symmetric-algebra family has geometrically irreducible fibres. -/
theorem symmetricExample_geometrically_irreducible
    (R : Type u) [CommRing R] (I : Ideal R) :
    GeometricallyIrreducible (symmetricExampleSchemeMap R I) := by
  sorry

/-- The smoothness and geometric irreducibility conclusions for the displayed
fibre alternatives. -/
theorem symmetricExample_fibre_geometric_properties
    (R : Type u) [CommRing R] (I : Ideal R) :
    ∀ s : baseScheme R,
      Smooth ((symmetricExampleSchemeMap R I).fiberToSpecResidueField s) ∧
        GeometricallyIrreducible
          ((symmetricExampleSchemeMap R I).fiberToSpecResidueField s) := by
  sorry

/-! ## The four-part existence lemma -/

/- The four witnesses below are the source-order instances used in the final lemma. -/

/-- The ring-level property used by the first item of the final lemma. -/
def FiniteFlatNotFinitePresentation (R A : Type u)
    [CommRing R] [CommRing A] [Algebra R A] : Prop :=
  Module.Finite R A ∧ Module.Flat R A ∧ ¬ Module.FinitePresentation R A

/-- The ring-level property used by the second item of the final lemma. -/
def FlatFiniteTypeNotFinitePresentation (R A : Type u)
    [CommRing R] [CommRing A] [Algebra R A] : Prop :=
  Algebra.FiniteType R A ∧ Module.Flat R A ∧ ¬ Module.FinitePresentation R A

/-- The scheme-level property used by the last two items. -/
def ProperFlatNotFinitePresentation {X Y : Scheme.{u}} (f : X ⟶ Y) : Prop :=
  IsProper f ∧ Flat f ∧ ¬ LocallyOfFinitePresentation f

/-- The four examples asserted by the chapter's final lemma. -/
theorem finiteTypeFlatNotFinitePresentation_exists
    (d : FiniteFlatNonProjectiveIdeal R) :
    (FiniteFlatNotFinitePresentation R (dualNumberExtension d) ∧
        ∀ p : PrimeSpectrum R,
          IsCompleteIntersectionRing
              (p.asIdeal.Fiber (dualNumberExtension d)) ∧
            GeometricallyIrreducible
              (residueFieldFibreSchemeMap R (dualNumberExtension d) p)) ∧
      (FlatFiniteTypeNotFinitePresentation R (affineExampleRing R d.ideal) ∧
        ∀ p : PrimeSpectrum R,
          GeometricallyConnected
              (residueFieldFibreSchemeMap R (affineExampleRing R d.ideal) p) ∧
            GeometricallyReduced
              (residueFieldFibreSchemeMap R (affineExampleRing R d.ideal) p) ∧
            ringKrullDim (p.asIdeal.Fiber (affineExampleRing R d.ideal)) = 1 ∧
            IsCompleteIntersectionRing
              (p.asIdeal.Fiber (affineExampleRing R d.ideal))) ∧
      (ProperFlatNotFinitePresentation (projectiveExampleSchemeMap R d.ideal) ∧
        ∀ s : baseScheme R,
          IsSchemeIsoToEither
            ((projectiveExampleSchemeMap R d.ideal).fiber s)
            (projectiveLine ((baseScheme R).residueField s))
            (projectiveNodeFibreScheme ((baseScheme R).residueField s))) ∧
      (ProperFlatNotFinitePresentation (symmetricExampleSchemeMap R d.ideal) ∧
        ∀ s : baseScheme R,
          IsSchemeIsoToEither
              ((symmetricExampleSchemeMap R d.ideal).fiber s)
              (projectiveLine ((baseScheme R).residueField s))
              (projectivePlane ((baseScheme R).residueField s)) ∧
            Smooth ((symmetricExampleSchemeMap R d.ideal).fiberToSpecResidueField s) ∧
            GeometricallyIrreducible
              ((symmetricExampleSchemeMap R d.ideal).fiberToSpecResidueField s)) := by
  sorry

end Formalization.Books.Examples.Unit38
