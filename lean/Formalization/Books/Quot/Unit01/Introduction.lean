import Formalization.Books.Quot.Unit01.Core

/-!
# Quot and Hilbert Spaces, Chapter 1: Introduction

This section records the mathematical interfaces and theorem statements in the
Introduction.  The proofs belong to the later proving stage.
-/

noncomputable section

open CategoryTheory
open AlgebraicGeometry

namespace Formalization.Books.Quot.Unit01

universe u v

structure CoherentStackFlatHypotheses {X B : Scheme.{u}} (f : X ⟶ B) where
  finitePresentation : IsFinitePresentationMorphism f
  separated : AlgebraicGeometry.IsSeparated f
  flat : AlgebraicGeometry.Flat f

structure CoherentStackGeneralHypotheses {X B : Scheme.{u}} (f : X ⟶ B) where
  finitePresentation : IsFinitePresentationMorphism f
  separated : AlgebraicGeometry.IsSeparated f

def homFunctor {X B : Scheme.{u}} {f : X ⟶ B} {F G : X.Modules}
    (H : RelativeHomFunctorData f F G) : RelativeSetFunctor B :=
  H.value

def isomFunctor {X B : Scheme.{u}} {f : X ⟶ B} {F G : X.Modules}
    (H : RelativeHomFunctorData f F G)
    (I : RelativeIsomFunctorData f F G H) : RelativeSetFunctor B :=
  I.value

def quotFunctor {X B : Scheme.{u}} {f : X ⟶ B} {F : X.Modules}
    (Q : QuotFunctorData f F) : RelativeSetFunctor B :=
  Q.value

def hilbertFunctor {X B : Scheme.{u}} {f : X ⟶ B}
    (H : HilbertFunctorData f) : RelativeSetFunctor B :=
  H.value

def picardFunctor {X B : Scheme.{u}} {f : X ⟶ B}
    (P : PicardFunctorData f) : RelativeSetFunctor B :=
  P.value

def picardStack {X B : Scheme.{u}} {f : X ⟶ B}
    (P : PicardStackData f) : RelativeStack B :=
  P.stack

def relativeMorphismFunctor {Z X B : Scheme.{u}}
    {z : Z ⟶ B} {f : X ⟶ B} (M : RelativeMorphismFunctorData z f) :
    RelativeSetFunctor B :=
  M.value

def coherentSheafStack {X B : Scheme.{u}} {f : X ⟶ B}
    (C : CoherentSheafStackData f) : RelativeStack B :=
  C.stack

def spacesStack {B : Scheme.{u}} (S : SpacesStackData B) : RelativeStack B :=
  S.stack

def polarizedStack {B : Scheme.{u}}
    (P : PolarizedStackData B) : RelativeStack B :=
  P.stack

def curvesStack {B : Scheme.{u}} (C : CurvesStackData B) : RelativeStack B :=
  C.stack

def complexesStack {X B : Scheme.{u}} {f : X ⟶ B}
    (C : ComplexesStackData f) : RelativeStack B :=
  C.stack

/-! ## Projective schemes and the Grassmannian -/

theorem projective_quot_hilbert_inside_grassmannian
    {R : Type u} [CommRing R]
    {M : Type v} [AddCommGroup M] [Module R M] (k : ℕ)
    (Quotient Hilbert : CommAlgCat.{u} R ⥤ Type (max v u))
    (h : ProjectiveGrassmannianHypotheses) :
    Nonempty (ProjectiveQuotHilbertGrassmannianData (R := R) (M := M)
      k Quotient Hilbert) := by
  sorry

/-! ## Hom, Isom, and the coherent-sheaf stack -/

theorem hom_functor_is_algebraic_space
    {X B : Scheme.{u}} (f : X ⟶ B) (F G : X.Modules)
    (h : HomRepresentabilityHypotheses f F G) :
    ∃ H : RelativeHomFunctorData f F G,
      IsAlgebraicSpaceValued (homFunctor H) := by
  sorry

theorem isom_functor_is_algebraic_space
    {X B : Scheme.{u}} (f : X ⟶ B) (F G : X.Modules)
    (h : IsomRepresentabilityHypotheses f F G) :
    ∃ H : RelativeHomFunctorData f F G,
      ∃ I : RelativeIsomFunctorData f F G H,
        IsAlgebraicSpaceValued (isomFunctor H I) := by
  sorry

theorem coherent_stack_diagonal_representable
    {X B : Scheme.{u}} (f : X ⟶ B)
    (C : CoherentSheafStackData f)
    (h : CoherentStackFlatHypotheses f) :
    RelativeDiagonalRepresentable (coherentSheafStack C) := by
  sorry

theorem coherent_stack_is_algebraic_flat
    {X B : Scheme.{u}} (f : X ⟶ B)
    (C : CoherentSheafStackData f)
    (h : CoherentStackFlatHypotheses f) :
    IsAlgebraicRelativeStack (coherentSheafStack C) := by
  sorry

theorem coherent_stack_is_algebraic_general
    {X B : Scheme.{u}} (f : X ⟶ B)
    (C : CoherentSheafStackData f)
    (h : CoherentStackGeneralHypotheses f) :
    IsAlgebraicRelativeStack (coherentSheafStack C) := by
  sorry

/-! ## Quot, Hilbert, Picard, and relative morphism functors -/

theorem quot_functor_is_algebraic_space
    {X B : Scheme.{u}} (f : X ⟶ B) (F : X.Modules)
    (Q : QuotFunctorData f F)
    (h : QuotRepresentabilityHypotheses f F) :
    IsAlgebraicSpaceValued (quotFunctor Q) := by
  sorry

theorem hilbert_functor_is_algebraic_space
    {X B : Scheme.{u}} (f : X ⟶ B)
    (H : HilbertFunctorData f)
    (h : HilbertRepresentabilityHypotheses f) :
    IsAlgebraicSpaceValued (hilbertFunctor H) := by
  sorry

theorem picard_functor_is_algebraic_space
    {X B : Scheme.{u}} (f : X ⟶ B)
    (P : PicardFunctorData f)
    (h : PicardFunctorHypotheses f) :
    IsAlgebraicSpaceValued (picardFunctor P) := by
  sorry

theorem picard_stack_is_algebraic
    {X B : Scheme.{u}} (f : X ⟶ B)
    (P : PicardStackData f)
    (h : PicardStackHypotheses f) :
    IsAlgebraicRelativeStack (picardStack P) := by
  sorry

theorem relative_morphism_functor_is_algebraic_space
    {Z X B : Scheme.{u}} (z : Z ⟶ B) (f : X ⟶ B)
    (M : RelativeMorphismFunctorData z f)
    (h : RelativeMorphismHypotheses z f) :
    IsAlgebraicSpaceValued (relativeMorphismFunctor M) := by
  sorry

/-! ## Spaces, polarized spaces, curves, and complexes -/

theorem flat_proper_spaces_stack_satisfies_artin_axioms
    {B : Scheme.{u}} (S : SpacesStackData B) :
    Nonempty (ArtinAxiomsWithoutFormalEffectiveness (spacesStack S)) := by
  sorry

theorem polarized_stack_is_algebraic
    {B : Scheme.{u}} (P : PolarizedStackData B) :
    IsAlgebraicRelativeStack (polarizedStack P) := by
  sorry

theorem polarized_schemes_are_formally_effective
    {B : Scheme.{u}} (P : PolarizedStackData B) :
    Nonempty (PolarizedFormalEffectivenessData P) := by
  sorry

theorem curves_stack_is_algebraic
    {B : Scheme.{u}} (C : CurvesStackData B) :
    IsAlgebraicRelativeStack (curvesStack C) := by
  sorry

theorem complexes_stack_is_algebraic
    {X B : Scheme.{u}} (f : X ⟶ B)
    (C : ComplexesStackData f)
    (h : ComplexesRepresentabilityHypotheses f) :
    IsAlgebraicRelativeStack (complexesStack C) := by
  sorry

end Formalization.Books.Quot.Unit01
