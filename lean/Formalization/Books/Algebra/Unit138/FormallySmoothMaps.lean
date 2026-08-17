import Formalization.Books.Algebra.Unit03.BasicNotions
import Formalization.Books.Algebra.Unit127.ColimitsAndFinitePresentation
import Formalization.Books.Algebra.Unit137.SmoothRingMaps
import Formalization.Books.Algebra.Unit14.BaseChange
import Mathlib.RingTheory.Etale.Descent
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.RingHom.FaithfullyFlat
import Mathlib.RingTheory.RingHom.Smooth
import Mathlib.RingTheory.Smooth.NoetherianDescent
import Mathlib.RingTheory.Smooth.Quotient

/-!
# Commutative Algebra, Chapter 138: Formally smooth maps

This file records the lifting, cotangent, descent, and exact-sequence
statements in the chapter.  The formal-smooth and smooth predicates are the
canonical `RingHom` predicates, while the extension and filtered-colimit
interfaces reuse Mathlib and the earlier formalization chapters.
-/

namespace Formalization.Books.Algebra.Unit138

open scoped TensorProduct

noncomputable section

universe u v

/-! ## Source-facing interfaces for split sequences and presentations -/

/-- A split short exact sequence of modules, with the splitting written as a
section of the surjection. -/
def IsSplitExactLinearSequence
    {R M N P : Type*} [Semiring R]
    [AddCommMonoid M] [AddCommMonoid N] [AddCommMonoid P]
    [Module R M] [Module R N] [Module R P]
    (f : M →ₗ[R] N) (g : N →ₗ[R] P) : Prop :=
  Function.Injective f ∧ Function.Exact f g ∧ Function.Surjective g ∧
    ∃ s : P →ₗ[R] N, g.comp s = LinearMap.id

/-- A section of the square-zero quotient attached to an algebra extension.
The kernel in the quotient is the kernel of the extension map. -/
def extensionHasSection
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    (P : Algebra.Extension R S) : Prop :=
  ∃ σ : S →ₐ[R]
      P.Ring ⧸ (RingHom.ker (IsScalarTower.toAlgHom R P.Ring S).toRingHom ^ 2),
    (IsScalarTower.toAlgHom R P.Ring S).kerSquareLift.comp σ =
      AlgHom.id R S

/-- The conormal--cotangent--differential sequence attached to an extension
is split exact. -/
def extensionDifferentialSplitExact
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    (P : Algebra.Extension R S) : Prop :=
  IsSplitExactLinearSequence P.cotangentComplex P.toKaehler

/-- The presentation-independent cotangent criterion for formal smoothness. -/
def formalSmoothCotangentCriterion
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] : Prop :=
  Subsingleton (Algebra.H1Cotangent R S) ∧
    Module.Projective S
      (Formalization.Books.Algebra.Unit131.ModuleOfDifferentials R S)

/-! The quotient and filtered-colimit constructions used by later statements. -/

/-- The map on quotients induced by extending an ideal along a ring map. -/
noncomputable def quotientBaseChangeRingMap
    {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (I : Ideal R) :
    R ⧸ I →+* S ⧸ Ideal.map f I :=
  Ideal.quotientMap (Ideal.map f I) f Ideal.le_comap_map

/-- The extension of `A → B → C` determined by a surjection `B → C`. -/
noncomputable def surjectiveExtensionOver
    {A B C : Type*} [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra A C] [Algebra B C] [IsScalarTower A B C]
    (h : Function.Surjective (algebraMap B C)) :
    Algebra.Extension A C :=
  Algebra.Extension.ofSurjective (IsScalarTower.toAlgHom A B C) h

/-- The tensor product appearing when a stage of a directed system of ring
maps is base changed to the represented source ring. -/
abbrev directedStageBaseChangeRing
    {R S : Type u} [CommRing R] [CommRing S] {f : R →+* S}
    (D : Formalization.Books.Algebra.Unit127.DirectedRingMapColimit f)
    (i : D.index) : Type u :=
  letI : Preorder D.index := D.indexPreorder
  letI : Algebra (D.sourceDiagram.obj i) (D.targetDiagram.obj i) :=
    (D.stageMap i).toAlgebra
  letI : Algebra (D.sourceDiagram.obj i) R :=
    (D.sourceStageToTarget i).toAlgebra
  D.targetDiagram.obj i ⊗[D.sourceDiagram.obj i] R

/-! ## Formally smooth maps and presentations -/

theorem formallySmooth_iff_lifting
    {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    (f : R →+* S) :
    letI : Algebra R S := f.toAlgebra
    f.FormallySmooth ↔
      ∀ ⦃A : Type max u v⦄ [CommRing A] [Algebra R A]
        (I : Ideal A), I ^ 2 = ⊥ →
          Function.Surjective
            ((Ideal.Quotient.mkₐ R I).comp :
              (S →ₐ[R] A) → S →ₐ[R] A ⧸ I) := by
  sorry

theorem formallySmooth_baseChange
    {R S R' : Type*} [CommRing R] [CommRing S] [CommRing R']
    (f : R →+* S) (g : R →+* R') (hf : f.FormallySmooth) :
    (Formalization.Books.Algebra.Unit14.baseChangeRingMap f g).FormallySmooth := by
  sorry

theorem formallySmooth_comp
    {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
    (f : R →+* S) (g : S →+* T)
    (hf : f.FormallySmooth) (hg : g.FormallySmooth) :
    (g.comp f).FormallySmooth := by
  exact hf.comp hg

theorem polynomialRing_formallySmooth
    {R : Type u} [CommRing R] (ι : Type v) :
    (algebraMap R (MvPolynomial ι R)).FormallySmooth := by
  exact RingHom.formallySmooth_algebraMap.mpr inferInstance

theorem formallySmooth_iff_extension_section
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    (P : Algebra.Extension.{u} R S)
    [Algebra.FormallySmooth R P.Ring] :
    Algebra.FormallySmooth R S ↔ extensionHasSection P := by
  sorry

theorem formallySmooth_iff_presentation_section
    {R S ι : Type*} [CommRing R] [CommRing S] [Algebra R S]
    (P : Formalization.Books.Algebra.Unit134.Presentation R S ι)
    [Algebra.FormallySmooth R P.Ring] :
    Algebra.FormallySmooth R S ↔ extensionHasSection P.toExtension := by
  sorry

theorem formallySmooth_iff_presentation_split_exact
    {R S ι : Type*} [CommRing R] [CommRing S] [Algebra R S]
    (P : Formalization.Books.Algebra.Unit134.Presentation R S ι)
    [Algebra.FormallySmooth R P.Ring] :
    Algebra.FormallySmooth R S ↔ extensionDifferentialSplitExact P.toExtension := by
  sorry

theorem formallySmooth_iff_cotangent_criterion
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] :
    Algebra.FormallySmooth R S ↔ formalSmoothCotangentCriterion (R := R) (S := S) := by
  sorry

theorem formallySmooth_presentation_characterization
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S] :
    List.TFAE
      [ Algebra.FormallySmooth R S,
        ∃ P : Algebra.Extension.{u} R S,
          Algebra.FormallySmooth R P.Ring ∧ extensionHasSection P,
        ∀ P : Algebra.Extension.{u} R S,
          Algebra.FormallySmooth R P.Ring → extensionHasSection P,
        ∃ P : Algebra.Extension.{u} R S,
          Algebra.FormallySmooth R P.Ring ∧ extensionDifferentialSplitExact P,
        ∀ P : Algebra.Extension.{u} R S,
          Algebra.FormallySmooth R P.Ring → extensionDifferentialSplitExact P,
        formalSmoothCotangentCriterion (R := R) (S := S) ] := by
  sorry

/-! ## Differential sequences -/

theorem ses_formallySmooth
    {A B C : Type*} [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra A C] [Algebra B C] [IsScalarTower A B C]
    (hBC : Algebra.FormallySmooth B C) :
    IsSplitExactLinearSequence
      (KaehlerDifferential.mapBaseChange A B C)
      (KaehlerDifferential.map A B C C) := by
  sorry

theorem differential_seq_formallySmooth
    {A B C : Type*} [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra A C] [Algebra B C] [IsScalarTower A B C]
    (hAC : Algebra.FormallySmooth A C)
    (hBC : Function.Surjective (algebraMap B C)) :
    extensionDifferentialSplitExact (surjectiveExtensionOver (A := A) hBC) := by
  sorry

theorem surjective_of_composite_algebraMap
    {A B C : Type*} [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra A C] [Algebra B C] [IsScalarTower A B C]
    (hAC : Function.Surjective (algebraMap A C)) :
    Function.Surjective (algebraMap B C) := by
  sorry

theorem application_NL_formallySmooth
    {A B C : Type*} [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra A C] [Algebra B C] [IsScalarTower A B C]
    (hAC : Function.Surjective (algebraMap A C))
    (hAB : Algebra.FormallySmooth A B) :
    ∃ d :
        (Formalization.Books.Algebra.Unit134.surjectiveExtension
            (surjective_of_composite_algebraMap (B := B) hAC)).Cotangent →ₗ[C]
          C ⊗[B] Formalization.Books.Algebra.Unit131.ModuleOfDifferentials A B,
      IsSplitExactLinearSequence
        (Algebra.Extension.Cotangent.map
          (Formalization.Books.Algebra.Unit134.surjectiveExtensionHom hAC
            (surjective_of_composite_algebraMap (B := B) hAC))) d := by
  sorry

/-! ## Square-zero lifting and smoothness -/

theorem formallySmooth_of_squareZero_flat
    {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (I : Ideal R) (hI : I ^ 2 = ⊥)
    (hflat : f.Flat)
    (hquot : (quotientBaseChangeRingMap f I).FormallySmooth) :
    f.FormallySmooth := by
  sorry

theorem smooth_iff_formallySmooth_and_finitePresentation
    {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) :
    f.Smooth ↔ f.FormallySmooth ∧ f.FinitePresentation :=
  RingHom.smooth_def

theorem smooth_finite_type_descent
    {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S)
    (hf : f.Smooth) :
    letI : Algebra R S := f.toAlgebra
    ∃ (R₀ : Type u) (S₀ : Type u) (_ : CommRing R₀) (_ : CommRing S₀)
      (_ : Algebra ℤ R₀) (_ : Algebra R₀ R) (_ : Algebra R₀ S₀),
      Function.Injective (algebraMap R₀ R) ∧
        Algebra.FiniteType ℤ R₀ ∧ Algebra.Smooth R₀ S₀ ∧
          Nonempty (S ≃ₐ[R] R ⊗[R₀] S₀) := by
  exact
    letI : Algebra R S := f.toAlgebra
    letI : Algebra.Smooth R S := hf.toAlgebra
    Algebra.Smooth.exists_finiteType ℤ R S

theorem smooth_descends_through_colimit
    {A B : Type u} [CommRing A] [CommRing B] (f : A →+* B)
    (D : Formalization.Books.Algebra.Unit127.DirectedRingMapColimit f)
    (hf : f.Smooth) :
    ∃ i : D.index,
      (D.stageMap i).Smooth ∧
        Nonempty (directedStageBaseChangeRing D i ≃+* B) := by
  sorry

theorem formallySmooth_iff_faithfullyFlat_baseChange
    {R S R' : Type*} [CommRing R] [CommRing S] [CommRing R']
    (f : R →+* S) (g : R →+* R') (hff : g.FaithfullyFlat) :
    f.FormallySmooth ↔
      (Formalization.Books.Algebra.Unit14.baseChangeRingMap f g).FormallySmooth := by
  sorry

theorem smooth_strong_lift
    {R S A : Type*} [CommRing R] [CommRing S] [CommRing A]
    [Algebra R A] (f : R →+* S) (hf : f.Smooth) :
    letI : Algebra R S := f.toAlgebra
    ∀ (I : Ideal A),
      Formalization.Books.Algebra.Unit03.locallyNilpotentIdeal I →
        ∀ (g : S →ₐ[R] A ⧸ I),
          ∃ lift : S →ₐ[R] A,
            (Ideal.Quotient.mkₐ R I).comp lift = g := by
  sorry

end

end Formalization.Books.Algebra.Unit138
