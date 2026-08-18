import Formalization.Books.Categories.Unit03.Opposite
import Formalization.Books.Dga.Unit25.Core
import Formalization.Books.Homology.Unit17.AdditiveMonoidalCategories
import Mathlib.CategoryTheory.GradedObject.Single
import Mathlib.CategoryTheory.Monoidal.Braided.Basic

/-!
# Weil Cohomology Theories, Chapter 1: Introduction

This file records the categorical interfaces announced in the introduction.
The carrier of `C` is the category of smooth projective schemes over a base
field, and the carrier of `M` is the corresponding category of Chow motives;
the concrete scheme, correspondence, Chow-group, and cycle-class
constructions are developed in the later sections of the book.

The introduction's Künneth, Poincaré-duality, and cycle-class requirements
are deliberately not replaced here by unconstrained propositions.  Their
typed forms depend on those later constructions.  The declarations below do
record the precise categorical factorization and Tate normalization that the
introduction uses as the organizing conditions for the general theory.
-/

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory

universe u v u' v' w w'

namespace Formalization.Books.Weil.Unit01

/-! ## The categories and functors in the introduction -/

/--
The categorical structure announced for the correspondence category of
smooth projective schemes over `k`.

`GradedCategory` is the established project interface for a graded category;
the monoidal and symmetric structures are Mathlib's canonical interfaces.
The interpretation of the objects as schemes and of morphisms as
correspondences is supplied by the later correspondence section.
-/
class CorrespondenceCategory (k : Type u) [Field k] (C : Type v)
    [Category.{w} C] [Preadditive C] [CategoryTheory.Linear ℚ C]
    extends MonoidalCategory C, SymmetricCategory C,
      Formalization.Books.Dga.Unit25.GradedCategory ℚ C

/--
The symmetric monoidal Karoubian interface for the category `M_k` of Chow
motives.  `IsIdempotentComplete` is Mathlib's canonical Karoubian condition;
the two displayed isomorphisms record that the Tate motive is the tensor
inverse of the Lefschetz motive.
-/
class ChowMotiveCategory (k : Type u) [Field k] (M : Type v)
    [Category.{w} M]
    extends MonoidalCategory M, SymmetricCategory M, IsIdempotentComplete M where
  /-- The Lefschetz motive. -/
  lefschetzMotive : M
  /-- The Tate motive, inverse to `lefschetzMotive` under tensor product. -/
  tateMotive : M
  /-- The Tate motive is a left tensor inverse of the Lefschetz motive. -/
  tate_lefschetz_iso : tateMotive ⊗ lefschetzMotive ≅ 𝟙_ M
  /-- The Tate motive is a right tensor inverse of the Lefschetz motive. -/
  lefschetz_tate_iso : lefschetzMotive ⊗ tateMotive ≅ 𝟙_ M

/-- The contravariant functor from smooth projective schemes to Chow motives. -/
abbrev ChowMotiveFunctor (C : Type u) [Category.{v} C]
    (M : Type u') [Category.{v'} M] :=
  Formalization.Books.Categories.Unit03.ContravariantFunctor C M

/--
The Lean interface for a Weil cohomology functor with coefficient field `F`:
it is contravariant and takes values in integer-graded `F`-vector spaces.
-/
abbrev WeilCohomologyFunctor (C : Type u) [Category.{v} C]
    (F : Type u') [Field F] :=
  Formalization.Books.Categories.Unit03.ContravariantFunctor C
    (Formalization.Books.Homology.Unit17.GradedVectorSpace F)

/-! ## The graded Tate line -/

/--
The graded vector space which is the ordinary one-dimensional `F`-vector
space in degree `n` and the zero object in every other degree.
-/
noncomputable def gradedLine (F : Type u) [Field F] (n : ℤ) :
    Formalization.Books.Homology.Unit17.GradedVectorSpace F :=
  (CategoryTheory.GradedObject.single n).obj (ModuleCat.of F F)

/-- The component of `gradedLine F n` in degree `n` is the standard line `F`. -/
noncomputable def gradedLine_component_iso (F : Type u) [Field F] (n : ℤ) :
    (gradedLine F n) n ≅ ModuleCat.of F F :=
  CategoryTheory.GradedObject.singleObjApplyIso n (ModuleCat.of F F)

/-- Every component of `gradedLine F n` away from degree `n` is initial. -/
noncomputable def gradedLine_component_isInitial
    (F : Type u) [Field F] (n i : ℤ) (h : i ≠ n) :
    IsInitial ((gradedLine F n) i) :=
  CategoryTheory.GradedObject.isInitialSingleObjApply n
    (ModuleCat.of F F) i h

/--
The Tate line `F(1)`, represented with the source convention that its copy of
`F` lies in degree `-2`.
-/
noncomputable def TateLine (F : Type u) [Field F] :
    Formalization.Books.Homology.Unit17.GradedVectorSpace F :=
  gradedLine F (-2)

/-!
The earlier Homology chapter constructs both the unsigned and Koszul-signed
symmetric structures on graded vector spaces.  The signed structure is the
one used here, since it is the symmetric monoidal structure compatible with
the graded tensor convention in the source.
-/

/-- A chosen symmetric monoidal structure on integer-graded `F`-vector spaces. -/
noncomputable def standardGradedVectorSpaceStructures (F : Type u) [Field F] :
    Formalization.Books.Homology.Unit17.GradedVectorSpaceSymmetricStructures F :=
  Classical.choice
    (Formalization.Books.Homology.Unit17.graded_vector_space_symmetric_structures F)

/-- The selected monoidal structure on graded `F`-vector spaces. -/
noncomputable instance standardGradedVectorSpaceMonoidalCategory
    (F : Type u) [Field F] :
    MonoidalCategory
      (Formalization.Books.Homology.Unit17.GradedVectorSpace F) :=
  (standardGradedVectorSpaceStructures F).monoidal

/-- The selected Koszul-signed symmetric structure on graded `F`-vector spaces. -/
noncomputable instance standardGradedVectorSpaceSymmetricCategory
    (F : Type u) [Field F] :
    @SymmetricCategory
      (Formalization.Books.Homology.Unit17.GradedVectorSpace F) _
      (standardGradedVectorSpaceMonoidalCategory F) :=
  (standardGradedVectorSpaceStructures F).signed

/-! ## Factorization through Chow motives -/

/--
The introduction's assertion that a Weil cohomology factors through `h`.
The source writes an equality `H = G ∘ h`; the categorical interface uses a
natural isomorphism, which is the usable notion of identifying functors while
retaining the specified symmetric monoidal structure on `G`.
-/
structure WeilCohomologyFactorization
    {k : Type u} [Field k]
    {C : Type v} [Category.{w} C] [Preadditive C]
    [CategoryTheory.Linear ℚ C] [CorrespondenceCategory k C]
    {M : Type u'} [Category.{v'} M] [ChowMotiveCategory k M]
    {F : Type w'} [Field F]
    (h : ChowMotiveFunctor C M) (H : WeilCohomologyFunctor C F) where
  /-- The realization functor on Chow motives. -/
  G : M ⥤ Formalization.Books.Homology.Unit17.GradedVectorSpace F
  /-- `G` is a symmetric monoidal functor. -/
  symmetric_monoidal : Functor.Braided G
  /-- The cohomology functor is identified with `G` after `h`. -/
  factorization : H ≅ h ⋙ G

/-! ## The first two general-field conditions -/

/--
A realization of the inverse Lefschetz (Tate) motive in `M_k` as the graded
line `F(1)`.
-/
structure TateMotiveRealization
    {k : Type u} [Field k]
    {M : Type v} [Category.{w} M] [ChowMotiveCategory k M]
    {F : Type u'} [Field F]
    (G : M ⥤ Formalization.Books.Homology.Unit17.GradedVectorSpace F) where
  /-- The realization of the Tate motive is the line in degree `-2`. -/
  realization : G.obj
      (ChowMotiveCategory.tateMotive (k := k) (M := M)) ≅ TateLine F

/--
The source's first two axioms for a general-field Weil cohomology: motivic
factorization and the normalization of the Tate motive.

The third introductory condition, recovery of the classical theory over an
algebraically closed field up to a choice of basis in `F(1)`, is intentionally
left for the later classical and comparison sections, where the cycle-class,
trace, and Poincaré-duality interfaces have been introduced.
-/
structure WeilCohomologyMotivicData
    {k : Type u} [Field k]
    {C : Type v} [Category.{w} C] [Preadditive C]
    [CategoryTheory.Linear ℚ C] [CorrespondenceCategory k C]
    {M : Type u'} [Category.{v'} M] [ChowMotiveCategory k M]
    {F : Type w'} [Field F]
    (h : ChowMotiveFunctor C M) (H : WeilCohomologyFunctor C F) where
  factorization : WeilCohomologyFactorization (k := k) h H
  tate : TateMotiveRealization (k := k) factorization.G

/-!
The introduction also warns that the literature does not use a universal
definition of “Weil cohomology”, that the non-closed-field cycle lemmas are
supporting results for later sections, and that first Chern classes provide an
alternative to cycle classes.  These are source-level scope and compatibility
statements; their typed declarations occur with the corresponding later
constructions rather than being replaced here by artificial placeholder
propositions.
-/

end Formalization.Books.Weil.Unit01
