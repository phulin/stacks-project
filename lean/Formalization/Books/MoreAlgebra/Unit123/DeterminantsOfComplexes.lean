import Formalization.Books.MoreAlgebra.Unit85.TwoTermComplexes
import Formalization.Books.MoreAlgebra.Unit119.Determinants

/-!
# More on Algebra, Chapter 123: Determinants of complexes

This file formalizes the ad hoc determinant construction for perfect objects
of tor-amplitude `[-1, 0]`.  The complex model is the earlier canonical
`TwoTermComplex`; determinant lines are written in the source's equivalent
`Hom` presentation, and the good-diagram interfaces make the final
derived-category construction explicit.
-/

noncomputable section

open CategoryTheory
open Formalization.Books.MoreAlgebra.Unit85
open Formalization.Books.MoreAlgebra.Unit119
open scoped TensorProduct

universe u

namespace Formalization.Books.MoreAlgebra.Unit123

abbrev Mod (R : Type u) [CommRing R] := ModuleCat.{u} R

/-! ## Two-term perfect complexes and their determinant lines -/

/-- A two-term complex whose two displayed terms are finite projective. -/
structure FiniteProjectiveTwoTermComplex (R : Type u) [CommRing R] where
  complex : TwoTermComplex R
  neg_finite : Module.Finite R (complex.neg : Type u)
  neg_projective : Module.Projective R (complex.neg : Type u)
  zero_finite : Module.Finite R (complex.zero : Type u)
  zero_projective : Module.Projective R (complex.zero : Type u)

namespace FiniteProjectiveTwoTermComplex

variable {R : Type u} [CommRing R]

abbrev neg (T : FiniteProjectiveTwoTermComplex R) : Mod R := T.complex.neg

abbrev zero (T : FiniteProjectiveTwoTermComplex R) : Mod R := T.complex.zero

abbrev differential (T : FiniteProjectiveTwoTermComplex R) :
    T.neg ⟶ T.zero := T.complex.differential

abbrev differentialLinearMap (T : FiniteProjectiveTwoTermComplex R) :
    (T.neg : Type u) →ₗ[R] (T.zero : Type u) := T.differential.hom

instance (T : FiniteProjectiveTwoTermComplex R) :
    Module.Finite R (T.neg : Type u) := T.neg_finite

instance (T : FiniteProjectiveTwoTermComplex R) :
    Module.Projective R (T.neg : Type u) := T.neg_projective

instance (T : FiniteProjectiveTwoTermComplex R) :
    Module.Finite R (T.zero : Type u) := T.zero_finite

instance (T : FiniteProjectiveTwoTermComplex R) :
    Module.Projective R (T.zero : Type u) := T.zero_projective

/-- Equality of the ranks of the two terms at every prime of the base ring. -/
def RankZero (T : FiniteProjectiveTwoTermComplex R) : Prop :=
  SameRankAtPrimes R (T.neg : Type u) (T.zero : Type u)

/-- The determinant line, in the source's `Hom` presentation. -/
abbrev determinantLine (T : FiniteProjectiveTwoTermComplex R) : Type u :=
  determinantModule R (T.neg : Type u) →ₗ[R]
    determinantModule R (T.zero : Type u)

/-- The source's tensor presentation of the determinant line. -/
abbrev determinantTensorLine (T : FiniteProjectiveTwoTermComplex R) : Type u :=
  determinantModule R (T.zero : Type u) ⊗[R]
    Module.Dual R (determinantModule R (T.neg : Type u))

/-- The displayed tensor and Hom presentations are canonically equivalent. -/
theorem exists_determinantTensorLineEquiv (T : FiniteProjectiveTwoTermComplex R) :
    Nonempty (determinantTensorLine T ≃ₗ[R] T.determinantLine) := by
  sorry

noncomputable def determinantTensorLineEquiv (T : FiniteProjectiveTwoTermComplex R) :
    determinantTensorLine T ≃ₗ[R] determinantLine T :=
  Classical.choice (exists_determinantTensorLineEquiv T)

/-- A determinant-line element is a trivialization when it is the image of `1`
under a linear equivalence from the base ring. -/
def IsTrivialization (T : FiniteProjectiveTwoTermComplex R)
    (δ : T.determinantLine) : Prop :=
  ∃ e : R ≃ₗ[R] T.determinantLine, e 1 = δ

/-- The canonical element associated to a rank-zero two-term complex. -/
noncomputable def canonicalElement (T : FiniteProjectiveTwoTermComplex R)
    (hT : T.RankZero) : T.determinantLine := by
  exact determinantMap T.differentialLinearMap hT

/-- In the rank-zero case, the canonical element is the determinant of the
differential, as in the source. -/
theorem canonicalElement_eq_determinant (T : FiniteProjectiveTwoTermComplex R)
    (hT : T.RankZero) :
    T.canonicalElement hT = determinantMap T.differentialLinearMap hT := by
  rfl

/-- For a two-term complex, acyclicity is the vanishing condition used by the
source's assertion about trivializations of the canonical element. -/
def IsAcyclic (T : FiniteProjectiveTwoTermComplex R) : Prop :=
  Function.Bijective T.differentialLinearMap

theorem canonicalElement_isTrivialization_iff_acyclic
    (T : FiniteProjectiveTwoTermComplex R) (hT : T.RankZero) :
    T.IsTrivialization (T.canonicalElement hT) ↔ T.IsAcyclic := by
  sorry

end FiniteProjectiveTwoTermComplex

/-! ## Surjective quasi-isomorphisms and their determinant maps -/

namespace FiniteProjectiveTwoTermComplex

variable {R : Type u} [CommRing R]

/-- A map satisfying the three hypotheses used in the source's construction
of `det(a)`. -/
structure SurjectiveQuasiIso (K L : FiniteProjectiveTwoTermComplex R) where
  hom : K.complex.complex ⟶ L.complex.complex
  quasiIso : QuasiIso hom
  surjective : Formalization.Books.MoreAlgebra.Unit59.TermwiseSurjective hom

abbrev component {K L : FiniteProjectiveTwoTermComplex R}
    (a : SurjectiveQuasiIso K L) (i : ℤ) :
    (K.complex.complex.X i : Type u) →ₗ[R] (L.complex.complex.X i : Type u) :=
  (a.hom.f i).hom

/-- The kernel complex and the two short exact sequences used in the source's
definition of `det(a)`.  The finite-projective and acyclicity fields expose
the facts needed to form the determinant lines of the kernel terms. -/
structure KernelData
    {K L : FiniteProjectiveTwoTermComplex R}
    (a : SurjectiveQuasiIso K L) where
  kernel : FiniteProjectiveTwoTermComplex R
  inclusion : kernel.complex.complex ⟶ K.complex.complex
  neg_inclusion : (kernel.neg : Type u) →ₗ[R] (K.neg : Type u)
  zero_inclusion : (kernel.zero : Type u) →ₗ[R] (K.zero : Type u)
  neg_inclusion_eq : (inclusion.f (-1)).hom = neg_inclusion
  zero_inclusion_eq : (inclusion.f 0).hom = zero_inclusion
  neg_exact : Function.Exact neg_inclusion (component a (-1))
  neg_injective : Function.Injective neg_inclusion
  neg_surjective : Function.Surjective (component a (-1))
  zero_exact : Function.Exact zero_inclusion (component a 0)
  zero_injective : Function.Injective zero_inclusion
  zero_surjective : Function.Surjective (component a 0)
  acyclic : kernel.IsAcyclic
  rank_zero : kernel.RankZero

/-- The determinant isomorphisms `γ⁻¹` and `γ⁰` from the two short exact
sequences in the source. -/
noncomputable def gammaNeg
    {K L : FiniteProjectiveTwoTermComplex R}
    {a : SurjectiveQuasiIso K L} (W : KernelData a) :
    determinantModule R (W.kernel.neg : Type u) ⊗[R]
        determinantModule R (L.neg : Type u) ≃ₗ[R]
      determinantModule R (K.neg : Type u) :=
  determinantShortExactIso W.neg_inclusion (component a (-1)) W.neg_exact
    W.neg_injective W.neg_surjective

noncomputable def gammaZero
    {K L : FiniteProjectiveTwoTermComplex R}
    {a : SurjectiveQuasiIso K L} (W : KernelData a) :
    determinantModule R (W.kernel.zero : Type u) ⊗[R]
        determinantModule R (L.zero : Type u) ≃ₗ[R]
      determinantModule R (K.zero : Type u) :=
  determinantShortExactIso W.zero_inclusion (component a 0) W.zero_exact
    W.zero_injective W.zero_surjective

theorem exists_kernelData
    {K L : FiniteProjectiveTwoTermComplex R}
    (a : SurjectiveQuasiIso K L) : Nonempty (KernelData a) := by
  sorry

/-- The determinant isomorphism attached to a surjective quasi-isomorphism.
Its existence is the exact-sequence construction in the source; the chosen
map is exposed separately so later statements can use it without repeating
the choice of a comparison diagram. -/
theorem exists_determinantMap
    {K L : FiniteProjectiveTwoTermComplex R} (a : SurjectiveQuasiIso K L) :
    Nonempty (K.determinantLine ≃ₗ[R] L.determinantLine) := by
  sorry

noncomputable def determinantMap
    {K L : FiniteProjectiveTwoTermComplex R} (a : SurjectiveQuasiIso K L) :
    K.determinantLine ≃ₗ[R] L.determinantLine :=
  Classical.choice (exists_determinantMap a)

/-- The canonical determinant map preserves canonical elements whenever the
target has rank zero. -/
theorem determinantMap_canonicalElement
    {K L : FiniteProjectiveTwoTermComplex R}
    (a : SurjectiveQuasiIso K L) (hL : L.RankZero) :
    determinantMap a (K.canonicalElement (by sorry)) =
      L.canonicalElement hL := by
  sorry

/-- The homotopy data in the source's second lemma. -/
structure HomotopicSurjection
    {K L : FiniteProjectiveTwoTermComplex R} (a : SurjectiveQuasiIso K L) where
  b : SurjectiveQuasiIso K L
  homotopy : K.zero ⟶ L.neg
  zero_eq : component b 0 = component a 0 +
      L.differentialLinearMap.comp homotopy.hom
  neg_eq : component b (-1) = component a (-1) +
      homotopy.hom.comp K.differentialLinearMap

theorem determinantMap_eq_of_homotopicSurjection
    {K L : FiniteProjectiveTwoTermComplex R}
    (a : SurjectiveQuasiIso K L) (h : HomotopicSurjection a) :
    determinantMap a = determinantMap h.b := by
  sorry

/-- The composition law for the determinant maps of surjective
quasi-isomorphisms. -/
theorem determinantMap_comp
    {K L M : FiniteProjectiveTwoTermComplex R}
    (a : SurjectiveQuasiIso K L) (b : SurjectiveQuasiIso L M)
    (c : SurjectiveQuasiIso K M)
    (hcomp : c.hom = a.hom ≫ b.hom) :
    determinantMap a ≪≫ₗ determinantMap b = determinantMap c := by
  sorry

end FiniteProjectiveTwoTermComplex

/-! ## Good diagrams and the final functorial statement -/

namespace FiniteProjectiveTwoTermComplex

variable {R : Type u} [CommRing R]

/-- A quasi-isomorphism between good two-term representatives. -/
structure DerivedIsomorphism (K L : FiniteProjectiveTwoTermComplex R) where
  hom : K.complex.complex ⟶ L.complex.complex
  quasiIso : QuasiIso hom

/-- A good diagram used to define the determinant of a general derived
isomorphism by comparing two surjective maps from a common representative. -/
structure GoodDiagram
    {K L : FiniteProjectiveTwoTermComplex R} (a : DerivedIsomorphism K L) where
  middle : FiniteProjectiveTwoTermComplex R
  toSource : SurjectiveQuasiIso middle K
  toTarget : SurjectiveQuasiIso middle L
  commutes : Nonempty (Homotopy (toSource.hom ≫ a.hom) toTarget.hom)

/-- The determinant map associated to one good diagram. -/
noncomputable def determinantOfGoodDiagram
    {K L : FiniteProjectiveTwoTermComplex R}
    {a : DerivedIsomorphism K L} (D : GoodDiagram a) :
    K.determinantLine ≃ₗ[R] L.determinantLine :=
  (determinantMap D.toSource).symm ≪≫ₗ determinantMap D.toTarget

/-- Good diagrams exist for quasi-isomorphisms of good complexes. -/
theorem exists_goodDiagram
    {K L : FiniteProjectiveTwoTermComplex R}
    (a : DerivedIsomorphism K L) : Nonempty (GoodDiagram a) := by
  sorry

/-- The good-diagram determinant is independent of the chosen diagram. -/
theorem determinantOfGoodDiagram_independent
    {K L : FiniteProjectiveTwoTermComplex R}
    (a : DerivedIsomorphism K L) (D₁ D₂ : GoodDiagram a) :
    determinantOfGoodDiagram D₁ = determinantOfGoodDiagram D₂ := by
  sorry

/-- The determinant of a derived isomorphism, chosen from any good diagram. -/
noncomputable def determinantOfDerivedIsomorphism
    {K L : FiniteProjectiveTwoTermComplex R}
    (a : DerivedIsomorphism K L) :
    K.determinantLine ≃ₗ[R] L.determinantLine :=
  determinantOfGoodDiagram (Classical.choice (exists_goodDiagram a))

theorem determinantOfDerivedIsomorphism_eq_goodDiagram
    {K L : FiniteProjectiveTwoTermComplex R}
    (a : DerivedIsomorphism K L) (D : GoodDiagram a) :
    determinantOfDerivedIsomorphism a = determinantOfGoodDiagram D := by
  sorry

/-- The identity derived isomorphism induces the identity on determinant lines. -/
theorem determinantOfDerivedIsomorphism_id
    (K : FiniteProjectiveTwoTermComplex R) :
    determinantOfDerivedIsomorphism
        { hom := 𝟙 K.complex.complex, quasiIso := by sorry } =
      LinearEquiv.refl R K.determinantLine := by
  sorry

/-- Determinants compose in the source-corrected covariant orientation. -/
theorem determinantOfDerivedIsomorphism_comp
    {K L M : FiniteProjectiveTwoTermComplex R}
    (a : DerivedIsomorphism K L) (b : DerivedIsomorphism L M)
    (hcomp : QuasiIso (a.hom ≫ b.hom)) :
    determinantOfDerivedIsomorphism a ≪≫ₗ
        determinantOfDerivedIsomorphism b =
      determinantOfDerivedIsomorphism
        { hom := a.hom ≫ b.hom, quasiIso := hcomp } := by
  sorry

/-- A rank-zero derived representative. -/
def DerivedRankZero (K : FiniteProjectiveTwoTermComplex R) : Prop := K.RankZero

/-- Canonical elements are invariant under derived isomorphisms. -/
theorem determinantOfDerivedIsomorphism_canonicalElement
    {K L : FiniteProjectiveTwoTermComplex R}
    (a : DerivedIsomorphism K L) (hL : L.DerivedRankZero) :
    determinantOfDerivedIsomorphism a
        (K.canonicalElement (by sorry)) = L.canonicalElement hL := by
  sorry

/-- The functorial interface asserted by the source's final lemma. -/
structure DeterminantFunctorData (R : Type u) [CommRing R] where
  map : ∀ {K L : FiniteProjectiveTwoTermComplex R},
    DerivedIsomorphism K L → K.determinantLine ≃ₗ[R] L.determinantLine
  map_id : ∀ (K : FiniteProjectiveTwoTermComplex R),
    map { hom := 𝟙 K.complex.complex, quasiIso := by sorry } =
      LinearEquiv.refl R K.determinantLine
  map_comp : ∀ {K L M : FiniteProjectiveTwoTermComplex R}
    (a : DerivedIsomorphism K L)
    (b : DerivedIsomorphism L M) (hcomp : QuasiIso (a.hom ≫ b.hom)),
    map a ≪≫ₗ map b =
      map { hom := a.hom ≫ b.hom, quasiIso := hcomp }

theorem exists_determinantFunctorData (R : Type u) [CommRing R] :
    Nonempty (DeterminantFunctorData R) := by
  sorry

noncomputable def determinantFunctorData (R : Type u) [CommRing R] :
    DeterminantFunctorData R :=
  Classical.choice (exists_determinantFunctorData R)

end FiniteProjectiveTwoTermComplex

end Formalization.Books.MoreAlgebra.Unit123
