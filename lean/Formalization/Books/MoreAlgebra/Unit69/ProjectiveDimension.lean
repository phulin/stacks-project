import Formalization.Books.Derived.Unit19.ProjectiveResolutions
import Formalization.Books.Derived.Unit27.ExtGroups
import Mathlib.CategoryTheory.Abelian.Projective.Dimension
import Mathlib.Order.Interval.Set.Basic
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Polynomial.Quotient

/-!
# More on Algebra, Chapter 69: projective dimension

The source works in the derived category of modules over a ring.  Complexes
are the canonical integer-indexed cochain complexes from Derived Chapter 8;
projectivity is the categorical `Projective` predicate, which is the existing
module-category projectivity interface.
-/

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Preadditive
open CategoryTheory.Pretriangulated
open Formalization.Books.Derived.Unit08
open Formalization.Books.Derived.Unit11
open Formalization.Books.Derived.Unit19
open Formalization.Books.Derived.Unit27
open scoped CategoryTheory.Pretriangulated.Opposite ZeroObject

universe w u

namespace Formalization.Books.MoreAlgebra.Unit69

section Definitions

variable {R : Type u} [Ring R]
variable [HasDerivedCategory.{w} (ModuleCat.{u} R)]

/-! ## Finite projective dimension and projective-amplitude -/

/-- A bounded integer-indexed complex of projective `R`-modules representing
an object of `D(R)`. -/
def HasFiniteProjectiveDimension
    {K : DerivedCategory (ModuleCat.{u} R)} : Prop :=
  ∃ P : BookComplex (ModuleCat.{u} R),
    IsBounded P ∧
      (∀ i : ℤ, Projective (P.X i)) ∧
        Nonempty ((DerivedCategory.Q (C := ModuleCat.{u} R)).obj P ≅ K)

/-- Data witnessing that `K` is represented by projectives in the interval
`[a, b]`.  The strict support predicates say that the terms outside the
interval are zero. -/
structure ProjectiveAmplitudeWitness
    (K : DerivedCategory (ModuleCat.{u} R)) (a b : ℤ) where
  complex : BookComplex (ModuleCat.{u} R)
  projective : ∀ i : ℤ, Projective (complex.X i)
  lowerBound : complex.IsStrictlyGE a
  upperBound : complex.IsStrictlyLE b
  represents :
    Nonempty ((DerivedCategory.Q (C := ModuleCat.{u} R)).obj complex ≅ K)

/-- `K` has projective-amplitude in `[a, b]`. -/
def HasProjectiveAmplitude
    (K : DerivedCategory (ModuleCat.{u} R)) (a b : ℤ) : Prop :=
  Nonempty (ProjectiveAmplitudeWitness K a b)

/-- Finite projective dimension is equivalent to projective-amplitude in some
integer interval. -/
theorem hasFiniteProjectiveDimension_iff_exists_projective_amplitude
    {K : DerivedCategory (ModuleCat.{u} R)} :
    HasFiniteProjectiveDimension (R := R) (K := K) ↔
      ∃ a b : ℤ, HasProjectiveAmplitude K a b := by
  sorry

/-- An object of finite projective dimension is bounded in the derived
category. -/
theorem derivedBounded_of_hasFiniteProjectiveDimension
    {K : DerivedCategory (ModuleCat.{u} R)}
    (hK : HasFiniteProjectiveDimension (R := R) (K := K)) :
    derivedBoundedProperty (ModuleCat.{u} R) K := by
  sorry

end Definitions

section ProjectiveAmplitudeCriteria

variable {R : Type u} [Ring R]
variable [HasDerivedCategory.{w} (ModuleCat.{u} R)]
variable {K : DerivedCategory (ModuleCat.{u} R)}
variable {P : BookComplex (ModuleCat.{u} R)} {a b : ℤ}

/-! ## Ext criteria -/

/-- The four equivalent criteria for projective-amplitude in `[a, b]`.

The interval notation in the source is represented by `Set.Icc` in `ℤ`.
The Ext predicate is the earlier chapter's canonical `DerivedExtVanishes`.
-/
theorem projective_amplitude_criteria
    (K : DerivedCategory (ModuleCat.{u} R)) (a b : ℤ) :
    List.TFAE [
      HasProjectiveAmplitude K a b,
      ∀ (N : ModuleCat.{u} R) (i : ℤ),
        i ∉ Set.Icc (-b) (-a) →
          DerivedExtVanishes K (DerivedObject N) i,
      (∀ n : ℤ, b < n →
          IsZero ((derivedCohomologyFunctor (ModuleCat.{u} R) n).obj K)) ∧
        (∀ (N : ModuleCat.{u} R) (i : ℤ), -a < i →
          DerivedExtVanishes K (DerivedObject N) i),
      (∀ n : ℤ, n ∉ Set.Icc (a - 1) b →
          IsZero ((derivedCohomologyFunctor (ModuleCat.{u} R) n).obj K)) ∧
      (∀ (N : ModuleCat.{u} R),
          DerivedExtVanishes K (DerivedObject N) (-a + 1)) ] := by
  sorry

theorem projective_amplitude_ext_compute
    (W : ProjectiveAmplitudeWitness K a b)
    (N : ModuleCat.{u} R) (i : ℤ) :
    Nonempty
      (DerivedExt K (DerivedObject N) i ≃+
        CochainComplex.HomComplex.CohomologyClass W.complex
          ((CochainComplex.singleFunctor (ModuleCat.{u} R) 0).obj N) i) := by
  sorry

theorem derivedExt_to_injective_cohomology
    (I : ModuleCat.{u} R) [Injective I] (n : ℤ) :
    Nonempty
      (DerivedExt K (DerivedObject I) (-n) ≃+
        ((derivedCohomologyFunctor (ModuleCat.{u} R) n).obj K ⟶ I)) := by
  sorry

/-! ## The truncation triangle used in the proof of the criterion -/

/-- The source's truncation data: `Q` is the cokernel of
`P^(a - 1) ⟶ P^a`, and the displayed distinguished triangle has terms
`K' ⟶ K ⟶ Q[-a] ⟶ K'[1]`.  The fields for the truncated complex retain the
projective and support information used in the proof. -/
structure ProjectiveAmplitudeTruncationData
    (K : DerivedCategory (ModuleCat.{u} R))
    (P : BookComplex (ModuleCat.{u} R)) (a b : ℤ) where
  truncation : BookComplex (ModuleCat.{u} R)
  truncationProjective : ∀ i : ℤ, Projective (truncation.X i)
  truncationLowerBound : truncation.IsStrictlyGE (a + 1)
  truncationUpperBound : truncation.IsStrictlyLE b
  truncationTermIso : ∀ (i : ℤ), a < i → i ≤ b →
    Nonempty (truncation.X i ≅ P.X i)
  quotient : ModuleCat.{u} R
  quotientIso : quotient ≅ cokernel (P.d a (a - 1))
  triangle : Triangle (DerivedCategory (ModuleCat.{u} R))
  distinguished : triangle ∈ distTriang (DerivedCategory (ModuleCat.{u} R))
  firstIso : triangle.obj₁ ≅
    (DerivedCategory.Q (C := ModuleCat.{u} R)).obj truncation
  secondIso : triangle.obj₂ ≅ K
  thirdIso : triangle.obj₃ ≅
    (shiftFunctor (DerivedCategory (ModuleCat.{u} R)) (-a)).obj
      (DerivedObject quotient)

/-- Under the hypotheses used in implication (4) `⇒` (1), the truncation
complex, cokernel, and distinguished triangle from the source can be chosen.
The proof is deferred, but the coker and all three triangle identifications
are part of the usable interface. -/
theorem projective_amplitude_truncation_exists
    (K : DerivedCategory (ModuleCat.{u} R))
    (P : BookComplex (ModuleCat.{u} R)) (a b : ℤ)
    (hPAbove : P.IsStrictlyLE b)
    (hPProjective : ∀ i : ℤ, Projective (P.X i))
    (hKBelow : ∀ n : ℤ, n < a →
      IsZero ((derivedCohomologyFunctor (ModuleCat.{u} R) n).obj K))
    (hRep : Nonempty ((DerivedCategory.Q (C := ModuleCat.{u} R)).obj P ≅ K)) :
    Nonempty (ProjectiveAmplitudeTruncationData K P a b) := by
  sorry

/-! ## The exact Ext sequence -/

/-- The five-term contravariant Ext window attached to the truncation
triangle.  Its central three terms are the shifted form of the source's
displayed exact sequence
`Ext^(-a)(K', N) → Ext^1(Q, N) → Ext^(1-a)(K, N)`. -/
noncomputable def projectiveAmplitudeExtWindow
    (T : ProjectiveAmplitudeTruncationData K P a b)
    (N : ModuleCat.{u} R) :
    ComposableArrows (AddCommGrpCat.{w}) 5 :=
  derivedExtContravariantWindow T.triangle (DerivedObject N) (-a)

/-- The Ext window attached to the truncation triangle is exact. -/
theorem projectiveAmplitudeExtWindow_exact
    (T : ProjectiveAmplitudeTruncationData K P a b)
    (N : ModuleCat.{u} R) :
    (projectiveAmplitudeExtWindow T N).Exact := by
  simpa [projectiveAmplitudeExtWindow] using
    (derivedExtContravariantWindow_exact T.triangle T.distinguished
      (DerivedObject N) (-a))

/-- The central three arrows of the exact Ext window, before identifying the
third object of the triangle with `Q[-a]`. -/
noncomputable def projectiveAmplitudeExtSequenceShifted
    (T : ProjectiveAmplitudeTruncationData K P a b)
    (N : ModuleCat.{u} R) : ShortComplex (AddCommGrpCat.{w}) :=
  ShortComplex.mk
    ((projectiveAmplitudeExtWindow T N).map' 2 3 (by omega) (by omega))
    ((projectiveAmplitudeExtWindow T N).map' 3 4 (by omega) (by omega))
    ((projectiveAmplitudeExtWindow_exact T N).toIsComplex.zero 2 (by omega))

/-- The shifted central three-term sequence is exact. -/
theorem projectiveAmplitudeExtSequenceShifted_exact
    (T : ProjectiveAmplitudeTruncationData K P a b)
    (N : ModuleCat.{u} R) :
    (projectiveAmplitudeExtSequenceShifted T N).Exact := by
  simpa [projectiveAmplitudeExtSequenceShifted] using
    (projectiveAmplitudeExtWindow_exact T N).exact 2 (by omega)

/-- Source-facing form of the displayed three-term Ext sequence.  The
isomorphisms identify its terms with the truncation object, the cokernel, and
`K`, respectively. -/
theorem projective_amplitude_displayed_ext_sequence
    (T : ProjectiveAmplitudeTruncationData K P a b)
    (N : ModuleCat.{u} R) :
    ∃ S : ComposableArrows (AddCommGrpCat.{w}) 2,
      S.Exact ∧
        Nonempty (S.obj' 0 ≅ AddCommGrpCat.of
          (DerivedExt
            ((DerivedCategory.Q (C := ModuleCat.{u} R)).obj T.truncation)
            (DerivedObject N) (-a))) ∧
        Nonempty (S.obj' 1 ≅ AddCommGrpCat.of
          (DerivedExt (DerivedObject T.quotient) (DerivedObject N) 1)) ∧
        Nonempty (S.obj' 2 ≅ AddCommGrpCat.of
          (DerivedExt K (DerivedObject N) (1 - a))) := by
  sorry

end ProjectiveAmplitudeCriteria

section DualNumbers

variable {k : Type u} [Field k]

/-! ## The dual-numbers example -/

/-- The ideal `(x²)` in `k[x]`. -/
def dualNumberPolynomialIdeal : Ideal (Polynomial k) :=
  Ideal.span ({Polynomial.X ^ 2} : Set (Polynomial k))

/-- The ring `k[x]/(x²)`. -/
abbrev dualNumberRing : Type u :=
  Polynomial k ⧸ dualNumberPolynomialIdeal

/-- The class `ε` of `x` in the dual-number ring. -/
def dualNumberEpsilon : dualNumberRing (k := k) :=
  Ideal.Quotient.mk (dualNumberPolynomialIdeal (k := k)) Polynomial.X

/-- The module `R/(ε)` from the dual-numbers example. -/
def dualNumberModule : ModuleCat.{u} (dualNumberRing (k := k)) :=
  ModuleCat.of (dualNumberRing (k := k))
    ((dualNumberRing (k := k)) ⧸
      Ideal.span ({dualNumberEpsilon (k := k)} : Set (dualNumberRing (k := k))))

/-- Multiplication by `ε` on the regular `R`-module. -/
def dualNumberMultiplication :
    ModuleCat.of (dualNumberRing (k := k)) (dualNumberRing (k := k)) ⟶
      ModuleCat.of (dualNumberRing (k := k)) (dualNumberRing (k := k)) :=
  ModuleCat.ofHom (LinearMap.lsmul (dualNumberRing (k := k))
    (dualNumberRing (k := k)) (dualNumberEpsilon (k := k)))

/-- Shape data for the infinite resolution
`R \xrightarrow{ε} R \xrightarrow{ε} R \to \cdots`.  The use of
`ProjectiveResolution` is Mathlib's canonical chain-complex indexing of this
cochain presentation. -/
def IsDualNumberResolutionShape
    (P : ProjectiveResolution (dualNumberModule (k := k))) : Prop :=
  ∃ e : ∀ n : ℕ,
      P.complex.X n ≅
        ModuleCat.of (dualNumberRing (k := k)) (dualNumberRing (k := k)),
    ∀ n : ℕ,
      (e (n + 1)).hom ≫ dualNumberMultiplication (k := k) =
        P.complex.d (n + 1) n ≫ (e n).hom

/-- The dual-number resolution has the source's repeated `ε` differential,
while the module does not have finite projective dimension.  The final
conjunct uses Mathlib's canonical module projective-dimension bound, which is
the earlier Algebra definition in its categorical form. -/
theorem dual_number_example
    [HasDerivedCategory.{w} (ModuleCat.{u} (dualNumberRing (k := k)))] :
    ∃ P : ProjectiveResolution (dualNumberModule (k := k)),
      IsDualNumberResolutionShape (k := k) P ∧
        ¬ HasFiniteProjectiveDimension
          (R := dualNumberRing (k := k))
          (K := DerivedObject (dualNumberModule (k := k))) ∧
        ¬ ∃ n : ℕ,
          CategoryTheory.HasProjectiveDimensionLE
            (dualNumberModule (k := k)) n := by
  sorry

end DualNumbers

end Formalization.Books.MoreAlgebra.Unit69
