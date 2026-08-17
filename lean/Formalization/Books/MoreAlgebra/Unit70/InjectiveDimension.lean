import Formalization.Books.MoreAlgebra.Unit68.SpectralSequencesForExt
import Formalization.Books.MoreAlgebra.Unit69.ProjectiveDimension
import Mathlib.Algebra.Category.ModuleCat.InjectiveDimension
import Mathlib.Order.Interval.Set.Basic
import Mathlib.RingTheory.DedekindDomain.Basic
import Mathlib.RingTheory.Jacobson.Ideal
import Mathlib.RingTheory.Jacobson.Radical
import Mathlib.RingTheory.LocalRing.ResidueField.Basic

/-!
# More on Algebra, Chapter 70: injective dimension

The source works in the derived category of modules over a ring.  Bounded
complexes, injective objects, Ext groups, and the bounded derived pieces all
reuse the canonical interfaces from the earlier derived-category chapters.
-/

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Preadditive
open CategoryTheory.Pretriangulated
open Formalization.Books.Derived.Unit08
open Formalization.Books.Derived.Unit11
open Formalization.Books.Derived.Unit18
open Formalization.Books.Derived.Unit27
open Formalization.Books.MoreAlgebra.Unit68
open scoped CategoryTheory.Pretriangulated.Opposite ZeroObject

universe w u

namespace Formalization.Books.MoreAlgebra.Unit70

section Definitions

variable {R : Type u} [Ring R]
variable [HasDerivedCategory.{w} (ModuleCat.{u} R)]

/-! ## Finite injective dimension and injective-amplitude -/

/-- A bounded integer-indexed complex of injective `R`-modules representing
an object of `D(R)`. -/
def HasFiniteInjectiveDimension
    {K : DerivedCategory (ModuleCat.{u} R)} : Prop :=
  ∃ I : BookComplex (ModuleCat.{u} R),
    IsBounded I ∧
      (∀ i : ℤ, Injective (I.X i)) ∧
        Nonempty ((DerivedCategory.Q (C := ModuleCat.{u} R)).obj I ≅ K)

/-- Data witnessing that `K` is represented by injectives in the interval
`[a, b]`.  The strict support predicates say that the terms outside the
interval are zero. -/
structure InjectiveAmplitudeWitness
    (K : DerivedCategory (ModuleCat.{u} R)) (a b : ℤ) where
  complex : BookComplex (ModuleCat.{u} R)
  injective : ∀ i : ℤ, Injective (complex.X i)
  lowerBound : complex.IsStrictlyGE a
  upperBound : complex.IsStrictlyLE b
  represents :
    Nonempty ((DerivedCategory.Q (C := ModuleCat.{u} R)).obj complex ≅ K)

/-- `K` has injective-amplitude in `[a, b]`. -/
def HasInjectiveAmplitude
    (K : DerivedCategory (ModuleCat.{u} R)) (a b : ℤ) : Prop :=
  Nonempty (InjectiveAmplitudeWitness K a b)

/-- Finite injective dimension is equivalent to injective-amplitude in some
integer interval. -/
theorem hasFiniteInjectiveDimension_iff_exists_injective_amplitude
    {K : DerivedCategory (ModuleCat.{u} R)} :
    HasFiniteInjectiveDimension (R := R) (K := K) ↔
      ∃ a b : ℤ, HasInjectiveAmplitude K a b := by
  sorry

/-- An object of finite injective dimension is bounded in the derived
category. -/
theorem derivedBounded_of_hasFiniteInjectiveDimension
    {K : DerivedCategory (ModuleCat.{u} R)}
    (hK : HasFiniteInjectiveDimension (R := R) (K := K)) :
    derivedBoundedProperty (ModuleCat.{u} R) K := by
  sorry

end Definitions

section InjectiveAmplitudeCriteria

variable {R : Type u} [Ring R]
variable [HasDerivedCategory.{w} (ModuleCat.{u} R)]
variable {K : DerivedCategory (ModuleCat.{u} R)}
variable {a b : ℤ}

/-! ## Ext criteria -/

/-- The three equivalent criteria for injective-amplitude in `[a, b]`.

The Ext predicate is the earlier chapter's canonical
`DerivedExtVanishes`.  Ideals are represented by the canonical quotient
module `ModuleCat.of R (R ⧸ I)`. -/
theorem injective_amplitude_criteria
    (K : DerivedCategory (ModuleCat.{u} R)) (a b : ℤ) :
    List.TFAE [
      HasInjectiveAmplitude K a b,
      ∀ (N : ModuleCat.{u} R) (i : ℤ),
        i ∉ Set.Icc a b →
          DerivedExtVanishes (DerivedObject N) K i,
      ∀ (I : Ideal R) (i : ℤ),
        i ∉ Set.Icc a b →
          DerivedExtVanishes
            (DerivedObject (ModuleCat.of R (R ⧸ I))) K i] := by
  sorry

/-- A representative with injective terms computes Ext by the corresponding
Hom-complex cohomology. -/
theorem injective_amplitude_ext_compute
    (W : InjectiveAmplitudeWitness K a b)
    (N : ModuleCat.{u} R) (i : ℤ) :
    Nonempty
      (DerivedExt (DerivedObject N) K i ≃+
        CochainComplex.HomComplex.CohomologyClass
          ((CochainComplex.singleFunctor (ModuleCat.{u} R) 0).obj N)
          W.complex i) := by
  sorry

/-- Ext from the regular module is the cohomology module of the second
derived argument, in the form of an additive equivalence of underlying
abelian groups. -/
theorem regular_module_derivedExt_iso_cohomology
    (K : DerivedCategory (ModuleCat.{u} R)) (n : ℤ) :
    Nonempty
      (DerivedExt
          (DerivedObject (ModuleCat.of R R)) K n ≃+
        ((derivedCohomologyFunctor (ModuleCat.{u} R) n).obj K : Type u)) := by
  sorry

/-! ## The truncation triangle used in the proof of the criterion -/

/-- The source's truncation data: `J` is the kernel of
`I^b ⟶ I^(b + 1)`, and the displayed distinguished triangle has terms
`J[-b] ⟶ K ⟶ K' ⟶ J[1-b]`. -/
structure InjectiveAmplitudeTruncationData
    (K : DerivedCategory (ModuleCat.{u} R))
    (I : BookComplex (ModuleCat.{u} R)) (a b : ℤ) where
  truncation : BookComplex (ModuleCat.{u} R)
  truncationInjective : ∀ i : ℤ, Injective (truncation.X i)
  truncationLowerBound : truncation.IsStrictlyGE a
  truncationUpperBound : truncation.IsStrictlyLE (b - 1)
  truncationTermIso : ∀ (i : ℤ), a ≤ i → i < b →
    Nonempty (truncation.X i ≅ I.X i)
  kernel : ModuleCat.{u} R
  kernelIso : kernel ≅ CategoryTheory.Limits.kernel (I.d b (b + 1))
  triangle : Triangle (DerivedCategory (ModuleCat.{u} R))
  distinguished : triangle ∈ distTriang (DerivedCategory (ModuleCat.{u} R))
  firstIso : triangle.obj₁ ≅
    (shiftFunctor (DerivedCategory (ModuleCat.{u} R)) (-b)).obj
      (DerivedObject kernel)
  secondIso : triangle.obj₂ ≅ K
  thirdIso : triangle.obj₃ ≅
    (DerivedCategory.Q (C := ModuleCat.{u} R)).obj truncation

/-- Under the hypotheses used in implication (3) `⇒` (1), the truncated
complex, its kernel term, and the distinguished triangle from the source can
be chosen. -/
theorem injective_amplitude_truncation_exists
    (K : DerivedCategory (ModuleCat.{u} R))
    (I : BookComplex (ModuleCat.{u} R)) (a b : ℤ)
    (hIAbove : I.IsStrictlyGE a)
    (hIInjective : ∀ i : ℤ, Injective (I.X i))
    (hKBelow : ∀ n : ℤ, n < a →
      IsZero ((derivedCohomologyFunctor (ModuleCat.{u} R) n).obj K))
    (hRep : Nonempty
      ((DerivedCategory.Q (C := ModuleCat.{u} R)).obj I ≅ K)) :
    Nonempty (InjectiveAmplitudeTruncationData K I a b) := by
  sorry

/-! ## The exact Ext sequence -/

/-- The five-term covariant Ext window attached to the truncation triangle.
At degree `b + 1` its first two terms are the shifted `J` and `K` terms in
the source's displayed long exact sequence. -/
noncomputable def injectiveAmplitudeExtWindow
    (T : InjectiveAmplitudeTruncationData K I a b)
    (N : ModuleCat.{u} R) :
    ComposableArrows (AddCommGrpCat.{w}) 5 :=
  derivedExtCovariantWindow T.triangle (DerivedObject N) (b + 1)

/-- The Ext window attached to the truncation triangle is exact. -/
theorem injectiveAmplitudeExtWindow_exact
    (T : InjectiveAmplitudeTruncationData K I a b)
    (N : ModuleCat.{u} R) :
    (injectiveAmplitudeExtWindow T N).Exact := by
  exact derivedExtCovariantWindow_exact T.triangle T.distinguished
    (DerivedObject N) (b + 1)

/-- Source-facing form of the displayed three-term Ext sequence
`Ext^b(R/I, K') → Ext^1(R/I, J) → Ext^(1+b)(R/I, K)`. -/
theorem injective_amplitude_displayed_ext_sequence
    (T : InjectiveAmplitudeTruncationData K I a b)
    (J : Ideal R) :
    ∃ S : ComposableArrows (AddCommGrpCat.{w}) 2,
      S.Exact ∧
        Nonempty (S.obj' 0 ≅ AddCommGrpCat.of
          (DerivedExt (DerivedObject (ModuleCat.of R (R ⧸ J)))
            ((DerivedCategory.Q (C := ModuleCat.{u} R)).obj T.truncation) b)) ∧
        Nonempty (S.obj' 1 ≅ AddCommGrpCat.of
          (DerivedExt (DerivedObject (ModuleCat.of R (R ⧸ J)))
            (DerivedObject T.kernel) 1)) ∧
        Nonempty (S.obj' 2 ≅ AddCommGrpCat.of
          (DerivedExt (DerivedObject (ModuleCat.of R (R ⧸ J))) K (1 + b))) := by
  sorry

end InjectiveAmplitudeCriteria

section DedekindDomainExample

variable {R : Type u} [CommRing R] [IsDedekindDomain R]
variable [HasDerivedCategory.{w} (ModuleCat.{u} R)]

/-! ## The Dedekind-domain example -/

/-- The source's Dedekind-domain example, including the finite-projective
ideal assertion, the injective-dimension bound, Ext vanishing in degrees at
least two, and the resulting bounded-derived decomposition interface. -/
theorem dedekind_domain_finite_injective_dimension
    :
    (∀ I : Ideal R, I ≠ ⊥ →
      Module.Finite R (I : Type u) ∧ Module.Projective R (I : Type u)) ∧
    (∀ I : Ideal R, I ≠ ⊥ →
      CategoryTheory.HasProjectiveDimensionLE
        (ModuleCat.of R (R ⧸ I)) 1) ∧
    (∀ M : ModuleCat.{u} R,
      CategoryTheory.HasInjectiveDimensionLE M 1) ∧
    (∀ M N : ModuleCat.{u} R, ∀ p : ℕ, 2 ≤ p →
      DerivedExtVanishes (DerivedObject M) (DerivedObject N) (p : ℤ)) ∧
    (∀ K : DBounded (ModuleCat.{u} R),
      ∃ a : ℤ, ∃ n : ℕ,
        BoundedCohomologySupported K a n ∧
          Nonempty
            (((DerivedCategory.Bounded.ι (C := ModuleCat.{u} R)).obj K) ≅
              finiteCohomologyDirectSum K a n)) := by
  sorry

end DedekindDomainExample

section DualNumbers

variable {k : Type u} [Field k]

/-! ## The reversed dual-numbers example -/

/-- Shape data for the left-infinite injective complex
`… ⟶ R \xrightarrow{ε} R \xrightarrow{ε} R` in the source's example. -/
def IsDualNumberInjectiveResolutionShape
    (I : BookComplex
      (ModuleCat.{u} (Formalization.Books.MoreAlgebra.Unit69.dualNumberRing
        (k := k)))) : Prop :=
  I.IsStrictlyLE 0 ∧
    (∀ n : ℤ, Injective (I.X n)) ∧
      ∃ e : ∀ (n : ℤ) (_ : n ≤ 0),
        I.X n ≅ ModuleCat.of
          (Formalization.Books.MoreAlgebra.Unit69.dualNumberRing (k := k))
          (Formalization.Books.MoreAlgebra.Unit69.dualNumberRing (k := k)),
        ∀ (n : ℤ) (hn : n < 0),
          (e n (by omega)).hom ≫
              Formalization.Books.MoreAlgebra.Unit69.dualNumberMultiplication
                (k := k) =
            I.d n (n + 1) ≫ (e (n + 1) (by omega)).hom

/-- The dual-numbers module is represented by a left-infinite complex of
injectives, but does not have finite injective dimension.  The regular module
is injective, as stated in the source. -/
theorem dual_number_injective_example
    [HasDerivedCategory.{w}
      (ModuleCat.{u}
        (Formalization.Books.MoreAlgebra.Unit69.dualNumberRing (k := k)))] :
    ∃ I : BookComplex
        (ModuleCat.{u}
          (Formalization.Books.MoreAlgebra.Unit69.dualNumberRing (k := k))),
      IsDualNumberInjectiveResolutionShape (k := k) I ∧
        Nonempty
          ((DerivedCategory.Q (C := ModuleCat.{u}
            (Formalization.Books.MoreAlgebra.Unit69.dualNumberRing (k := k)))).obj I ≅
            DerivedObject
              (Formalization.Books.MoreAlgebra.Unit69.dualNumberModule
                (k := k))) ∧
        ¬ HasFiniteInjectiveDimension
          (R := Formalization.Books.MoreAlgebra.Unit69.dualNumberRing (k := k))
          (K := DerivedObject
            (Formalization.Books.MoreAlgebra.Unit69.dualNumberModule (k := k))) ∧
        Injective
          (ModuleCat.of
            (Formalization.Books.MoreAlgebra.Unit69.dualNumberRing (k := k))
            (Formalization.Books.MoreAlgebra.Unit69.dualNumberRing (k := k))) := by
  sorry

end DualNumbers

section FiniteInjectiveDimension

variable {R : Type u} [Ring R]
variable [HasDerivedCategory.{w} (ModuleCat.{u} R)]

/-! ## Finite injective dimension and bounded complexes -/

/-- A bounded derived object whose cohomology modules all have finite
injective dimension has finite injective dimension. -/
theorem finite_injective_dimension_of_bounded_cohomology
    (K : DBounded (ModuleCat.{u} R))
    (hK : ∀ i : ℤ,
      CategoryTheory.injectiveDimension
        ((derivedCohomologyFunctor (ModuleCat.{u} R) i).obj
          ((DerivedCategory.Bounded.ι (C := ModuleCat.{u} R)).obj K)) ≠ ⊤) :
    HasFiniteInjectiveDimension
      (R := R)
      (K := (DerivedCategory.Bounded.ι (C := ModuleCat.{u} R)).obj K) := by
  sorry

/-- A bounded complex whose terms all have finite injective dimension
represents an object of finite injective dimension. -/
theorem finite_injective_dimension_of_bounded_complex
    (K : DerivedCategory (ModuleCat.{u} R))
    (Kcomplex : BookComplex (ModuleCat.{u} R))
    (hRep : Nonempty
      ((DerivedCategory.Q (C := ModuleCat.{u} R)).obj Kcomplex ≅ K))
    (hBounded : IsBounded Kcomplex)
    (hTerms : ∀ i : ℤ,
      CategoryTheory.injectiveDimension (Kcomplex.X i) ≠ ⊤) :
    HasFiniteInjectiveDimension (R := R) (K := K) := by
  sorry

end FiniteInjectiveDimension

section NoetherianRadical

variable {R : Type u} [CommRing R] [IsNoetherianRing R]
variable [HasDerivedCategory.{w} (ModuleCat.{u} R)]

/-- Every cohomology module of `K ∈ D⁺(R)` is finite. -/
def HasFiniteCohomologyModules
    (K : DPlus (ModuleCat.{u} R)) : Prop :=
  ∀ i : ℤ, Module.Finite R
    ((moduleDerivedCohomology K i : Type u))

/-- The multiplication-and-quotient short exact sequence used in the
Noetherian-radical argument.  Its target quotient is the canonical
`R/(p, f)`, written as `R ⧸ (p ⊔ (f))`. -/
theorem noetherian_radical_multiplication_exact
    (p : Ideal R) [p.IsPrime] {f : R} (hf : f ∉ p) :
    Function.Injective (fun x : R ⧸ p => f • x) ∧
      Function.Exact
        (fun x : R ⧸ p => f • x)
        (Ideal.Quotient.factor
          (show p ≤ p ⊔ Ideal.span ({f} : Set R) from le_sup_left)) ∧
      Function.Surjective
        (Ideal.Quotient.factor
          (show p ≤ p ⊔ Ideal.span ({f} : Set R) from le_sup_left)) := by
  sorry

/-- The Noetherian-radical criterion for finite injective dimension. -/
theorem finite_injective_dimension_noetherian_radical
    (I : Ideal R) (hI : I ≤ Ring.jacobson R)
    (K : DPlus (ModuleCat.{u} R))
    (hK : HasFiniteCohomologyModules (R := R) K) :
    List.TFAE [
      HasFiniteInjectiveDimension (R := R)
        (K := (DerivedCategory.Plus.ι (C := ModuleCat.{u} R)).obj K),
      ∃ b : ℤ, ∀ J : Ideal R, I ≤ J → ∀ i : ℤ, b < i →
        DerivedExtVanishes
          (DerivedObject (ModuleCat.of R (R ⧸ J)))
          ((DerivedCategory.Plus.ι (C := ModuleCat.{u} R)).obj K) i] := by
  sorry

end NoetherianRadical

section NoetherianLocal

variable {R : Type u} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
variable [HasDerivedCategory.{w} (ModuleCat.{u} R)]

/-- The local Noetherian criterion, using Mathlib's canonical maximal ideal
and residue field. -/
theorem finite_injective_dimension_noetherian_local
    (K : DPlus (ModuleCat.{u} R))
    (hK : HasFiniteCohomologyModules (R := R) K) :
    List.TFAE [
      HasFiniteInjectiveDimension (R := R)
        (K := (DerivedCategory.Plus.ι (C := ModuleCat.{u} R)).obj K),
      ∃ b : ℤ, ∀ i : ℤ, b < i →
        DerivedExtVanishes
          (DerivedObject
            (ModuleCat.of R (IsLocalRing.ResidueField R)))
          ((DerivedCategory.Plus.ι (C := ModuleCat.{u} R)).obj K) i] := by
  sorry

end NoetherianLocal

end Formalization.Books.MoreAlgebra.Unit70
