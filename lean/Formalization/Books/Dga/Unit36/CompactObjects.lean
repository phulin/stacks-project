import Formalization.Books.Dga.Unit22.Core
import Formalization.Books.Derived.Unit37.CompactObjects
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# Differential Graded Algebra, Chapter 36: Characterizing compact objects

This file records the compactness, comparison, finite-filtration, and
boundedness interfaces used in the source section.  Differential graded
modules and the derived category are reused from Chapters 20--22, while
compactness is the canonical coproduct-comparison predicate from the earlier
Derived Categories formalization.
-/

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open Formalization.Books.Dga.Unit14
open Formalization.Books.Dga.Unit22
open Formalization.Books.Derived.Unit06
open Formalization.Books.Homology.Unit03

universe u v w wk vk

namespace Formalization.Books.Dga.Unit36

variable {R : Type u} {A : ℤ → Type v}
  [CommRing R]
  [∀ i, AddCommGroup (A i)] [∀ i, Module R (A i)]
  [DirectSum.GSemiring A] [DirectSum.GAlgebra R A]

variable {D : DifferentialGradedAlgebraData (R := R) (A := A)}
  {K : Type*} [Category K] [AdditiveCategory K]
  [HasShift K ℤ] [∀ n : ℤ, (shiftFunctor K n).Additive]
  [Pretriangulated K]

/-! ## The derived and homotopy objects attached to a DGA model -/

/-- The object of the derived category represented by a DG module. -/
abbrev dgDerivedObject (H : DgHomotopyCategoryModel (D := D) (K := K))
    (M : DGModule.{u,v,w} D) : DgDerivedCategory H :=
  (dgDerivedLocalization H).obj ((H.quotient).obj M)

/-- The derived morphism induced by a morphism of DG modules. -/
def dgDerivedMap (H : DgHomotopyCategoryModel (D := D) (K := K))
    {M N : DGModule.{u,v,w} D} (f : DGMap M N) :
    dgDerivedObject H M ⟶ dgDerivedObject H N :=
  (dgDerivedLocalization H).map ((H.quotient).map f)

/-! ## The comparison subcategory from the first source remark -/

/-- A DG module has the source's equality between homotopy and derived Homs.

The localization API expresses equality of the two Hom types by the
existence of a canonical equivalence between them.
-/
def DgHomotopyDerivedHomComparison
    (H : DgHomotopyCategoryModel (D := D) (K := K))
    (P : DGModule.{u,v,w} D) : Prop :=
  ∀ M : DGModule.{u,v,w} D,
    Nonempty
      (((H.quotient).obj P ⟶ (H.quotient).obj M) ≃
        (dgDerivedObject H P ⟶ dgDerivedObject H M))

/-- The object property on K(A,d) cut out by the comparison condition. -/
def dgComparisonObjects
    (H : DgHomotopyCategoryModel (D := D) (K := K)) :
    ObjectProperty (DgHomotopyCategory H) :=
  fun X =>
    ∃ P : DGModule.{u,v,w} D,
      Nonempty ((H.quotient).obj P ≅ X) ∧
        DgHomotopyDerivedHomComparison H P

/-- The comparison objects form the strictly full saturated triangulated
subcategory described in the source. -/
theorem dgComparisonObjects_properties
    (H : DgHomotopyCategoryModel (D := D) (K := K)) :
    IsStrictlyFullSaturatedPretriangulated (dgComparisonObjects H) := by
  sorry

/-- A graded-projective DG module is a comparison object as soon as its
homotopy Homs vanish on every acyclic DG module. -/
theorem dgHomotopyDerivedHomComparison_of_gradedProjective
    (H : DgHomotopyCategoryModel (D := D) (K := K))
    (P : DGModule.{u,v,w} D) (hP : IsGradedProjective P)
    (hvanish : ∀ M : DGModule.{u,v,w} D, DgAcyclic M →
      Formalization.Books.Dga.Unit20.HomotopyHomVanishes P M) :
    DgHomotopyDerivedHomComparison H P := by
  sorry

/-! The dual-number warning is retained as a reusable obstruction predicate.
It is deliberately separate from the general comparison theorem: the source
uses the example to warn that graded projectivity alone is not enough. -/

/-- A homotopy-category object is an acyclic nonzero-identity obstruction. -/
def IsAcyclicNonzeroIdentity
    (H : DgHomotopyCategoryModel (D := D) (K := K))
    [Preadditive (DgHomotopyCategory H)] (P : DGModule.{u,v,w} D) : Prop :=
  DgAcyclic P ∧
    ¬ ((𝟙 ((H.quotient).obj P) :
      (H.quotient).obj P ⟶ (H.quotient).obj P) = 0)

/-- The source's counterexample interface: a graded-projective DG module may
be an acyclic nonzero-identity obstruction. -/
structure GradedProjectiveAcyclicObstruction
    (H : DgHomotopyCategoryModel (D := D) (K := K))
    [Preadditive (DgHomotopyCategory H)] where
  object : DGModule.{u,v,w} D
  graded_projective : IsGradedProjective object
  obstruction : IsAcyclicNonzeroIdentity H object

/-- The concrete dual-number shape of the obstruction in the source remark.
The component equivalences encode Pⁿ = R, and differential_is_epsilon_mul
encodes the differential given by multiplication by the square-zero element
epsilon. -/
structure DualNumberPeriodicAcyclicData
    (k : Type u) [Field k]
    (H : DgHomotopyCategoryModel (D := D) (K := K))
    [Preadditive (DgHomotopyCategory H)] where
  dual_number_equiv :
    R ≃+* (Polynomial k ⧸
      Ideal.span ({Polynomial.X ^ 2} : Set (Polynomial k)))
  epsilon : R
  epsilon_spec :
    dual_number_equiv epsilon =
      Ideal.Quotient.mk _ Polynomial.X
  object : DGModule.{u,v,w} D
  component_equiv : ∀ n : ℤ,
    object.graded.component n ≃ₗ[R] R
  differential_is_epsilon_mul : ∀ (n : ℤ) (x : object.graded.component n),
    component_equiv (n + 1) (object.differential n x) =
      epsilon * component_equiv n x
  graded_projective : IsGradedProjective object
  acyclic : DgAcyclic object
  identity_nonzero :
    ¬ ((𝟙 ((H.quotient).obj object) :
      (H.quotient).obj object ⟶ (H.quotient).obj object) = 0)

/-- An acyclic nonzero-identity obstruction cannot satisfy the comparison
condition. -/
theorem not_comparison_of_acyclic_nonzero_identity
    (H : DgHomotopyCategoryModel (D := D) (K := K))
    [Preadditive (DgHomotopyCategory H)]
    (O : GradedProjectiveAcyclicObstruction H) :
    ¬ DgHomotopyDerivedHomComparison H O.object := by
  sorry

/-! ## Finite graded generation and finite shifted-free presentations -/

/-- The value of a finite homogeneous right-module combination in degree n.

The coefficient at a generator of degree degree i is taken in the
homogeneous component of degree n - degree i; gradedTransport only
reassociates the resulting degree.
-/
def finiteGradedCombination
    (M : DGModule.{u,v,w} D) {I : Type w} (degree : I → ℤ)
    (generator : ∀ i, M.graded.component (degree i))
    (n : ℤ) (s : Finset I) (coefficient : ∀ i, A (n - degree i)) :
    M.graded.component n :=
  s.sum (fun i =>
    gradedTransport (show degree i + (n - degree i) = n by omega)
      (M.graded.action (generator i) (coefficient i)))

/-- Finite homogeneous generators for a graded right A-module. -/
structure FiniteGradedGenerationData (M : DGModule.{u,v,w} D) where
  index : Type w
  index_finite : Finite index
  degree : index → ℤ
  generator : ∀ i, M.graded.component (degree i)
  spans : ∀ (n : ℤ) (x : M.graded.component n),
    ∃ (s : Finset index) (coefficient : ∀ i, A (n - degree i)),
      finiteGradedCombination M degree generator n s coefficient = x

/-- A DG module is finite as a graded right module. -/
def IsFiniteGradedModule (M : DGModule.{u,v,w} D) : Prop :=
  Nonempty (FiniteGradedGenerationData M)

/-- A finite graded-projective DG module, in the terminology of the source. -/
def IsFiniteGradedProjective (M : DGModule.{u,v,w} D) : Prop :=
  IsFiniteGradedModule M ∧ IsGradedProjective M

/-- A presentation of a DG module by a direct sum of shifts of A. -/
structure DgShiftedFreePresentation (P : DGModule.{u,v,w} D) where
  index : Type w
  degree : index → ℤ
  sum : Formalization.Books.Dga.Unit20.DgDirectSum.{u, v, w, w, v} D
    (fun i => differentialGradedAlgebraShift D (degree i))
  iso : Nonempty (P ≅ sum.object)

/-- A presentation by a finite direct sum of shifts of A. -/
structure DgFiniteShiftedFreePresentation (P : DGModule.{u,v,w} D)
    extends DgShiftedFreePresentation P where
  index_finite : Finite index

/-- A finite direct sum of shifts of the regular DG module. -/
def IsDgFiniteShiftedFree (P : DGModule.{u,v,w} D) : Prop :=
  Nonempty (DgFiniteShiftedFreePresentation P)

/-- An arbitrary direct sum of shifts of the regular DG module. -/
def IsDgShiftedFree (P : DGModule.{u,v,w} D) : Prop :=
  Nonempty (DgShiftedFreePresentation P)

/-- A finite shifted-free presentation obtained by selecting finitely many
summands from a specified shifted-free presentation. -/
structure DgSelectedFiniteShiftedFreePresentation
    {P Q : DGModule.{u,v,w} D} (S : DgShiftedFreePresentation P) where
  index : Type w
  index_finite : Finite index
  embed : index → S.index
  embed_injective : Function.Injective embed
  degree : index → ℤ
  degree_selected : ∀ i, degree i = S.degree (embed i)
  sum : Formalization.Books.Dga.Unit20.DgDirectSum.{u, v, w, w, v} D
    (fun i => differentialGradedAlgebraShift D (degree i))
  iso : Nonempty (P ≅ sum.object)

/-! ## Finite filtrations -/

/-- A finite filtration by DG submodules whose successive quotients are
finite direct sums of shifts of A.

Stage 0 is F₋₁ and the last stage is Fₙ, matching the source indexing.
Stage maps and their degreewise injectivity encode submodule inclusions;
the exact sequences encode the quotients.
-/
structure FiniteDgFiltration (P : DGModule.{u,v,w} D) where
  length : ℕ
  stage : Fin (length + 2) → DGModule.{u,v,w} D
  stage_map : ∀ i, DGMap (stage i) P
  stage_map_injective : ∀ (i : Fin (length + 2)) (n : ℤ),
    Function.Injective ((stage_map i).underlying.app n)
  inclusion : ∀ i : Fin (length + 1),
    DGMap (stage i.castSucc) (stage i.succ)
  inclusion_injective : ∀ (i : Fin (length + 1)) (n : ℤ),
    Function.Injective ((inclusion i).underlying.app n)
  stage_map_comm : ∀ i : Fin (length + 1),
    DifferentialGradedModuleHom.comp (inclusion i) (stage_map i.succ) =
      stage_map i.castSucc
  zero_stage : Nonempty
    (stage ⟨0, by omega⟩ ≅ Formalization.Books.Dga.Unit20.dgZeroModule D)
  top_stage : Nonempty (stage ⟨length + 1, by omega⟩ ≅ P)
  quotient : ∀ _i : Fin (length + 1), DGModule.{u,v,w} D
  quotient_map : ∀ i : Fin (length + 1),
    DGMap (stage i.succ) (quotient i)
  quotient_exact : ∀ i : Fin (length + 1),
    Formalization.Books.Dga.Unit20.IsExactPair (inclusion i) (quotient_map i)
  quotient_presentation : ∀ i : Fin (length + 1),
    DgShiftedFreePresentation (quotient i)

/-- A finite filtration whose successive quotients are finite direct sums of
shifts of the regular DG module. -/
structure FiniteDgFiltrationWithFiniteQuotients
    (P : DGModule.{u,v,w} D) extends FiniteDgFiltration P where
  quotient_finite : ∀ i : Fin (toFiniteDgFiltration.length + 1),
    IsDgFiniteShiftedFree (toFiniteDgFiltration.quotient i)

/-- A categorical pullback square, used to express an intersection of
submodules without introducing a second DG-module subobject API. -/
def IsPullbackSquare {C : Type*} [Category C]
    {X Y Z T : C} (f : X ⟶ Y) (g : X ⟶ Z)
    (a : Y ⟶ T) (b : Z ⟶ T) : Prop :=
  f ≫ a = g ≫ b ∧
    ∀ (W : C) (u : W ⟶ Y) (v : W ⟶ Z),
      u ≫ a = v ≫ b →
        ∃! w : W ⟶ X, w ≫ f = u ∧ w ≫ g = v

/-- A finite filtered submodule of P, with its stages identified as the
intersections with the stages of the original filtration. -/
def IsFiniteFilteredSubmodule
    {P P' : DGModule.{u,v,w} D} (F : FiniteDgFiltration P)
    (F' : FiniteDgFiltrationWithFiniteQuotients P')
    (inclusion : DGMap P' P) : Prop :=
  (∀ n : ℤ, Function.Injective (inclusion.underlying.app n)) ∧
  ∃ h : F'.length = F.length,
    (∀ i : Fin (F.length + 2),
      ∃ f : DGMap.{u,v,w}
          (F'.toFiniteDgFiltration.stage
            (Fin.cast (congrArg (fun n => n + 2) h.symm) i))
          (F.stage i),
        DifferentialGradedModuleHom.comp f (F.stage_map i) =
          DifferentialGradedModuleHom.comp
            (F'.toFiniteDgFiltration.stage_map
              (Fin.cast (congrArg (fun n => n + 2) h.symm) i))
            inclusion ∧
        IsPullbackSquare
          (X := F'.toFiniteDgFiltration.stage
            (Fin.cast (congrArg (fun n => n + 2) h.symm) i))
          (Y := F.stage i) (Z := P') (T := P) f
          (F'.toFiniteDgFiltration.stage_map
            (Fin.cast (congrArg (fun n => n + 2) h.symm) i))
          (F.stage_map i) inclusion) ∧
    (∀ i : Fin (F.length + 1),
      IsDgFiniteShiftedFree
        (F'.toFiniteDgFiltration.quotient
          (Fin.cast (congrArg (fun n => n + 1) h.symm) i))) ∧
    (∀ i : Fin (F.length + 1),
      Nonempty (DgSelectedFiniteShiftedFreePresentation
        (P := F.quotient i)
        (Q := F'.toFiniteDgFiltration.quotient
          (Fin.cast (congrArg (fun n => n + 1) h.symm) i))
        (F.quotient_presentation i)))

/-! ## Compactness and factorization -/

variable (H : DgHomotopyCategoryModel (D := D) (K := K))

/-- A direct-summand relation in a category. -/
def IsDirectSummand {C : Type*} [Category C] (E X : C) : Prop :=
  ∃ (i : E ⟶ X) (r : X ⟶ E), i ≫ r = 𝟙 E

/-- Compactness of a derived object, reusing the canonical coproduct API. -/
abbrev DgCompactObject
    [AdditiveCategory (DgDerivedCategory H)]
    [HasCoproducts (DgDerivedCategory H)]
    (E : DgDerivedCategory H) : Prop :=
  Formalization.Books.Derived.Unit37.IsCompactObject E

/-- A morphism in the derived category is zero, in the source's Hom-set
language, when its Hom type is subsingleton. -/
def DgDerivedHomVanishes
    [Preadditive (DgDerivedCategory H)]
    (E X : DgDerivedCategory H) : Prop :=
  Subsingleton (E ⟶ X)

/-- The bounded-cohomology condition used by the compactness lemma. -/
def DgCohomologyVanishingOnInterval (M : DGModule.{u,v,w} D) (a b : ℤ) : Prop :=
  ∀ i : ℤ, a ≤ i → i ≤ b → Subsingleton (dgCohomology M i)

/-- Compact objects admit a finite cohomological detection interval. -/
theorem compact_object_implies_bounded_interval
    [AdditiveCategory (DgDerivedCategory H)]
    [HasCoproducts (DgDerivedCategory H)]
    (E : DgDerivedCategory H) (hE : DgCompactObject H E) :
    ∃ a b : ℤ, a ≤ b ∧
      ∀ M : DGModule.{u,v,w} D,
        DgCohomologyVanishingOnInterval M a b →
          DgDerivedHomVanishes H E (dgDerivedObject H M) := by
  sorry

/-- Every compact object is a direct summand of a finite-filtered DG module. -/
theorem compact_object_iff_direct_summand_finite_filtered
    [AdditiveCategory (DgDerivedCategory H)]
    [HasCoproducts (DgDerivedCategory H)]
    (hProducts : DgDerivedProductsData H)
    (E : DgDerivedCategory H) :
    DgCompactObject H E ↔
      ∃ (P : DGModule.{u,v,w} D)
        (F : FiniteDgFiltrationWithFiniteQuotients P),
        IsDirectSummand E (dgDerivedObject H P) := by
  sorry

/-- A compact map into a finite-filtered DG module factors through a finite
filtered submodule whose successive quotients use finite subsets of the
original shifted-free summands. -/
theorem compact_map_factors_through_finite_filtered_submodule
    [AdditiveCategory (DgDerivedCategory H)]
    [HasCoproducts (DgDerivedCategory H)]
    (E : DgDerivedCategory H) (hE : DgCompactObject H E)
    (P : DGModule.{u,v,w} D) (F : FiniteDgFiltration P)
    (f : E ⟶ dgDerivedObject H P) :
    ∃ (P' : DGModule.{u,v,w} D)
      (F' : FiniteDgFiltrationWithFiniteQuotients P')
      (inclusion : DGMap P' P),
      IsFiniteFilteredSubmodule F F' inclusion ∧
        ∃ g : E ⟶ dgDerivedObject H P',
          f = g ≫ dgDerivedMap H inclusion := by
  sorry

/-! ## Finite graded-projective modules and compactness -/

/-- The conditional compactness assertion posed in the source's second
remark, recorded as a proposition rather than asserted as a theorem. -/
def AllFiniteGradedProjectivesCompact
    [AdditiveCategory (DgDerivedCategory H)]
    [HasCoproducts (DgDerivedCategory H)] : Prop :=
  ∀ P : DGModule.{u,v,w} D, IsFiniteGradedProjective P →
    DgCompactObject H (dgDerivedObject H P)

/-- A witness for the source's warning that compact objects need not all be
represented by finite graded-projective DG modules.  The source points to a
later examples section for such witnesses, so Chapter 36 records the exact
interface without importing that later material. -/
structure CompactObjectNotFiniteGradedProjective
    [AdditiveCategory (DgDerivedCategory H)]
    [HasCoproducts (DgDerivedCategory H)] where
  object : DgDerivedCategory H
  compact : DgCompactObject H object
  not_represented :
    ¬ ∃ P : DGModule.{u,v,w} D,
      Nonempty (dgDerivedObject H P ≅ object) ∧
        IsFiniteGradedProjective P

/-- A finite graded-projective comparison object is compact. -/
theorem finite_graded_projective_comparison_is_compact
    [AdditiveCategory (DgDerivedCategory H)]
    [HasCoproducts (DgDerivedCategory H)]
    (P : DGModule.{u,v,w} D) (hP : IsFiniteGradedProjective P)
    (hComparison : DgHomotopyDerivedHomComparison H P) :
    DgCompactObject H (dgDerivedObject H P) := by
  sorry

/-! ## The finite-degree hypothesis and the precise compactness criterion -/

/-- The graded algebra is bounded in degree. -/
def IsDegreewiseBounded : Prop :=
  ∃ c : ℕ, 0 < c ∧
    ∀ n : ℤ, c ≤ n.natAbs → Subsingleton (A n)

/-- Under degreewise boundedness, compact objects are precisely represented by
finite graded-projective comparison modules. -/
theorem compact_object_iff_finite_graded_projective_comparison
    [AdditiveCategory (DgDerivedCategory H)]
    [HasCoproducts (DgDerivedCategory H)]
    (hA : IsDegreewiseBounded (A := A))
    (E : DgDerivedCategory H) :
    DgCompactObject H E ↔
      ∃ P : DGModule.{u,v,w} D,
        Nonempty (dgDerivedObject H P ≅ E) ∧
        IsFiniteGradedProjective P ∧
        DgHomotopyDerivedHomComparison H P := by
  sorry

/-! ## Source-order support interfaces -/

/-- A positive degree bound usable in the proof of the finite-degree criterion. -/
structure DegreeBoundWitness where
  bound : ℕ
  positive : 0 < bound
  vanishes : ∀ n : ℤ, bound ≤ n.natAbs → Subsingleton (A n)

/-- The source's choice of a separation integer n for a cohomological window. -/
def HasSeparationInteger (a b c : ℤ) : Prop :=
  ∃ n : ℕ, 0 < n ∧ b + 4 * c - n < a

end Formalization.Books.Dga.Unit36
