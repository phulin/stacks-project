import Mathlib.Algebra.Module.LinearMap.End
import Mathlib.Algebra.Module.LocalizedModule.Basic
import Mathlib.LinearAlgebra.Finsupp.LSum
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.RingTheory.Localization.Basic
import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.RingTheory.TensorProduct.Maps
import Formalization.Books.Algebra.Unit131.Differentials
import Formalization.Books.Algebra.Unit132.DeRhamComplex

/-!
# Commutative Algebra, Chapter 133: Finite order differential operators

The source's `Diff^k_{S/R}(M, N)` is represented by the submodule of
`R`-linear maps whose iterated commutators with multiplication by elements of
`S` have the prescribed order.  The module of principal parts is represented
by the quotient of the free `S`-module on `M` by the source's generators and
relations.  Statements whose proof is the substantial mathematical content of
the chapter are intentionally left as theorem interfaces at this stage.
-/

namespace Formalization.Books.Algebra.Unit133

open scoped TensorProduct
open Formalization.Books.Algebra.Unit131
open Formalization.Books.Algebra.Unit132

attribute [local instance] SMulCommClass.of_commMonoid

noncomputable section

universe u v w u' v' w'

/-! ## Differential operators and their filtration -/

section DifferentialOperators

variable {R S M N : Type*} [CommRing R] [CommRing S] [Algebra R S]
  [AddCommGroup M] [AddCommGroup N]
  [Module S M] [Module S N] [Module R M] [Module R N]
  [IsScalarTower R S M] [IsScalarTower R S N]

/- The commutator with multiplication by `s`. -/
def differentialOperatorCommutator (D : M →ₗ[R] N) (s : S) : M →ₗ[R] N :=
  D.comp (DistribSMul.toLinearMap R M s) -
    (DistribSMul.toLinearMap R N s).comp D

/- The source's inductive predicate, with the order-zero clause made
   explicit instead of referring to `k - 1`. -/
def IsDifferentialOperator
    {R S M N : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup M] [AddCommGroup N]
    [Module S M] [Module S N] [Module R M] [Module R N]
    [IsScalarTower R S M] [IsScalarTower R S N] :
    ℕ → (M →ₗ[R] N) → Prop
  | 0, D => ∀ (s : S) (m : M), D (s • m) = s • D m
  | k + 1, D => ∀ (s : S),
      IsDifferentialOperator (R := R) (S := S) (M := M) (N := N) k
        (differentialOperatorCommutator D s)

theorem isDifferentialOperator_zero (k : ℕ) :
    IsDifferentialOperator (R := R) (S := S) k (0 : M →ₗ[R] N) := by
  sorry

theorem isDifferentialOperator_add (k : ℕ) (D E : M →ₗ[R] N)
    (hD : IsDifferentialOperator (R := R) (S := S) k D)
    (hE : IsDifferentialOperator (R := R) (S := S) k E) :
    IsDifferentialOperator (R := R) (S := S) k (D + E) := by
  sorry

theorem isDifferentialOperator_smul (k : ℕ) (c : S) (D : M →ₗ[R] N)
    (hD : IsDifferentialOperator (R := R) (S := S) k D) :
    IsDifferentialOperator (R := R) (S := S) k (c • D) := by
  sorry

/- The space `Diff^k_{S/R}(M, N)`, as an actual `S`-submodule. -/
def differentialOperatorSubmodule (k : ℕ) : Submodule S (M →ₗ[R] N) where
  carrier := {D | IsDifferentialOperator (R := R) (S := S) k D}
  zero_mem' := isDifferentialOperator_zero (R := R) (S := S) k
  add_mem' := by
    intro D E hD hE
    change IsDifferentialOperator (R := R) (S := S) k D at hD
    change IsDifferentialOperator (R := R) (S := S) k E at hE
    change IsDifferentialOperator (R := R) (S := S) k (D + E)
    exact isDifferentialOperator_add (R := R) (S := S) k D E hD hE
  smul_mem' := by
    intro c D hD
    change IsDifferentialOperator (R := R) (S := S) k D at hD
    change IsDifferentialOperator (R := R) (S := S) k (c • D)
    exact isDifferentialOperator_smul (R := R) (S := S) k c D hD

/-- Differential operators of order `k`, with their underlying `R`-linear map. -/
abbrev DifferentialOperator (k : ℕ) : Submodule S (M →ₗ[R] N) :=
  differentialOperatorSubmodule (R := R) (S := S) k

theorem mem_differentialOperatorSubmodule_iff (k : ℕ) (D : M →ₗ[R] N) :
    D ∈ differentialOperatorSubmodule (R := R) (S := S) k ↔
      IsDifferentialOperator (R := R) (S := S) k D :=
  Iff.rfl

theorem differentialOperatorSubmodule_mono (k : ℕ) :
    differentialOperatorSubmodule (R := R) (S := S) (M := M) (N := N) k ≤
      differentialOperatorSubmodule (R := R) (S := S) (M := M) (N := N) (k + 1) := by
  sorry

theorem differentialOperatorSubmodule_zero_iff (D : M →ₗ[R] N) :
    D ∈ differentialOperatorSubmodule (R := R) (S := S) 0 ↔
      ∀ (s : S) (m : M), D (s • m) = s • D m :=
  Iff.rfl

theorem differentialOperator_subtype_coe (k : ℕ)
    (D : DifferentialOperator (R := R) (S := S) (M := M) (N := N) k) :
    IsDifferentialOperator (R := R) (S := S) k D.1 :=
  D.2

theorem differentialOperator_comp_isDifferentialOperator
    {L : Type*} [AddCommGroup L] [Module S L] [Module R L]
    [IsScalarTower R S L]
    (k k' : ℕ) (D : M →ₗ[R] N) (D' : N →ₗ[R] L)
    (hD : IsDifferentialOperator (R := R) (S := S) k D)
    (hD' : IsDifferentialOperator (R := R) (S := S) k' D') :
    IsDifferentialOperator (R := R) (S := S) (k + k') (D'.comp D) := by
  sorry

theorem differentialOperator_postcompose_isDifferentialOperator
    {N' : Type*} [AddCommGroup N'] [Module S N'] [Module R N']
    [IsScalarTower R S N'] (k : ℕ) (D : M →ₗ[R] N)
    (f : N →ₗ[S] N')
    (hD : IsDifferentialOperator (R := R) (S := S) k D) :
    IsDifferentialOperator (R := R) (S := S) k
      ((f.restrictScalars R).comp D) := by
  sorry

/- Bundled versions of the two operations used repeatedly below. -/
def differentialOperatorComp
    {L : Type*} [AddCommGroup L] [Module S L] [Module R L]
    [IsScalarTower R S L]
    {k k' : ℕ}
    (D' : DifferentialOperator (R := R) (S := S) (M := N) (N := L) k')
    (D : differentialOperatorSubmodule (R := R) (S := S) (M := M) (N := N) k) :
    differentialOperatorSubmodule (R := R) (S := S) (M := M) (N := L) (k + k') :=
  ⟨D'.1.comp D.1,
    differentialOperator_comp_isDifferentialOperator (R := R) (S := S)
      k k' D.1 D'.1 D.2 D'.2⟩

def differentialOperatorPostcompose
    {N' : Type*} [AddCommGroup N'] [Module S N'] [Module R N']
    [IsScalarTower R S N'] {k : ℕ}
    (f : N →ₗ[S] N')
    (D : DifferentialOperator (R := R) (S := S) (M := M) (N := N) k) :
    differentialOperatorSubmodule (R := R) (S := S) (M := M) (N := N') k :=
  ⟨(f.restrictScalars R).comp D.1,
    differentialOperator_postcompose_isDifferentialOperator
      (R := R) (S := S) k D.1 f D.2⟩

theorem differentialOperator_comp_order_add
    {L : Type*} [AddCommGroup L] [Module S L] [Module R L]
    [IsScalarTower R S L]
    {k k' : ℕ}
    (D : differentialOperatorSubmodule (R := R) (S := S) (M := M) (N := N) k)
    (D' : DifferentialOperator (R := R) (S := S) (M := N) (N := L) k') :
    IsDifferentialOperator (R := R) (S := S) (k + k') (D'.1.comp D.1) :=
  (differentialOperatorComp D' D).2

end DifferentialOperators

/-! ## The module of principal parts -/

section PrincipalParts

variable {R S M N : Type*} [CommRing R] [CommRing S] [Algebra R S]
  [AddCommGroup M] [Module S M] [Module R M]
  [IsScalarTower R S M]

include R

def principalPartsAddRelation (m m' : M) : M →₀ S :=
  Finsupp.single (m + m') 1 - Finsupp.single m 1 - Finsupp.single m' 1

def principalPartsScalarRelation (r : R) (m : M) : M →₀ S :=
  (algebraMap R S r) • Finsupp.single m 1 - Finsupp.single (r • m) 1

def principalPartsHigherRelation (k : ℕ) (g : Fin (k + 1) → S) (m : M) : M →₀ S := by
  classical
  exact (Finset.univ : Finset (Finset (Fin (k + 1)))).sum (fun t =>
    ((-1 : S) ^ t.card) •
      (((Finset.univ \ t).prod g) •
        Finsupp.single ((t.prod g) • m) 1))

def principalPartsRelationSet (k : ℕ) : Set (M →₀ S) :=
  Set.range (fun p : M × M => principalPartsAddRelation p.1 p.2) ∪
    Set.range (fun p : R × M => principalPartsScalarRelation p.1 p.2) ∪
    Set.range (fun p : (Fin (k + 1) → S) × M =>
      principalPartsHigherRelation k p.1 p.2)

def principalPartsRelationSubmodule (k : ℕ) : Submodule S (M →₀ S) :=
  Submodule.span S (principalPartsRelationSet (R := R) (S := S) (M := M) k)

/-- The quotient construction of the module of principal parts. -/
abbrev PrincipalParts (k : ℕ) : Type _ :=
  (M →₀ S) ⧸ principalPartsRelationSubmodule (R := R) (S := S) (M := M) k

theorem principalParts_relation_succ_le (k : ℕ) :
    principalPartsRelationSubmodule (R := R) (S := S) (M := M) (k + 1) ≤
      principalPartsRelationSubmodule (R := R) (S := S) (M := M) k := by
  sorry

noncomputable def principalPartsTransition (k : ℕ) :
    PrincipalParts (R := R) (S := S) (M := M) (k + 1) →ₗ[S]
      PrincipalParts (R := R) (S := S) (M := M) k :=
  Submodule.factor (principalParts_relation_succ_le (R := R) (S := S) (M := M) k)

theorem principalPartsTransition_on_generator (k : ℕ) (m : M) :
    principalPartsTransition (R := R) (S := S) (M := M) k
        (Submodule.mkQ _ (Finsupp.single m 1)) =
      Submodule.mkQ _ (Finsupp.single m 1) := by
  rfl

def principalPartsGenerator (k : ℕ) (m : M) :
    PrincipalParts (R := R) (S := S) (M := M) k :=
  Submodule.mkQ _ (Finsupp.single m 1)

theorem principalParts_universal_linear_map_exists (k : ℕ) :
    ∃ u : M →ₗ[R] PrincipalParts (R := R) (S := S) (M := M) k,
      (∀ m, u m = principalPartsGenerator (R := R) (S := S) (M := M) k m) ∧
      IsDifferentialOperator (R := R) (S := S) k u := by
  sorry

noncomputable def principalPartsUniversalLinearMap (k : ℕ) :
    M →ₗ[R] PrincipalParts (R := R) (S := S) (M := M) k :=
  Classical.choose (principalParts_universal_linear_map_exists (R := R) (S := S) (M := M) k)

theorem principalPartsUniversalLinearMap_apply (k : ℕ) (m : M) :
    principalPartsUniversalLinearMap (R := R) (S := S) (M := M) k m =
      principalPartsGenerator (R := R) (S := S) (M := M) k m :=
  (Classical.choose_spec
    (principalParts_universal_linear_map_exists (R := R) (S := S) (M := M) k)).1 m

theorem principalPartsUniversalLinearMap_isDifferentialOperator (k : ℕ) :
    IsDifferentialOperator (R := R) (S := S) k
      (principalPartsUniversalLinearMap (R := R) (S := S) (M := M) k) :=
  (Classical.choose_spec
    (principalParts_universal_linear_map_exists (R := R) (S := S) (M := M) k)).2

abbrev principalPartsUniversal (k : ℕ) :
    differentialOperatorSubmodule (R := R) (S := S) (M := M)
      (N := PrincipalParts (R := R) (S := S) (M := M) k) k :=
  ⟨principalPartsUniversalLinearMap (R := R) (S := S) (M := M) k,
    principalPartsUniversalLinearMap_isDifferentialOperator (R := R) (S := S) (M := M) k⟩

theorem principalParts_universal_property_exists (k : ℕ) (N : Type*)
    [AddCommGroup N] [Module S N] [Module R N] [IsScalarTower R S N] :
    Nonempty
      (↥(differentialOperatorSubmodule (R := R) (S := S) (M := M) (N := N) k)
        ≃ₗ[S]
        (PrincipalParts (R := R) (S := S) (M := M) k →ₗ[S] N)) := by
  sorry

noncomputable def principalPartsHomEquiv (k : ℕ)
    (N : Type*) [AddCommGroup N] [Module S N] [Module R N] [IsScalarTower R S N] :
    differentialOperatorSubmodule (R := R) (S := S) (M := M) (N := N) k ≃ₗ[S]
      (PrincipalParts (R := R) (S := S) (M := M) k →ₗ[S] N) :=
  Classical.choice
    (principalParts_universal_property_exists (S := S) (M := M) k N)

theorem principalParts_factorization_unique (k : ℕ) (N : Type*)
    [AddCommGroup N] [Module S N] [Module R N] [IsScalarTower R S N]
    (D : differentialOperatorSubmodule (R := R) (S := S) (M := M) (N := N) k) :
    ∃! α : PrincipalParts (R := R) (S := S) (M := M) k →ₗ[S] N,
      (α.restrictScalars R).comp
          (principalPartsUniversalLinearMap (R := R) (S := S) (M := M) k) = D.1 := by
  sorry

theorem principalPartsHomEquiv_natural (k : ℕ)
    {N N' : Type*} [AddCommGroup N] [AddCommGroup N']
    [Module S N] [Module S N'] [Module R N] [Module R N']
    [IsScalarTower R S N] [IsScalarTower R S N'] (f : N →ₗ[S] N')
    (D : differentialOperatorSubmodule (R := R) (S := S) (M := M) (N := N) k) :
    principalPartsHomEquiv (R := R) (S := S) (M := M) k N'
        (differentialOperatorPostcompose f D) =
      f.comp (principalPartsHomEquiv (R := R) (S := S) (M := M) k N D) := by
  sorry

/- The map to `M` obtained by sending `[m]` to `m`. -/
noncomputable def principalPartsFreeEvaluation : (M →₀ S) →ₗ[S] M :=
  Finsupp.lsum S (α := M) (M := S) (N := M)
    (fun m : M => ((LinearMap.id : S →ₗ[S] S).smulRight m))

theorem principalParts_relation_le_ker_evaluation (k : ℕ) :
    principalPartsRelationSubmodule (R := R) (S := S) (M := M) k ≤
      LinearMap.ker (principalPartsFreeEvaluation (S := S) (M := M)) := by
  sorry

noncomputable def principalPartsProjection (k : ℕ) :
    PrincipalParts (R := R) (S := S) (M := M) k →ₗ[S] M :=
  Submodule.liftQ _ (principalPartsFreeEvaluation (S := S) (M := M))
    (principalParts_relation_le_ker_evaluation (R := R) (S := S) (M := M) k)

theorem principalPartsProjection_on_generator (k : ℕ) (m : M) :
    principalPartsProjection (R := R) (S := S) (M := M) k
        (principalPartsGenerator (R := R) (S := S) (M := M) k m) = m := by
  sorry

theorem principalParts_zero_equiv_exists :
    Nonempty (PrincipalParts (R := R) (S := S) (M := M) 0 ≃ₗ[S] M) := by
  sorry

noncomputable def principalPartsZeroEquiv :
    PrincipalParts (R := R) (S := S) (M := M) 0 ≃ₗ[S] M :=
  Classical.choice (principalParts_zero_equiv_exists (R := R) (S := S) (M := M))

theorem principalParts_zero_equiv_agrees_with_projection :
    (principalPartsZeroEquiv (R := R) (S := S) (M := M)).toLinearMap =
      principalPartsProjection (R := R) (S := S) (M := M) 0 := by
  sorry

end PrincipalParts

/-! ## Derivations and the order-one example -/

section OrderOneExample

variable {R S N : Type*} [CommRing R] [CommRing S] [Algebra R S]
  [AddCommGroup N] [Module S N] [Module R N] [IsScalarTower R S N]

def scalarValueLinearMap (x : N) : S →ₗ[S] N :=
  (LinearMap.id : S →ₗ[S] S).smulRight x

def differentialOperatorDerivationFormula
    (D : differentialOperatorSubmodule (R := R) (S := S) (M := S) (N := N) 1) (g : S) : N :=
  D.1 g - g • D.1 1

theorem differentialOperator_order_one_derivation_decomposition
    (D : differentialOperatorSubmodule (R := R) (S := S) (M := S) (N := N) 1) :
    ∃ σ : Derivation R S N,
      (∀ g, σ g = differentialOperatorDerivationFormula (R := R) (S := S) D g) ∧
      (∀ g, D.1 g = σ g + scalarValueLinearMap (S := S) (N := N) (D.1 1) g) := by
  sorry

theorem differentialOperator_order_one_ring_equiv_exists :
    Nonempty
      (differentialOperatorSubmodule (R := R) (S := S) (M := S) (N := N) 1 ≃ₗ[S]
        (Derivation R S N × N)) := by
  sorry

theorem principalParts_one_equiv_differentials_prod :
    Nonempty
      (PrincipalParts (R := R) (S := S) 1 (M := S) ≃ₗ[S]
        (ModuleOfDifferentials R S × S)) := by
  sorry

end OrderOneExample

/-! ## The sequence of principal parts -/

section PrincipalPartsSequence

variable {R S M : Type*} [CommRing R] [CommRing S] [Algebra R S]
  [AddCommGroup M] [Module S M] [Module R M] [IsScalarTower R S M]

theorem principalParts_sequence_left_exists :
    ∃ i : (ModuleOfDifferentials R S) ⊗[S] M →ₗ[S]
          PrincipalParts (R := R) (S := S) (M := M) 1,
      Function.Exact i (principalPartsProjection (R := R) (S := S) (M := M) 1) ∧
        Function.Injective i ∧
        Function.Surjective (principalPartsProjection (R := R) (S := S) (M := M) 1) := by
  sorry

noncomputable def principalPartsSequenceLeft :
    (ModuleOfDifferentials R S) ⊗[S] M →ₗ[S]
      PrincipalParts (R := R) (S := S) (M := M) 1 :=
  Classical.choose (principalParts_sequence_left_exists (R := R) (S := S) (M := M))

theorem principalParts_sequence_exact :
    Function.Exact (principalPartsSequenceLeft (R := R) (S := S) (M := M))
      (principalPartsProjection (R := R) (S := S) (M := M) 1) :=
  (Classical.choose_spec (principalParts_sequence_left_exists (R := R) (S := S) (M := M))).1

theorem principalParts_sequence_left_injective :
    Function.Injective (principalPartsSequenceLeft (R := R) (S := S) (M := M)) :=
  (Classical.choose_spec (principalParts_sequence_left_exists (R := R) (S := S) (M := M))).2.1

theorem principalParts_sequence_right_surjective :
    Function.Surjective (principalPartsProjection (R := R) (S := S) (M := M) 1) :=
  (Classical.choose_spec (principalParts_sequence_left_exists (R := R) (S := S) (M := M))).2.2

structure PrincipalPartsShortExactSequence where
  left : (ModuleOfDifferentials R S) ⊗[S] M →ₗ[S]
    PrincipalParts (R := R) (S := S) (M := M) 1
  right : PrincipalParts (R := R) (S := S) (M := M) 1 →ₗ[S] M
  left_eq : left = principalPartsSequenceLeft (R := R) (S := S) (M := M)
  right_eq : right = principalPartsProjection (R := R) (S := S) (M := M) 1
  exact : Function.Exact left right
  left_injective : Function.Injective left
  right_surjective : Function.Surjective right

noncomputable def principalPartsSequence : PrincipalPartsShortExactSequence
    (R := R) (S := S) (M := M) :=
  { left := principalPartsSequenceLeft (R := R) (S := S) (M := M)
    right := principalPartsProjection (R := R) (S := S) (M := M) 1
    left_eq := rfl
    right_eq := rfl
    exact := principalParts_sequence_exact (R := R) (S := S) (M := M)
    left_injective := principalParts_sequence_left_injective (R := R) (S := S) (M := M)
    right_surjective := principalParts_sequence_right_surjective (R := R) (S := S) (M := M) }

end PrincipalPartsSequence

/-! ## Functoriality and base change -/

section PrincipalPartsFunctoriality

variable {A A' B B' M M' : Type*}
  [CommRing A] [CommRing A'] [CommRing B] [CommRing B']
  [Algebra A B] [Algebra A A'] [Algebra B B'] [Algebra A' B']
  [AddCommGroup M] [Module B M] [Module A M] [IsScalarTower A B M]
  [AddCommGroup M'] [Module B' M'] [Module A' M'] [IsScalarTower A' B' M']

/-- The data carried by the functoriality statement for principal parts.

The source calls the map on `M` `B`-linear.  Since the target has its
`B`-action induced through `B → B'`, `f_smul` records that statement
without requiring a second, potentially ambiguous `Module B M'` instance.
-/
structure PrincipalPartsFunctoriality where
  f : M →+ M'
  f_smul : ∀ b m, f (b • m) = algebraMap B B' b • f m
  commutes :
    (algebraMap A' B').comp (algebraMap A A') =
      (algebraMap B B').comp (algebraMap A B)
  map : ∀ k, PrincipalParts (R := A) (S := B) (M := M) k →+
    PrincipalParts (R := A') (S := B') (M := M') k
  map_zero : ∀ k, map k 0 = 0
  map_add : ∀ k x y, map k (x + y) = map k x + map k y
  map_smul : ∀ k b x, map k (b • x) = algebraMap B B' b • map k x
  map_generator : ∀ k m,
    map k (principalPartsGenerator (R := A) (S := B) k m) =
      principalPartsGenerator (R := A') (S := B') k (f m)
  map_transition : ∀ k x,
    map k (principalPartsTransition (R := A) (S := B) k x) =
      principalPartsTransition (R := A') (S := B') k (map (k + 1) x)

theorem principalParts_functoriality_exists
    (f : M →+ M')
    (hf : ∀ b m, f (b • m) = algebraMap B B' b • f m)
    (hcomm :
      (algebraMap A' B').comp (algebraMap A A') =
        (algebraMap B B').comp (algebraMap A B)) :
    Nonempty (PrincipalPartsFunctoriality (A := A) (A' := A') (B := B) (B' := B')
      (M := M) (M' := M')) := by
  sorry

def principalPartsFunctorialitySequenceCompatible
    (F : PrincipalPartsFunctoriality (A := A) (A' := A') (B := B) (B' := B')
      (M := M) (M' := M')) : Prop :=
  ∃ φ : (ModuleOfDifferentials A B) ⊗[B] M →+
      (ModuleOfDifferentials A' B') ⊗[B'] M',
    (∀ x,
      F.map 1 (principalPartsSequenceLeft (R := A) (S := B) (M := M) x) =
        principalPartsSequenceLeft (R := A') (S := B') (M := M') (φ x)) ∧
    (∀ x,
      principalPartsProjection (R := A') (S := B') (M := M') 1
          (F.map 1 x) =
        F.f (principalPartsProjection (R := A) (S := B) (M := M) 1 x))

theorem principalParts_functoriality_sequence_compatible
    (F : PrincipalPartsFunctoriality (A := A) (A' := A') (B := B) (B' := B')
      (M := M) (M' := M')) :
    principalPartsFunctorialitySequenceCompatible F := by
  sorry

end PrincipalPartsFunctoriality

section PrincipalPartsFunctorialityComposition

variable {A A' A'' B B' B'' M M' M'' : Type*}
  [CommRing A] [CommRing A'] [CommRing A'']
  [CommRing B] [CommRing B'] [CommRing B'']
  [Algebra A B] [Algebra A A'] [Algebra B B'] [Algebra A' B']
  [Algebra A' A''] [Algebra B' B''] [Algebra A'' B'']
  [Algebra A A''] [Algebra B B'']
  [AddCommGroup M] [Module B M] [Module A M] [IsScalarTower A B M]
  [AddCommGroup M'] [Module B' M'] [Module A' M'] [IsScalarTower A' B' M']
  [AddCommGroup M''] [Module B'' M''] [Module A'' M'']
  [IsScalarTower A'' B'' M'']

/-- Composition of two compatible principal-parts systems, including the
source-level map and the maps in every order. -/
structure PrincipalPartsFunctorialityComposition
    (F : PrincipalPartsFunctoriality
      (A := A) (A' := A') (B := B) (B' := B') (M := M) (M' := M'))
    (G : PrincipalPartsFunctoriality
      (A := A') (A' := A'') (B := B') (B' := B'') (M := M') (M' := M'')) where
  composed : PrincipalPartsFunctoriality
    (A := A) (A' := A'') (B := B) (B' := B'') (M := M) (M' := M'')
  f_eq : composed.f =
    (G.f.comp F.f)
  map_eq : ∀ k x, composed.map k x = G.map k (F.map k x)

theorem principalParts_functoriality_composition_exists
    (F : PrincipalPartsFunctoriality
      (A := A) (A' := A') (B := B) (B' := B') (M := M) (M' := M'))
    (G : PrincipalPartsFunctoriality
      (A := A') (A' := A'') (B := B') (B' := B'') (M := M') (M' := M'')) :
    Nonempty (PrincipalPartsFunctorialityComposition
      (A := A) (A' := A') (A'' := A'') (B := B) (B' := B') (B'' := B'')
      (M := M) (M' := M') (M'' := M'') F G) := by
  sorry

theorem principalParts_functoriality_composition_sequence_compatible
    (C : PrincipalPartsFunctorialityComposition
      (A := A) (A' := A') (A'' := A'') (B := B) (B' := B') (B'' := B'')
      (M := M) (M' := M') (M'' := M'') F G) :
    principalPartsFunctorialitySequenceCompatible C.composed := by
  sorry

end PrincipalPartsFunctorialityComposition

section PrincipalPartsBaseChange

variable {A A' B M : Type*}
  [CommRing A] [CommRing A'] [CommRing B]
  [Algebra A A'] [Algebra A B]
  [AddCommGroup M] [Module B M] [Module A M] [IsScalarTower A B M]

/-- The base-change statement for principal parts, with the tensor-product
convention used by Mathlib (`B ⊗[A] A'`).  The required target module
structures are explicit parameters because Mathlib deliberately does not
install all tensor-product algebra actions globally.
-/
structure PrincipalPartsBaseChangeData (k : ℕ) where
  B' : Type u'
  M' : Type u'
  [commRing_B' : CommRing B']
  [algebra_A'_B' : Algebra A' B']
  [addCommGroup_M' : AddCommGroup M']
  [module_B'_M' : Module B' M']
  [module_A'_M' : Module A' M']
  [module_A_M' : Module A M']
  [tower_A'_B'_M' : IsScalarTower A' B' M']
  [module_B'_left : Module B' (PrincipalParts (R := A) (S := B) (M := M) k ⊗[A] A')]
  identify_B' : B' ≃+* (B ⊗[A] A')
  identify_M' : M' ≃ₗ[A] (M ⊗[A] A')
  equivalence :
    PrincipalParts (R := A) (S := B) (M := M) k ⊗[A] A' ≃ₗ[B']
      PrincipalParts (R := A') (S := B') (M := M') k

theorem principalParts_base_change (k : ℕ) :
    Nonempty (PrincipalPartsBaseChangeData (A := A) (A' := A') (B := B) (M := M) k) := by
  sorry

end PrincipalPartsBaseChange

/-! ## The diagonal presentation -/

section PrincipalPartsDiagonal

variable {R S M : Type*} [CommRing R] [CommRing S] [Algebra R S]
  [AddCommGroup M] [Module S M] [Module R M]
  [IsScalarTower R S M]

def diagonalMultiplication : S ⊗[R] S →ₐ[R] S :=
  Algebra.TensorProduct.lmul' R

def diagonalIdeal : Ideal (S ⊗[R] S) :=
  RingHom.ker (diagonalMultiplication (R := R) (S := S)).toRingHom

def diagonalGenerator (g : S) : S ⊗[R] S :=
  g ⊗ₜ[R] (1 : S) - (1 : S) ⊗ₜ[R] g

theorem diagonalIdeal_eq_span_generators :
    diagonalIdeal (R := R) (S := S) =
      Ideal.span (Set.range (diagonalGenerator (R := R) (S := S))) := by
  sorry

def diagonalHigherRelation (k : ℕ) (g : Fin (k + 1) → S) (m : M) : S ⊗[R] M := by
  classical
  exact (Finset.univ : Finset (Finset (Fin (k + 1)))).sum (fun t =>
    ((-1 : S) ^ t.card) •
      (((Finset.univ \ t).prod g) ⊗ₜ[R] ((t.prod g) • m)))

def diagonalPowerSubmodule (k : ℕ) : Submodule S (S ⊗[R] M) :=
  Submodule.span S (Set.range (fun p : (Fin (k + 1) → S) × M =>
    diagonalHigherRelation (R := R) (S := S) k p.1 p.2))

abbrev DiagonalPrincipalParts (k : ℕ) : Type _ :=
  (S ⊗[R] M) ⧸ diagonalPowerSubmodule (R := R) (S := S) k

noncomputable def diagonalUniversalLinearMap (k : ℕ) :
    M →ₗ[R] DiagonalPrincipalParts (R := R) (S := S) (M := M) k :=
  (Submodule.mkQ (diagonalPowerSubmodule (R := R) (S := S) k)).restrictScalars R |>.comp
    (TensorProduct.AlgebraTensorModule.mk R S S M 1)

theorem principalParts_diagonal_equiv_exists (k : ℕ) :
    ∃ e : PrincipalParts (R := R) (S := S) (M := M) k ≃ₗ[S]
        DiagonalPrincipalParts (R := R) (S := S) (M := M) k,
      ∀ m,
        e (principalPartsGenerator (R := R) (S := S) k m) =
          diagonalUniversalLinearMap (R := R) (S := S) (M := M) k m := by
  sorry

noncomputable def principalPartsDiagonalEquiv (k : ℕ) :
    PrincipalParts (R := R) (S := S) (M := M) k ≃ₗ[S]
      DiagonalPrincipalParts (R := R) (S := S) (M := M) k :=
  Classical.choose (principalParts_diagonal_equiv_exists (R := R) (S := S) (M := M) k)

theorem principalPartsDiagonalEquiv_on_generator (k : ℕ) (m : M) :
    principalPartsDiagonalEquiv (R := R) (S := S) (M := M) k
        (principalPartsGenerator (R := R) (S := S) (M := M) k m) =
      diagonalUniversalLinearMap (R := R) (S := S) (M := M) k m :=
  (Classical.choose_spec
    (principalParts_diagonal_equiv_exists (R := R) (S := S) (M := M) k)) m

end PrincipalPartsDiagonal

/-! ## Differential forms, generators, localization, and tensor products -/

section DifferentialFormsAndGenerators

variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]

theorem deRham_differential_is_differentialOperator (i : ℕ) :
    @IsDifferentialOperator A B (deRhamTerm A B i) (deRhamTerm A B (i + 1))
      inferInstance inferInstance inferInstance inferInstance inferInstance
      inferInstance inferInstance
      (deRhamTerm.moduleA (A := A) (B := B) i)
      (deRhamTerm.moduleA (A := A) (B := B) (i + 1))
      (deRhamTerm.isScalarTower (A := A) (B := B) i)
      (deRhamTerm.isScalarTower (A := A) (B := B) (i + 1))
      1 (deRhamDifferential (A := A) (B := B) i) := by
  sorry

theorem differentialOperator_check_on_algebra_generators
    {I : Type*} (g : I → B)
    (hg : Algebra.adjoin A (Set.range g) = ⊤)
    {M N : Type*} [AddCommGroup M] [AddCommGroup N]
    [Module B M] [Module B N] [Module A M] [Module A N]
    [IsScalarTower A B M] [IsScalarTower A B N]
    (k : ℕ) (hk : 1 ≤ k) (D : M →ₗ[A] N)
    (hD : ∀ i, IsDifferentialOperator (R := A) (S := B) (k - 1)
      (differentialOperatorCommutator (R := A) (S := B) D (g i))) :
    IsDifferentialOperator (R := A) (S := B) k D := by
  sorry

end DifferentialFormsAndGenerators

section DifferentialOperatorLocalization

variable {A B M N : Type*} [CommRing A] [CommRing B] [Algebra A B]
  [AddCommGroup M] [AddCommGroup N]
  [Module B M] [Module B N] [Module A M] [Module A N]
  [IsScalarTower A B M] [IsScalarTower A B N]

theorem differentialOperator_localization_unique (T : Submonoid B) (k : ℕ)
    (D : differentialOperatorSubmodule (R := A) (S := B) (M := M) (N := N) k) :
    ∃! E : differentialOperatorSubmodule (R := A) (S := B) k
        (M := LocalizedModule T M) (N := LocalizedModule T N),
      ∀ m,
        E.1 (LocalizedModule.mkLinearMap T M m) =
          LocalizedModule.mkLinearMap T N (D.1 m) := by
  sorry

noncomputable def localizedDifferentialOperator (T : Submonoid B) (k : ℕ)
    (D : differentialOperatorSubmodule (R := A) (S := B) (M := M) (N := N) k) :
    differentialOperatorSubmodule (R := A) (S := B) k
      (M := LocalizedModule T M) (N := LocalizedModule T N) :=
  Classical.choose (differentialOperator_localization_unique (A := A) (B := B)
    (M := M) (N := N) T k D)

theorem localizedDifferentialOperator_extends (T : Submonoid B) (k : ℕ)
    (D : differentialOperatorSubmodule (R := A) (S := B) (M := M) (N := N) k) (m : M) :
    (localizedDifferentialOperator (A := A) (B := B) (M := M) (N := N) T k D).1
        (LocalizedModule.mkLinearMap T M m) =
      LocalizedModule.mkLinearMap T N (D.1 m) :=
  (Classical.choose_spec (differentialOperator_localization_unique (A := A) (B := B)
    (M := M) (N := N) T k D)).1 m

end DifferentialOperatorLocalization

section DifferentialOperatorTensorProduct

variable {R A B M M' N : Type*}
  [CommRing R] [CommRing A] [CommRing B]
  [Algebra R A] [Algebra R B]
  [AddCommGroup M] [AddCommGroup M'] [AddCommGroup N]
  [Module A M] [Module A M'] [Module R M] [Module R M']
  [IsScalarTower R A M] [IsScalarTower R A M']
  [Module B N] [Module R N] [IsScalarTower R B N]

def tensorProductDifferentialOperator (D : M →ₗ[R] M') :
    M ⊗[R] N →ₗ[R] M' ⊗[R] N :=
  TensorProduct.map D (LinearMap.id : N →ₗ[R] N)

theorem differentialOperator_tensor_product_base_change
    (k : ℕ) (D : differentialOperatorSubmodule (R := R) (S := A) k
      (M := M) (N := M'))
    [Module (A ⊗[R] B) (M ⊗[R] N)]
    [Module (A ⊗[R] B) (M' ⊗[R] N)]
    [IsScalarTower R (A ⊗[R] B) (M ⊗[R] N)]
    [IsScalarTower R (A ⊗[R] B) (M' ⊗[R] N)] :
    IsDifferentialOperator (R := R) (S := A ⊗[R] B) k
      (tensorProductDifferentialOperator (R := R) (M := M) (M' := M')
        (N := N) D.1) := by
  sorry

end DifferentialOperatorTensorProduct

end
end Formalization.Books.Algebra.Unit133
