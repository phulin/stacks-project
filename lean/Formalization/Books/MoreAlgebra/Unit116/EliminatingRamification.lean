import Formalization.Books.MoreAlgebra.Unit115
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.FieldTheory.KummerExtension
import Mathlib.FieldTheory.PurelyInseparable.Basic
import Mathlib.FieldTheory.Separable
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.AdicCompletion.Completeness
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.RingTheory.TensorProduct.Basic

/-!
This file formalizes the declarations in More on Algebra, Chapter 116,
“Eliminating ramification”.  The base-change constructions and the DVR
predicates are those introduced in Chapters 112 and 115; this file adds the
solution predicates and the interfaces for Epp's elimination argument.
-/

namespace Formalization.Books.MoreAlgebra.Unit116

open Formalization.Books.MoreAlgebra.Unit112
open Formalization.Books.MoreAlgebra.Unit115
open Formalization.Books.Algebra.Unit162
open scoped TensorProduct

noncomputable section

universe u v w z uA uB uC uK uL uM uK₁

/-! ## Common DVR diagrams and the solution predicates -/

/-- An extension of DVRs together with its chosen fraction fields. -/
structure DVRFieldDiagram
    (A B K L : Type*) [CommRing A] [CommRing B] [Field K] [Field L]
    [Algebra A K] [Algebra A L] [Algebra B L] [Algebra K L]
    [IsDomain A] [IsDomain B]
    [IsDiscreteValuationRing A] [IsDiscreteValuationRing B] where
  map : DVRMap A B
  fraction : FractionFieldExtension (K := K) (L := L) map

/-- Three compatible extensions of DVRs `A ⊂ B ⊂ C` and their fraction
fields. -/
structure DVRTower
    (A B C K L M : Type*) [CommRing A] [CommRing B] [CommRing C]
    [Field K] [Field L] [Field M]
    [Algebra A K] [Algebra A L] [Algebra A M]
    [Algebra B L] [Algebra B M] [Algebra C M]
    [Algebra K L] [Algebra K M] [Algebra L M]
    [IsDomain A] [IsDomain B] [IsDomain C]
    [IsDiscreteValuationRing A] [IsDiscreteValuationRing B]
    [IsDiscreteValuationRing C] where
  ab : DVRFieldDiagram A B K L
  bc : DVRFieldDiagram B C L M
  ac : DVRFieldDiagram A C K M
  map_comp : ac.map.hom = bc.map.hom.comp ab.map.hom

/-- A local map in a base-change diagram is weakly unramified. -/
def localDVRMapWeaklyUnramified (D : LocalDVRMap) : Prop :=
  letI := D.sourceCommRing
  letI := D.targetCommRing
  letI := D.sourceDomain
  letI := D.targetDomain
  letI := D.sourceDVR
  letI := D.targetDVR
  WeaklyUnramified D.map

/-- The two alternatives used uniformly in the source's “(weak) solution”. -/
inductive SolutionMode
  | weak
  | formallySmooth

/-- A base-change witness carrying the local extensions occurring in
Remark `remark-construction`.  The field on the reduced tensor product is
the source's assertion that `L₁` is a field. -/
structure BaseChangeSolutionWitness
    {A : Type uA} {B : Type uB} {K : Type uK} {L : Type uL} {K₁ : Type uK₁}
    [CommRing A] [CommRing B] [Field K] [Field L]
    [Field K₁] [Algebra A K] [Algebra A L] [Algebra B L] [Algebra K L]
    [Algebra K K₁] [Algebra A K₁] [FiniteDimensional K K₁]
    [IsDomain A] [IsDomain B]
    [IsDiscreteValuationRing A] [IsDiscreteValuationRing B]
    (E : DVRMap A B) (F : FractionFieldExtension (K := K) (L := L) E) where
  construction :
    BaseChangeConstruction.{uA, uB, uK, uL, uK₁, uB} (K₁ := K₁) E F
  places : BaseChangePlaceData E
  tensorProductField : Field (baseChangeL₁ K L K₁)

def BaseChangeSolutionWitness.satisfies
    {A B K L K₁ : Type*} [CommRing A] [CommRing B] [Field K] [Field L]
    [Field K₁] [Algebra A K] [Algebra A L] [Algebra B L] [Algebra K L]
    [Algebra K K₁] [Algebra A K₁] [FiniteDimensional K K₁]
    [IsDomain A] [IsDomain B]
    [IsDiscreteValuationRing A] [IsDiscreteValuationRing B]
    {E : DVRMap A B} {F : FractionFieldExtension (K := K) (L := L) E}
    (W : BaseChangeSolutionWitness (K₁ := K₁) E F) (mode : SolutionMode) : Prop :=
  match mode with
  | .weak => ∀ i j, localDVRMapWeaklyUnramified (W.places.localExtension i j)
  | .formallySmooth => ∀ i j, (W.places.localExtension i j).formallySmooth

/-- A finite field extension is a weak solution for an extension of DVRs. -/
def WeakSolutionFor
    {A B K L : Type*} [CommRing A] [CommRing B] [Field K] [Field L]
    [Algebra A K] [Algebra A L] [Algebra B L] [Algebra K L]
    [IsDomain A] [IsDomain B]
    [IsDiscreteValuationRing A] [IsDiscreteValuationRing B]
    (D : DVRFieldDiagram A B K L) (K₁ : Type*) [Field K₁]
    [Algebra K K₁] [Algebra A K₁] [FiniteDimensional K K₁] : Prop :=
  ∃ W : BaseChangeSolutionWitness (K₁ := K₁) D.map D.fraction,
    W.satisfies .weak

/-- A finite field extension is a solution in the formally smooth sense. -/
def SolutionFor
    {A B K L : Type*} [CommRing A] [CommRing B] [Field K] [Field L]
    [Algebra A K] [Algebra A L] [Algebra B L] [Algebra K L]
    [IsDomain A] [IsDomain B]
    [IsDiscreteValuationRing A] [IsDiscreteValuationRing B]
    (D : DVRFieldDiagram A B K L) (K₁ : Type*) [Field K₁]
    [Algebra K K₁] [Algebra A K₁] [FiniteDimensional K K₁] : Prop :=
  ∃ W : BaseChangeSolutionWitness (K₁ := K₁) D.map D.fraction,
    W.satisfies .formallySmooth

/-- A solution whose field extension is separable. -/
def SeparableSolutionFor
    {A B K L : Type*} [CommRing A] [CommRing B] [Field K] [Field L]
    [Algebra A K] [Algebra A L] [Algebra B L] [Algebra K L]
    [IsDomain A] [IsDomain B]
    [IsDiscreteValuationRing A] [IsDiscreteValuationRing B]
    (D : DVRFieldDiagram A B K L) (K₁ : Type*) [Field K₁]
    [Algebra K K₁] [Algebra A K₁] [FiniteDimensional K K₁]
    [Algebra.IsSeparable K K₁] : Prop :=
  SolutionFor D K₁ ∧ Algebra.IsSeparable K K₁

/-! ## The opening example and the first permanence lemmas -/

/-- The source's characteristic-
`p` example, abstracted to the chosen DVR diagram and the root extension
predicate for `B = A[x^(1/p)]`. -/
structure InseparableNecessaryExample
    (A B K : Type u) [CommRing A] [CommRing B] [Field K]
    [Algebra A K] [IsDomain A] [IsDomain B] [IsDiscreteValuationRing A]
    [IsDiscreteValuationRing B] where
  p : ℕ
  p_prime : Nat.Prime p
  residueCharacteristic : ringChar (DVRResidueField A) = p
  basePerfect : Prop
  powerSeriesBase : Prop
  rootExtension : Prop
  diagram : ∀ (L : Type u) [Field L] [Algebra A L] [Algebra B L]
    [Algebra K L] [Algebra A K] [IsDomain B],
    DVRFieldDiagram A B K L
  finiteInseparableExtensionsAreSolutions :
    ∀ (L : Type u) [Field L] [Algebra A L] [Algebra B L] [Algebra K L]
      (D : DVRFieldDiagram A B K L) (K₁ : Type u) [Field K₁]
      [Algebra K K₁] [Algebra A K₁] [FiniteDimensional K K₁],
      ¬ Algebra.IsSeparable K K₁ → SolutionFor D K₁

theorem inseparable_necessary_example
    {A B K : Type u} [CommRing A] [CommRing B] [Field K]
    [Algebra A K] [IsDomain A] [IsDomain B] [IsDiscreteValuationRing A]
    [IsDiscreteValuationRing B]
    (X : InseparableNecessaryExample A B K)
    {L : Type u} [Field L] [Algebra A L] [Algebra B L] [Algebra K L]
    [IsDomain B] (D : DVRFieldDiagram A B K L)
    {K₁ : Type u} [Field K₁] [Algebra K K₁] [Algebra A K₁]
    [FiniteDimensional K K₁]
    (h : WeakSolutionFor D K₁) : ¬ Algebra.IsSeparable K K₁ := by
  sorry

theorem inseparable_example_finite_inseparable_solution
    {A B K : Type u} [CommRing A] [CommRing B] [Field K]
    [Algebra A K] [IsDomain A] [IsDomain B] [IsDiscreteValuationRing A]
    [IsDiscreteValuationRing B]
    (X : InseparableNecessaryExample A B K)
    {L : Type u} [Field L] [Algebra A L] [Algebra B L] [Algebra K L]
    (D : DVRFieldDiagram A B K L)
    {K₁ : Type u} [Field K₁] [Algebra K K₁] [Algebra A K₁]
    [FiniteDimensional K K₁] (h : ¬ Algebra.IsSeparable K K₁) :
    SolutionFor D K₁ := by
  exact X.finiteInseparableExtensionsAreSolutions L D K₁ h

theorem weaklyUnramified_goes_up_along_totallyRamified
    {A B K L : Type*} [CommRing A] [CommRing B] [Field K] [Field L]
    [Algebra A K] [Algebra A L] [Algebra B L] [Algebra K L]
    [IsDomain A] [IsDomain B]
    [IsDiscreteValuationRing A] [IsDiscreteValuationRing B]
    (D : DVRFieldDiagram A B K L) (hD : WeaklyUnramified D.map)
    {K₁ : Type*} [Field K₁] [Algebra K K₁] [Algebra A K₁]
    [FiniteDimensional K K₁] [Algebra.IsSeparable K K₁]
    (X : FiniteSeparableExtensionData A K K₁)
    (hTot : IsTotallyRamified X) :
    ∃ W : BaseChangeSolutionWitness (K₁ := K₁) D.map D.fraction,
      W.satisfies .weak := by
  sorry

/-! The finite product of factors in Lemma `solutions-go-down`. -/

structure WeakSolutionProduct
    {B : Type uB} {C : Type uC} {L : Type uL} {M : Type uM}
    [CommRing B] [CommRing C] [Field L] [Field M]
    [Algebra B L] [Algebra B M] [Algebra C M] [Algebra L M]
    [IsDomain B] [IsDomain C]
    [IsDiscreteValuationRing B] [IsDiscreteValuationRing C]
    (D : DVRFieldDiagram B C L M) where
  numberOfFactors : ℕ
  numberOfFactors_pos : 0 < numberOfFactors
  factor : Fin numberOfFactors → Type uL
  factorField : ∀ i, Field (factor i)
  factorAlgebra : ∀ i, Algebra L (factor i)
  factorBaseAlgebra : ∀ i, Algebra B (factor i)
  factorFinite : ∀ i, FiniteDimensional L (factor i)
  factorSolution : ∀ i,
    letI := factorField i
    letI := factorAlgebra i
    letI := factorBaseAlgebra i
    letI := factorFinite i
    WeakSolutionFor D (factor i)
  reducedTensorProductPresentation : Prop

def SolutionProductFor
    {B C L M : Type*} [CommRing B] [CommRing C] [Field L] [Field M]
    [Algebra B L] [Algebra B M] [Algebra C M] [Algebra L M]
    [IsDomain B] [IsDomain C]
    [IsDiscreteValuationRing B] [IsDiscreteValuationRing C]
    (D : DVRFieldDiagram B C L M) (mode : SolutionMode) : Prop :=
  ∃ P : WeakSolutionProduct D,
    ∀ i,
      letI := P.factorField i
      letI := P.factorAlgebra i
      letI := P.factorBaseAlgebra i
      letI := P.factorFinite i
      ∃ W : BaseChangeSolutionWitness (K₁ := P.factor i) D.map D.fraction,
        W.satisfies mode

theorem solutions_go_down
    {A B C K L M : Type*} [CommRing A] [CommRing B] [CommRing C]
    [Field K] [Field L] [Field M]
    [Algebra A K] [Algebra A L] [Algebra A M]
    [Algebra B L] [Algebra B M] [Algebra C M]
    [Algebra K L] [Algebra K M] [Algebra L M]
    [IsDomain A] [IsDomain B] [IsDomain C]
    [IsDiscreteValuationRing A] [IsDiscreteValuationRing B]
    [IsDiscreteValuationRing C]
    (T : DVRTower A B C K L M) (mode : SolutionMode)
    {K₁ : Type*} [Field K₁] [Algebra K K₁] [Algebra A K₁]
    [FiniteDimensional K K₁]
    (h₁ : ∃ W : BaseChangeSolutionWitness (K₁ := K₁) T.ab.map T.ab.fraction,
      W.satisfies mode)
    (h₂ : SolutionProductFor T.bc mode) :
    ∃ W : BaseChangeSolutionWitness (K₁ := K₁) T.ac.map T.ac.fraction,
      W.satisfies mode := by
  sorry

/-! ## Strict henselization and Galois symmetry -/

def SeparableAlgebraicClosureOf (k k' : Type*) [Field k] [Field k']
    [Algebra k k'] : Prop :=
  Algebra.IsSeparable k k' ∧ Algebra.IsAlgebraic k k' ∧ IsAlgClosed k'

structure StrictHenselizationData
    {A : Type uA} {B : Type uB} [CommRing A] [CommRing B]
    [IsDomain A] [IsDomain B]
    [IsDiscreteValuationRing A] [IsDiscreteValuationRing B] where
  K' : Type uA
  L' : Type uB
  A' : Type uA
  B' : Type uB
  fieldK' : Field K'
  fieldL' : Field L'
  commRingA' : CommRing A'
  commRingB' : CommRing B'
  algebraAK' : Algebra A' K'
  algebraA'L' : Algebra A' L'
  algebraB'L' : Algebra B' L'
  algebraK'L' : Algebra K' L'
  domainA' : IsDomain A'
  domainB' : IsDomain B'
  dvrA' : IsDiscreteValuationRing A'
  dvrB' : IsDiscreteValuationRing B'
  diagram : letI := fieldK'; letI := fieldL'; letI := commRingA';
    letI := commRingB'; letI := algebraAK'; letI := algebraA'L';
    letI := algebraB'L'; letI := algebraK'L'; letI := domainA';
    letI := domainB'; letI := dvrA'; letI := dvrB';
    DVRFieldDiagram A' B' K' L'
  fractionFieldsSeparableAlgebraic : Prop
  residueA : Type uA
  residueB : Type uB
  residueAField : Field residueA
  residueBField : Field residueB
  residueAAlgebra : Algebra (DVRResidueField A) residueA
  residueBAlgebra : Algebra (DVRResidueField B) residueB
  residueAClosure : SeparableAlgebraicClosureOf (DVRResidueField A) residueA
  residueBClosure : SeparableAlgebraicClosureOf (DVRResidueField B) residueB
  solutionTransfer : Prop

theorem solution_after_strict_henselization
    {A B : Type*} [CommRing A] [CommRing B]
    [IsDomain A] [IsDomain B]
    [IsDiscreteValuationRing A] [IsDiscreteValuationRing B] :
    ∃ X : StrictHenselizationData (A := A) (B := B),
      X.solutionTransfer := by
  sorry

theorem galois_relative_action
    {A B K L K₁ : Type*} [CommRing A] [CommRing B] [Field K] [Field L]
    [Field K₁] [Algebra A K] [Algebra A L] [Algebra B L] [Algebra K L]
    [Algebra K K₁] [Algebra A K₁] [FiniteDimensional K K₁]
    [IsDomain A] [IsDomain B]
    [IsDiscreteValuationRing A] [IsDiscreteValuationRing B]
    (D : DVRFieldDiagram A B K L) [Normal K K₁]
    (W : BaseChangeSolutionWitness (K₁ := K₁) D.map D.fraction) :
    ∃ action : (K₁ ≃ₐ[K] K₁) →
        Ideal W.construction.B₁ → Ideal W.construction.B₁,
        (∀ J, action 1 J = J) ∧
          (∀ σ τ J, action (σ * τ) J = action σ (action τ J)) ∧
          ∀ m₁ m₂ : Ideal W.construction.B₁,
            m₁.IsMaximal → m₂.IsMaximal →
              ∃ σ : K₁ ≃ₐ[K] K₁, action σ m₁ = m₂ := by
  sorry

/-! ## Purely inseparable and Artin--Schreier steps -/

/-- The two equations for the uniformizer in Lemma
`make-degree-q-extension`. -/
structure DegreeQExtensionSpecification
    {A B K L : Type*} [CommRing A] [CommRing B] [Field K] [Field L]
    [Algebra A K] [Algebra A L] [Algebra B L] [Algebra K L]
    [IsDomain A] [IsDomain B]
    [IsDiscreteValuationRing A] [IsDiscreteValuationRing B]
    (D : DVRFieldDiagram A B K L) (π : A) (p q n : ℕ) where
  p_prime : Nat.Prime p
  q_is_p_power : ∃ r : ℕ, q = p ^ r
  n_gt_one : 1 < n
  finiteDegree : Module.finrank K L = q
  separable : Algebra.IsSeparable K L
  totallyRamified : ∃ X : FiniteSeparableExtensionData A K L,
    IsTotallyRamified X
  integralClosure : Nonempty (B ≃+* integralClosureIn A L)
  ramificationIndex : ramificationIndex D.map = q
  uniformizer : B
  uniformizer_is_irreducible : Irreducible uniformizer
  first_equation : ∃ b : B,
    uniformizer ^ q = D.map.hom π + (D.map.hom π) ^ n * b
  second_equation : ∃ b' : B,
    uniformizer ^ q = D.map.hom π + uniformizer ^ (n * q) * b'

theorem make_degree_q_extension
    {A K : Type*} [CommRing A] [Field K] [Algebra A K]
    [IsDomain A] [IsDiscreteValuationRing A]
    (π : A) (hπ : Irreducible π) {p q n : ℕ}
    (hp : Nat.Prime p) (hq : ∃ r : ℕ, q = p ^ r) (hn : 1 < n)
    (hres : ringChar (DVRResidueField A) = p) :
    ∃ (B L : Type*) (hB : CommRing B) (hL : Field L)
      (hBL : Algebra B L) (hAL : Algebra A L) (hKL : Algebra K L)
      (hdomB : IsDomain B) (hdvrB : IsDiscreteValuationRing B),
      letI := hB
      letI := hL
      letI := hBL
      letI := hAL
      letI := hKL
      letI := hdomB
      letI := hdvrB
      ∃ D : DVRFieldDiagram A B K L,
        Nonempty (DegreeQExtensionSpecification D π p q n) := by
  sorry

def ResidueClassNotPthPower
    {A : Type*} [CommRing A] [IsDomain A]
    [IsDiscreteValuationRing A] (p : ℕ) (a : A) : Prop :=
  ¬ ∃ x : DVRResidueField A,
    x ^ p = algebraMap A (DVRResidueField A) a

def ResidueFrobeniusCoreContained
    {A B : Type*} [CommRing A] [CommRing B]
    [IsDomain A] [IsDomain B]
    [IsDiscreteValuationRing A] [IsDiscreteValuationRing B]
    (E : DVRMap A B) (p : ℕ) : Prop :=
  letI := residueFieldAlgebra E
  ∀ x : DVRResidueField B,
    (∀ n : ℕ, ∃ y : DVRResidueField B, y ^ (p ^ n) = x) →
      ∃ y : DVRResidueField A, algebraMap _ _ y = x

structure PurelyInseparableRootData
    {A K : Type*} [CommRing A] [Field K] [Algebra A K]
    [IsDomain A] [IsDiscreteValuationRing A]
    (a : A) (p : ℕ) where
  L : Type*
  B : Type*
  fieldL : Field L
  commRingB : CommRing B
  algebraKL : Algebra K L
  algebraAL : Algebra A L
  algebraBL : Algebra B L
  algebraAB : Algebra A B
  domainB : IsDomain B
  dvrB : IsDiscreteValuationRing B
  map : A →+* B
  map_injective : Function.Injective map
  map_local : IsLocalHom map
  map_eq_algebra : letI := algebraAB; map = algebraMap A B
  root : L
  root_equation : letI := algebraAL; root ^ p = algebraMap A L a
  generates : letI := algebraKL; Algebra.adjoin K {root} = ⊤
  degree : Module.finrank K L = p
  integralClosure : letI := algebraAL; Nonempty (B ≃+* integralClosureIn A L)
  map_is_weaklyUnramified :
    letI := fieldL
    letI := commRingB
    letI := algebraKL
    letI := algebraAL
    letI := algebraBL
    letI := algebraAB
    letI := domainB
    letI := dvrB
    WeaklyUnramified (DVRMap.mk map map_injective map_local)

theorem pre_purely_inseparable_case
    {A K : Type*} [CommRing A] [Field K] [Algebra A K]
    [IsDomain A] [IsDiscreteValuationRing A]
    {a : A} {p : ℕ} (hp : Nat.Prime p)
    (hchar : ringChar (DVRResidueField A) = p)
    (ha : ResidueClassNotPthPower p a) :
    Nonempty (PurelyInseparableRootData (K := K) a p) := by
  sorry

def IsAdjoiningUniformizerPthRoot
    {A B C : Type*} [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra B C] [Algebra A C] (π : A) (p : ℕ) : Prop :=
  ∃ θ : C, θ ^ p = algebraMap A C π ∧ Algebra.adjoin B {θ} = ⊤

theorem purely_inseparable_case
    {A B C K L M : Type*} [CommRing A] [CommRing B] [CommRing C]
    [Field K] [Field L] [Field M]
    [Algebra A K] [Algebra A L] [Algebra A M]
    [Algebra B L] [Algebra B M] [Algebra C M]
    [Algebra K L] [Algebra K M] [Algebra L M]
    [Algebra A B] [Algebra B C] [Algebra A C]
    [IsDomain A] [IsDomain B] [IsDomain C]
    [IsDiscreteValuationRing A] [IsDiscreteValuationRing B]
    [IsDiscreteValuationRing C]
    (T : DVRTower A B C K L M) (π : A) (p : ℕ) (hp : Nat.Prime p)
    (hNagata : IsNagataRing B) (hWeak : WeaklyUnramified T.ab.map)
    [IsPurelyInseparable L M]
    (hdegree : Module.finrank L M = p) :
    WeaklyUnramified T.ac.map ∨
      IsAdjoiningUniformizerPthRoot (A := A) (B := B) (C := C) π p ∨
      ∃ (K₁ : Type*) (hK₁ : Field K₁) (hKK₁ : Algebra K K₁)
        (hAK₁ : Algebra A K₁) (hfin : FiniteDimensional K K₁)
        (hsep : Algebra.IsSeparable K K₁),
        letI := hK₁
        letI := hKK₁
        letI := hAK₁
        letI := hfin
        letI := hsep
        ∃ X : FiniteSeparableExtensionData A K K₁,
          Module.finrank K K₁ = p ∧ IsTotallyRamified X ∧
            WeakSolutionFor T.ac K₁ := by
  sorry

/-! ## Cohen sections and the equicharacteristic case -/

def NilpotentIdeal {A : Type*} [CommRing A] (I : Ideal A) : Prop :=
  ∃ n : ℕ, I ^ n = ⊥

def ResidueFieldExtensionIsSeparable
    {A A' : Type*} [CommRing A] [CommRing A'] [IsLocalRing A]
    [IsLocalRing A'] (f : A →+* A') (hf : IsLocalHom f) : Prop :=
  letI : IsLocalHom f := hf
  letI : Algebra (IsLocalRing.ResidueField A)
      (IsLocalRing.ResidueField A') :=
    (IsLocalRing.ResidueField.map f).toAlgebra
  Algebra.IsSeparable (IsLocalRing.ResidueField A)
    (IsLocalRing.ResidueField A')

theorem cohen
    {A A' : Type*} [CommRing A] [CommRing A'] [IsLocalRing A]
    [IsLocalRing A'] {p : ℕ} (hp : Nat.Prime p)
    [CharP A p] [CharP A' p]
    (hA : NilpotentIdeal (IsLocalRing.maximalIdeal A))
    (hA' : NilpotentIdeal (IsLocalRing.maximalIdeal A'))
    (f : A →+* A') (hf : IsLocalHom f)
    (hsep : ResidueFieldExtensionIsSeparable f hf) :
    ∃ σ₀ : IsLocalRing.ResidueField A →+* A,
      ∃ σ : IsLocalRing.ResidueField A' →+* A',
        (IsLocalRing.residue A).comp σ₀ = RingHom.id _ ∧
          (IsLocalRing.residue A').comp σ = RingHom.id _ ∧
          letI : IsLocalHom f := hf
          f.comp σ₀ = σ.comp (IsLocalRing.ResidueField.map f) := by
  sorry

def ArtinSchreierUnramifiedOfDegree
    {A K L : Type*} [CommRing A] [Field K] [Field L]
    [Algebra A K] [Algebra A L] [Algebra K L]
    [IsDomain A] [IsDiscreteValuationRing A] (p : ℕ) : Prop :=
  ∃ X : FiniteSeparableExtensionData A K L,
    Module.finrank K L = p ∧ UnramifiedWithRespectTo X

def ArtinSchreierTotallyRamifiedOfDegree
    {A K L : Type*} [CommRing A] [Field K] [Field L]
    [Algebra A K] [Algebra A L] [Algebra K L]
    [IsDomain A] [IsDiscreteValuationRing A] (p : ℕ) : Prop :=
  ∃ X : FiniteSeparableExtensionData A K L,
    Module.finrank K L = p ∧ IsTotallyRamified X

def ArtinSchreierWeakResidueCase
    {A K : Type*} {L : Type uL} [CommRing A] [Field K] [Field L]
    [Algebra A K] [Algebra A L] [Algebra K L]
    [IsDomain A] [IsDiscreteValuationRing A] (p : ℕ) : Prop :=
  ∃ (B : Type uL) (hB : CommRing B) (hBL : Algebra B L)
    (hdomB : IsDomain B) (hdvrB : IsDiscreteValuationRing B),
    letI := hB
    letI := hBL
    letI := hdomB
    letI := hdvrB
    ∃ D : DVRFieldDiagram A B K L,
      WeaklyUnramified D.map ∧
        letI := residueFieldAlgebra D.map
        Module.finrank (DVRResidueField A) (DVRResidueField B) = p ∧
          IsPurelyInseparable (DVRResidueField A) (DVRResidueField B)

def IsTrivialFieldExtension
    {K L : Type*} [Field K] [Field L] [Algebra K L] : Prop :=
  Nonempty (L ≃ₐ[K] K)

theorem pre_characteristic_p_case
    {A K L : Type*} [CommRing A] [Field K] [Field L]
    [Algebra A K] [Algebra A L] [Algebra K L]
    [IsDomain A] [IsDiscreteValuationRing A]
    [FiniteDimensional K L] [Algebra.IsSeparable K L] [IsGalois K L]
    {p : ℕ} (hp : Nat.Prime p) (ξ : K)
    (z : L) (hz : z ^ p - z = algebraMap K L ξ)
    (hgen : Algebra.adjoin K {z} = ⊤) (π : A) (hπ : Irreducible π) :
    (IsTrivialFieldExtension (K := K) (L := L) ∨
      ArtinSchreierUnramifiedOfDegree (A := A) (K := K) (L := L) p ∨
      ArtinSchreierTotallyRamifiedOfDegree (A := A) (K := K) (L := L) p ∨
      ArtinSchreierWeakResidueCase (A := A) (K := K) (L := L) p) ∧
    ((∃ a : A, algebraMap A K a = ξ) →
      IsTrivialFieldExtension (K := K) (L := L) ∨
        ArtinSchreierUnramifiedOfDegree (A := A) (K := K) (L := L) p) ∧
    (∀ n : ℕ, 0 < n → n % p ≠ 0 →
      ∀ a : A, IsUnit a →
        ξ = (algebraMap A K π)⁻¹ ^ n * algebraMap A K a →
          ArtinSchreierTotallyRamifiedOfDegree (A := A) (K := K) (L := L) p) ∧
    (∀ n : ℕ, 0 < n → p ∣ n →
      ∀ a : A, ResidueClassNotPthPower p a →
          ξ = (algebraMap A K π)⁻¹ ^ n * algebraMap A K a →
          ArtinSchreierWeakResidueCase (A := A) (K := K) (L := L) p) := by
  sorry

def FrobeniusCoreElement
    {k : Type*} [Field k] (p : ℕ) (x : k) : Prop :=
  ∀ n : ℕ, ∃ y : k, y ^ (p ^ n) = x

def FrobeniusCoreContainedIn
    {k K : Type*} [Field k] [Field K] [Algebra k K] (p : ℕ) : Prop :=
  ∀ x : K, FrobeniusCoreElement p x → ∃ y : k, algebraMap k K y = x

theorem characteristic_p_case
    {A B C K L M : Type*} [CommRing A] [CommRing B] [CommRing C]
    [Field K] [Field L] [Field M]
    [Algebra A K] [Algebra A L] [Algebra A M]
    [Algebra B L] [Algebra B M] [Algebra C M]
    [Algebra K L] [Algebra K M] [Algebra L M]
    [IsDomain A] [IsDomain B] [IsDomain C]
    [IsDiscreteValuationRing A] [IsDiscreteValuationRing B]
    [IsDiscreteValuationRing C]
    (T : DVRTower A B C K L M) {p : ℕ} [CharP K p]
    (hp : Nat.Prime p) (hWeak : WeaklyUnramified T.ab.map)
    [IsGalois L M] (hdegree : Module.finrank L M = p)
    (hCore : letI := residueFieldAlgebra T.ab.map
      FrobeniusCoreContainedIn (k := DVRResidueField A)
        (K := DVRResidueField B) p) :
    ∃ (K₁ : Type*) (hK₁ : Field K₁) (hKK₁ : Algebra K K₁)
      (hAK₁ : Algebra A K₁) (hfin : FiniteDimensional K K₁)
      (hsep : Algebra.IsSeparable K K₁) (hgal : IsGalois K K₁),
      letI := hK₁
      letI := hKK₁
      letI := hAK₁
      letI := hfin
      letI := hsep
      letI := hgal
      WeakSolutionFor T.ac K₁ := by
  sorry

/-! ## Mixed characteristic and the finite-level filtration -/

def IsPrimitivePthRoot
    {A : Type*} [CommRing A] (ζ : A) (p : ℕ) : Prop :=
  ζ ^ p = 1 ∧ ∀ m : ℕ, 0 < m → m < p → ζ ^ m ≠ 1

/-- The coefficient-and-identity interface for the polynomial in Lemma
`prepare`.  The displayed polynomial shape is represented by its canonical
`Polynomial` expression; the divisibility statement records `aᵢ ∈ (w)`. -/
structure PreparedPolynomialData
    (A : Type*) [CommRing A] (p : ℕ) (w : A) where
  P : Polynomial A
  coefficients : ∃ a : Fin (p - 1) → A,
    P = Polynomial.X ^ p - Polynomial.X +
      ∑ i : Fin (p - 1), Polynomial.C (a i) * Polynomial.X ^ (i.1 + 1)
  coefficients_in_w : ∀ i : Fin (p - 1),
    ∃ c : A, P.coeff (i.1 + 1) = w * c
  identity : ∀ z₁ z₂ : Polynomial A,
    Polynomial.eval₂ Polynomial.C
        (z₁ + z₂ + Polynomial.C w * z₁ * z₂) P =
      Polynomial.eval₂ Polynomial.C z₁ P +
        Polynomial.eval₂ Polynomial.C z₂ P +
        Polynomial.C (w ^ p) * Polynomial.eval₂ Polynomial.C z₁ P *
          Polynomial.eval₂ Polynomial.C z₂ P

theorem prepare
    {A : Type*} [CommRing A] {p : ℕ} (hp : Nat.Prime p)
    (ζ w : A) (hw : w = 1 - ζ) (hζ : IsPrimitivePthRoot ζ p) :
    Nonempty (PreparedPolynomialData A p w) := by
  sorry

def FiniteLevelCondition
    {A K : Type*} [CommRing A] [Field K] [Algebra A K]
    [IsDomain A] [IsDiscreteValuationRing A]
    (w : A) (p : ℕ) (ξ : K) : Prop :=
  algebraMap A K (w ^ p) * ξ ∈
    Ideal.map (algebraMap A K) (IsLocalRing.maximalIdeal A)

def IsDegreePFiniteLevel
    {A K L : Type*} [CommRing A] [Field K] [Field L]
    [Algebra A K] [Algebra A L] [Algebra K L]
    [IsDomain A] [IsDiscreteValuationRing A]
    (p : ℕ) (w : A) (P : Polynomial A) : Prop :=
  Module.finrank K L = p ∧
    ∃ z : L, ∃ ξ : K,
      Algebra.adjoin K {z} = ⊤ ∧
        Polynomial.eval₂ (algebraMap A L) z P = algebraMap K L ξ ∧
        FiniteLevelCondition w p ξ

def IntegralPowerCondition
    {A K : Type*} [CommRing A] [Field K] [Algebra A K]
    (π : A) (n : ℕ) (ξ : K) : Prop :=
  ∃ a : A, algebraMap A K a = algebraMap A K (π ^ n) * ξ

def FiniteLevel
    {A K L : Type*} [CommRing A] [Field K] [Field L]
    [Algebra A K] [Algebra A L] [Algebra K L]
    [IsDomain A] [IsDiscreteValuationRing A]
    (e₁ p : ℕ) (π w : A) (P : Polynomial A) : ℚ := by
  classical
  let S : Set ℚ := {q : ℚ |
    ∃ z : L, ∃ ξ : K, ∃ n : ℕ,
      Algebra.adjoin K {z} = ⊤ ∧
        Polynomial.eval₂ (algebraMap A L) z P = algebraMap K L ξ ∧
        IntegralPowerCondition π n ξ ∧ q = (n : ℚ) / (e₁ : ℚ)}
  exact if h : ∃ q : ℚ, IsLeast S q then Classical.choose h else 0

def NicePolynomialCase
    {A K : Type*} {L : Type uL} [CommRing A] [Field K] [Field L]
    [Algebra A K] [Algebra A L] [Algebra K L]
    [IsDomain A] [IsDiscreteValuationRing A] (p : ℕ)
    (P : Polynomial A) : Prop :=
  IsTrivialFieldExtension (K := K) (L := L) ∨
    ArtinSchreierUnramifiedOfDegree (A := A) (K := K) (L := L) p ∨
    ArtinSchreierTotallyRamifiedOfDegree (A := A) (K := K) (L := L) p ∨
    ArtinSchreierWeakResidueCase (A := A) (K := K) (L := L) p

theorem extension_defined_by_nice_polynomial
    {A K L : Type*} [CommRing A] [Field K] [Field L]
    [Algebra A K] [Algebra A L] [Algebra K L]
    [IsDomain A] [IsDiscreteValuationRing A]
    [FiniteDimensional K L] [Algebra.IsSeparable K L]
    [IsGalois K L]
    {p : ℕ} (hp : Nat.Prime p) (w : A) (P : Polynomial A)
    (hchar : ringChar A = 0 ∧ ringChar (DVRResidueField A) = p)
    (hprepared : ∃ Q : PreparedPolynomialData A p w, Q.P = P)
    (ξ : K) (z : L)
    (hz : Polynomial.eval₂ (algebraMap A L) z P = algebraMap K L ξ)
    (hgen : Algebra.adjoin K {z} = ⊤) (π : A) (hπ : Irreducible π) :
    NicePolynomialCase (A := A) (K := K) (L := L) p P ∧
      ((∃ a : A, algebraMap A K a = ξ) →
        IsTrivialFieldExtension (K := K) (L := L) ∨
          ArtinSchreierUnramifiedOfDegree (A := A) (K := K) (L := L) p) ∧
      (∀ n : ℕ, 0 < n → n % p ≠ 0 → ∀ a : A, IsUnit a →
        ξ = (algebraMap A K π)⁻¹ ^ n * algebraMap A K a →
          ArtinSchreierTotallyRamifiedOfDegree (A := A) (K := K) (L := L) p) ∧
      (∀ n : ℕ, 0 < n → p ∣ n → ∀ a : A,
        ResidueClassNotPthPower p a →
        ξ = (algebraMap A K π)⁻¹ ^ n * algebraMap A K a →
          ArtinSchreierWeakResidueCase (A := A) (K := K) (L := L) p) := by
  sorry

def FiniteLevelBaseChangeAlternative
    {B : Type uB} {K : Type uK} {L : Type uL} {M : Type uM}
    [CommRing B] [Field K] [Field L] [Field M]
    [Algebra B L] [Algebra B M] [Algebra K L]
    [Algebra K M] [Algebra L M] [IsDomain B]
    [IsDiscreteValuationRing B]
    (p : ℕ) (w : B) (P : Polynomial B) : Prop :=
  ∃ (B₁ : Type uB) (L₁ : Type uL) (M₁ : Type uM)
    (hB₁ : CommRing B₁) (hL₁ : Field L₁)
    (hM₁ : Field M₁) (hB₁L₁ : Algebra B₁ L₁)
    (hB₁M₁ : Algebra B₁ M₁) (hL₁M₁ : Algebra L₁ M₁)
    (hK₁L₁ : Algebra K L₁) (hdomB₁ : IsDomain B₁)
    (hdvrB₁ : IsDiscreteValuationRing B₁) (hBB₁ : Algebra B B₁),
    letI := hB₁
    letI := hL₁
    letI := hM₁
    letI := hB₁L₁
    letI := hB₁M₁
    letI := hL₁M₁
    letI := hK₁L₁
    letI := hdomB₁
    letI := hdvrB₁
    letI := hBB₁
    ∃ P₁ : Polynomial B₁,
      IsDegreePFiniteLevel (A := B₁) (K := L₁) (L := M₁) p
        (algebraMap B B₁ w) P₁

def BoundedFiniteLevelAlternative
    {B : Type uB} {K : Type uK} {L : Type uL} {M : Type uM}
    [CommRing B] [Field K] [Field L] [Field M]
    [Algebra B L] [Algebra B M] [Algebra K L]
    [Algebra K M] [Algebra L M] [IsDomain B]
    [IsDiscreteValuationRing B]
    (p : ℕ) (w : B) (P : Polynomial B) (bound : ℚ) : Prop :=
  ∃ l' : ℚ, l' ≤ bound ∧
    FiniteLevelBaseChangeAlternative (B := B) (K := K) (L := L) (M := M)
      p w P

theorem make_finite_level
    {A B C K L M : Type*} [CommRing A] [CommRing B] [CommRing C]
    [Field K] [Field L] [Field M]
    [Algebra A K] [Algebra A L] [Algebra A M]
    [Algebra B L] [Algebra B M] [Algebra C M]
    [Algebra K L] [Algebra K M] [Algebra L M]
    [IsDomain A] [IsDomain B] [IsDomain C]
    [IsDiscreteValuationRing A] [IsDiscreteValuationRing B]
    [IsDiscreteValuationRing C]
    (T : DVRTower A B C K L M) (π : A) (p : ℕ) (w : B) (P : Polynomial B)
    (hchar : ringChar A = 0 ∧ ringChar (DVRResidueField A) = p)
    (hroot : ∃ ζ : B, IsPrimitivePthRoot ζ p ∧ w = 1 - ζ)
    (hWeak : WeaklyUnramified T.ab.map)
    [IsGalois L M] (hdegree : Module.finrank L M = p) :
    ∃ (K₁ : Type*) (hK₁ : Field K₁) (hKK₁ : Algebra K K₁)
      (hAK₁ : Algebra A K₁) (hfin : FiniteDimensional K K₁)
      (hsep : Algebra.IsSeparable K K₁) (hGalois : IsGalois K K₁),
      letI := hK₁
      letI := hKK₁
      letI := hAK₁
      letI := hfin
      letI := hsep
      letI := hGalois
      ∃ X₁ : FiniteSeparableExtensionData A K K₁,
        IsTotallyRamified X₁ ∧
          (WeakSolutionFor T.ac K₁ ∨
            FiniteLevelBaseChangeAlternative (B := B) (K := K) (L := L) (M := M)
              p w P) := by
  sorry

theorem lowering_the_level
    {A B C K L M : Type*} [CommRing A] [CommRing B] [CommRing C]
    [Field K] [Field L] [Field M]
    [Algebra A K] [Algebra A L] [Algebra A M]
    [Algebra B L] [Algebra B M] [Algebra C M]
    [Algebra K L] [Algebra K M] [Algebra L M]
    [IsDomain A] [IsDomain B] [IsDomain C]
    [IsDiscreteValuationRing A] [IsDiscreteValuationRing B]
    [IsDiscreteValuationRing C]
    (T : DVRTower A B C K L M) (π : A) (p : ℕ) (w : B) (P : Polynomial B)
    (hchar : ringChar A = 0 ∧ ringChar (DVRResidueField A) = p)
    (hroot : ∃ ζ : B, IsPrimitivePthRoot ζ p ∧ w = 1 - ζ)
    (e₁ : ℕ) (l : ℚ) (hl : l > 0)
    (hWeak : WeaklyUnramified T.ab.map)
    (hintersection : ResidueFrobeniusCoreContained T.ab.map p)
    (hLevel : l = FiniteLevel (A := B) (K := L) (L := M) e₁ p
      (T.ab.map.hom π) w P) :
    ∃ (K₁ : Type*) (hK₁ : Field K₁) (hKK₁ : Algebra K K₁)
      (hAK₁ : Algebra A K₁) (hfin : FiniteDimensional K K₁)
      (hsep : Algebra.IsSeparable K K₁),
      letI := hK₁
      letI := hKK₁
      letI := hAK₁
      letI := hfin
      letI := hsep
      ∃ X₁ : FiniteSeparableExtensionData A K K₁,
        IsTotallyRamified X₁ ∧
          (WeakSolutionFor T.ac K₁ ∨
            BoundedFiniteLevelAlternative (B := B) (K := K) (L := L) (M := M)
              p w P (max (max 0 (l - 1)) (2 * l - p))) := by
  sorry

def FractionalPowerMembership
    {B K : Type*} [CommRing B] [Field K] [Algebra B K]
    (π : B) (r : ℤ) (x : K) : Prop :=
  ∃ b : B, x = (algebraMap B K π) ^ r * algebraMap B K b

theorem first_congruence
    {A B K : Type*} [CommRing A] [CommRing B] [Field K]
    [Algebra A B] [Algebra B K] [Algebra A K] [IsScalarTower A B K]
    [IsDomain B] [IsDiscreteValuationRing B]
    (π : A) (w : B) (p n e₁ : ℕ) (P : Polynomial B)
    (hprepared : ∃ Q : PreparedPolynomialData B p w, Q.P = P)
    (hw : ∃ u : B, IsUnit u ∧ w = u * (algebraMap A B π) ^ e₁) :
    ∀ z : K,
      FractionalPowerMembership (algebraMap A B π) (-(n : ℤ))
        (Polynomial.eval₂ (algebraMap B K) z P) →
        FractionalPowerMembership (algebraMap A B π)
          (-(n : ℤ) + (e₁ : ℤ))
          (Polynomial.eval₂ (algebraMap B K) z P - (z ^ p - z)) := by
  sorry

theorem second_congruence
    {B K : Type*} [CommRing B] [Field K] [Algebra B K]
    [IsDomain B] [IsDiscreteValuationRing B]
    (π w : B) (ξ₁ ξ₂ : K) (p n e₁ : ℕ)
    (h₁ : FractionalPowerMembership π (-(n : ℤ)) ξ₁)
    (h₂ : FractionalPowerMembership π (-(n : ℤ)) ξ₂) :
    FractionalPowerMembership π
      (-2 * (n : ℤ) + (p : ℤ) * (e₁ : ℤ))
      ((algebraMap B K w) ^ p * ξ₁ * ξ₂) := by
  sorry

/-! ## The complete case and Epp's theorem -/

def SeparableAlgebraicElementOver
    {k K : Type*} [Field k] [Field K] [Algebra k K] (x : K) : Prop :=
  ∃ S : Subalgebra k K, x ∈ S ∧ Algebra.IsAlgebraic k S ∧
    Algebra.IsSeparable k S

def FrobeniusCoreSeparableAlgebraic
    {k K : Type*} [Field k] [Field K] [Algebra k K] (p : ℕ) : Prop :=
  ∀ x : K, FrobeniusCoreElement p x →
    SeparableAlgebraicElementOver (k := k) (K := K) x

theorem special_case
    {A B C K L M : Type*} [CommRing A] [CommRing B] [CommRing C]
    [Field K] [Field L] [Field M]
    [Algebra A K] [Algebra A L] [Algebra A M]
    [Algebra B L] [Algebra B M] [Algebra C M]
    [Algebra K L] [Algebra K M] [Algebra L M]
    [IsDomain A] [IsDomain B] [IsDomain C]
    [IsDiscreteValuationRing A] [IsDiscreteValuationRing B]
    [IsDiscreteValuationRing C]
    (T : DVRTower A B C K L M) {p : ℕ} (hp : Nat.Prime p)
    [CharP (DVRResidueField A) p] [IsAlgClosed (DVRResidueField A)]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    [IsAdicComplete (IsLocalRing.maximalIdeal B) B]
    [FiniteDimensional L M] (hWeak : WeaklyUnramified T.ab.map)
    (hCore : letI := residueFieldAlgebra T.ab.map
      FrobeniusCoreContainedIn (k := DVRResidueField A)
        (K := DVRResidueField B) p) :
    ∃ (K₁ : Type*) (hK₁ : Field K₁) (hKK₁ : Algebra K K₁)
      (hAK₁ : Algebra A K₁) (hfin : FiniteDimensional K K₁),
      letI := hK₁
      letI := hKK₁
      letI := hAK₁
      letI := hfin
      WeakSolutionFor T.ac K₁ := by
  sorry

theorem epp
    {A B K L : Type*} [CommRing A] [CommRing B] [Field K] [Field L]
    [Algebra A K] [Algebra A L] [Algebra B L] [Algebra K L]
    [IsDomain A] [IsDomain B]
    [IsDiscreteValuationRing A] [IsDiscreteValuationRing B]
    (D : DVRFieldDiagram A B K L)
    (hchar : ringChar (DVRResidueField A) = 0 ∨
      ∃ p : ℕ, Nat.Prime p ∧ ringChar (DVRResidueField A) = p ∧
        letI := residueFieldAlgebra D.map
        FrobeniusCoreSeparableAlgebraic (k := DVRResidueField A)
          (K := DVRResidueField B) p) :
    ∃ (K₁ : Type*) (hK₁ : Field K₁) (hKK₁ : Algebra K K₁)
      (hAK₁ : Algebra A K₁) (hfin : FiniteDimensional K K₁),
      letI := hK₁
      letI := hKK₁
      letI := hAK₁
      letI := hfin
      WeakSolutionFor D K₁ := by
  sorry

end

end Formalization.Books.MoreAlgebra.Unit116
