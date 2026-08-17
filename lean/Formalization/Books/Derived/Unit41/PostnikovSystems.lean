import Mathlib.Algebra.Homology.Embedding.CochainComplex
import Mathlib.Algebra.Homology.Embedding.Extend
import Mathlib.CategoryTheory.Functor.OfSequence
import Mathlib.CategoryTheory.Limits.Shapes.Biproducts
import Formalization.Books.Derived.Unit04.ElementaryResults
import Formalization.Books.Derived.Unit33.DerivedColimits

/-!
# Derived Categories, Chapter 41: Postnikov systems

Finite complexes are represented by `HomologicalComplex` with the finite
downward shape.  A Postnikov system records its objects, the maps to the
terms of the complex, and the distinguished triangle between two successive
terms.  The theorem interfaces below retain the source's existence,
extension, uniqueness, and vanishing statements without attempting their
proofs.
-/

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Preadditive
open CategoryTheory.Pretriangulated
open CategoryTheory.Triangulated
open ComplexShape
open Formalization.Books.Derived.Unit04
open Formalization.Books.Derived.Unit33
open Formalization.Books.Homology.Unit03
open scoped CategoryTheory.Pretriangulated.Opposite ZeroObject

universe v u w

namespace Formalization.Books.Derived.Unit41

/-! ## Finite complexes -/

/-- The finite downward complex shape on `Fin (n + 1)`. -/
def finitePostnikovShape (n : ℕ) : ComplexShape (Fin (n + 1)) where
  Rel i j := j.val + 1 = i.val
  next_eq := by
    intro i j j' hij hij'
    apply Fin.ext
    omega
  prev_eq := by
    intro i i' j hij hij'
    apply Fin.ext
    omega

/-- A finite complex `X_n → ⋯ → X_0` in a category with zero morphisms. -/
abbrev FinitePostnikovComplex
    (C : Type u) [Category.{v} C] [HasZeroMorphisms C] (n : ℕ) :=
  HomologicalComplex C (finitePostnikovShape n)

/-- The index `i` viewed in `Fin (n + 1)`. -/
def finitePostnikovIndex
    {n : ℕ} (i : Fin n) : Fin (n + 1) :=
  ⟨i.val, by omega⟩

/-- The successor index used for the arrow `X_(i+1) → X_i`. -/
def finitePostnikovSuccIndex
    {n : ℕ} (i : Fin n) : Fin (n + 1) :=
  ⟨i.val + 1, by omega⟩

/-- The last index of a finite complex. -/
def finitePostnikovLastIndex (n : ℕ) : Fin (n + 1) :=
  ⟨n, by omega⟩

/-- The degree-zero index of a finite complex. -/
def finitePostnikovZeroIndex (n : ℕ) : Fin (n + 1) :=
  ⟨0, by omega⟩

/-- The index `j - (i + 1)` when `i + 1 ≤ j`. -/
def finitePostnikovSubIndex
    {n : ℕ} (i : Fin n) (j : Fin (n + 1))
    (h : i.val + 1 ≤ j.val) : Fin (n + 1) :=
  ⟨j.val - (i.val + 1), by omega⟩

/-- The differential `X_(i+1) → X_i` of a finite complex. -/
abbrev finitePostnikovDifferential
    {C : Type u} [Category.{v} C] [HasZeroMorphisms C]
    {n : ℕ} (K : FinitePostnikovComplex C n) (i : Fin n) :
    K.X (finitePostnikovSuccIndex i) ⟶ K.X (finitePostnikovIndex i) :=
  K.d (finitePostnikovSuccIndex i) (finitePostnikovIndex i)

/-! ## The finite Postnikov-system structure and its maps -/

variable {C : Type u} [Category.{v} C] [AdditiveCategory C]
  [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive]
  [Pretriangulated C] [IsTriangulated C]

/-- The data of a Postnikov system for a finite complex.

`toX i` is the map `Y_i → X_i`; for `i < n`, the corresponding distinguished
triangle is `Y_(i+1) → X_(i+1) → Y_i → Y_(i+1)[1]`. -/
structure PostnikovSystem
    {n : ℕ} (K : FinitePostnikovComplex C n) where
  Y : Fin (n + 1) → C
  toX : ∀ i, Y i ⟶ K.X i
  baseIso : Y (finitePostnikovZeroIndex n) ≅ K.X (finitePostnikovZeroIndex n)
  baseIso_hom : baseIso.hom = toX _
  fromX : ∀ i : Fin n, K.X (finitePostnikovSuccIndex i) ⟶
    Y (finitePostnikovIndex i)
  connecting : ∀ i : Fin n,
    Y (finitePostnikovIndex i) ⟶
      (shiftFunctor C (1 : ℤ)).obj (Y (finitePostnikovSuccIndex i))
  distinguished : ∀ i : Fin n,
    Triangle.mk (toX (finitePostnikovSuccIndex i)) (fromX i) (connecting i) ∈
      distTriang C
  compatibility : ∀ i : Fin n,
    fromX i ≫ toX (finitePostnikovIndex i) = finitePostnikovDifferential K i

/-- The distinguished triangle at a step of a Postnikov system. -/
def postnikovTriangle
    {n : ℕ} {K : FinitePostnikovComplex C n} (P : PostnikovSystem K)
    (i : Fin n) : Triangle C :=
  Triangle.mk (P.toX (finitePostnikovSuccIndex i)) (P.fromX i) (P.connecting i)

/-- The rotated and shifted distinguished triangle displayed in the source:
`Y_i[i] → Y_(i+1)[i+1] → X_(i+1)[i+1] → Y_i[i+1]`. -/
def postnikovShiftedTriangle
    {n : ℕ} {K : FinitePostnikovComplex C n} (P : PostnikovSystem K)
    (i : Fin n) : Triangle C :=
  (Triangle.shiftFunctor C (i.val : ℤ)).obj
    ((rotate C).obj ((rotate C).obj (postnikovTriangle P i)))

/-- A morphism of Postnikov systems over a morphism of finite complexes. -/
structure PostnikovSystemHom
    {n : ℕ} {K K' : FinitePostnikovComplex C n}
    {P : PostnikovSystem K} {P' : PostnikovSystem K'}
    (f : K ⟶ K') where
  y : ∀ i, P.Y i ⟶ P'.Y i
  toX_naturality : ∀ i,
    P.toX i ≫ f.f i = y i ≫ P'.toX i
  triangleMap : ∀ i : Fin n,
    postnikovTriangle P i ⟶ postnikovTriangle P' i
  triangleMap_hom₁ : ∀ i : Fin n,
    (triangleMap i).hom₁ = y (finitePostnikovSuccIndex i)
  triangleMap_hom₂ : ∀ i : Fin n,
    (triangleMap i).hom₂ = f.f (finitePostnikovSuccIndex i)
  triangleMap_hom₃ : ∀ i : Fin n,
    (triangleMap i).hom₃ = y (finitePostnikovIndex i)

/-- A morphism of Postnikov systems whose maps on the `Y_i` are isomorphisms. -/
structure PostnikovSystemIso
    {n : ℕ} {K K' : FinitePostnikovComplex C n}
    {P : PostnikovSystem K} {P' : PostnikovSystem K'}
    (f : K ⟶ K') where
  hom : PostnikovSystemHom (P := P) (P' := P') f
  y_isIso : ∀ i, IsIso (hom.y i)

/-- The maps `Y_i → Y_(i+1)[1]` form the source's Postnikov tower. -/
abbrev postnikovTowerMap
    {n : ℕ} {K : FinitePostnikovComplex C n} (P : PostnikovSystem K)
    (i : Fin n) := P.connecting i

/-! ## The direct-sum special case and the low-length assertions -/

/-- All differentials of a finite complex vanish. -/
def IsZeroPostnikovComplex
    {n : ℕ} (K : FinitePostnikovComplex C n) : Prop :=
  ∀ i : Fin n, finitePostnikovDifferential K i = 0

/-- The finite direct sum `⊕ i, X_i[i]` from the zero-differential remark. -/
noncomputable def zeroDifferentialTotal
    {n : ℕ} (K : FinitePostnikovComplex C n) : C :=
  ⨁ fun i : Fin (n + 1) =>
    (shiftFunctor C (i.val : ℤ)).obj (K.X i)

/-- In the zero-differential case the last totalization can be chosen as the
finite direct sum of the shifted terms. -/
theorem exists_zero_differential_postnikov_system
    {n : ℕ} (K : FinitePostnikovComplex C n)
    (hK : IsZeroPostnikovComplex K) :
    ∃ P : PostnikovSystem K,
      Nonempty
        ((shiftFunctor C (n : ℤ)).obj (P.Y (finitePostnikovLastIndex n)) ≅
          zeroDifferentialTotal K) := by
  sorry

/-- Every shifted triangle in the Postnikov tower is distinguished. -/
theorem postnikovShiftedTriangle_distinguished
    {n : ℕ} {K : FinitePostnikovComplex C n} (P : PostnikovSystem K)
    (i : Fin n) :
    postnikovShiftedTriangle P i ∈ distTriang C := by
  sorry

/-- Existence of a Postnikov system for a complex of length zero. -/
theorem postnikovSystem_exists_length_zero
    (K : FinitePostnikovComplex C 0) :
    Nonempty (PostnikovSystem K) := by
  sorry

/-- Any map of length-zero complexes extends to a map of chosen systems. -/
theorem postnikovSystemHom_exists_length_zero
    {K K' : FinitePostnikovComplex C 0}
    (f : K ⟶ K') (P : PostnikovSystem K) (P' : PostnikovSystem K') :
    Nonempty (PostnikovSystemHom (P := P) (P' := P') f) := by
  sorry

/-- The length-zero extension is unique. -/
theorem postnikovSystemHom_unique_length_zero
    {K K' : FinitePostnikovComplex C 0}
    (f : K ⟶ K') (P : PostnikovSystem K) (P' : PostnikovSystem K')
    (φ ψ : PostnikovSystemHom (P := P) (P' := P') f) :
    φ = ψ := by
  sorry

/-- Existence of a Postnikov system for a complex of length one. -/
theorem postnikovSystem_exists_length_one
    (K : FinitePostnikovComplex C 1) :
    Nonempty (PostnikovSystem K) := by
  sorry

/-- Any map of length-one complexes extends to a map of chosen systems. -/
theorem postnikovSystemHom_exists_length_one
    {K K' : FinitePostnikovComplex C 1}
    (f : K ⟶ K') (P : PostnikovSystem K) (P' : PostnikovSystem K') :
    Nonempty (PostnikovSystemHom (P := P) (P' := P') f) := by
  sorry

/-- The source's warning that length-one extensions need not be unique. -/
def HasLengthOnePostnikovExtensionNonuniqueness : Prop :=
  ∃ (K K' : FinitePostnikovComplex C 1) (f : K ⟶ K')
    (P : PostnikovSystem K) (P' : PostnikovSystem K')
    (φ ψ : PostnikovSystemHom (P := P) (P' := P') f),
    φ ≠ ψ

/-- Existence of a Postnikov system for a complex of length two. -/
theorem postnikovSystem_exists_length_two
    (K : FinitePostnikovComplex C 2) :
    Nonempty (PostnikovSystem K) := by
  sorry

/-- The source's warning that length-two maps need not extend is represented
by the exact existential failure predicate; no particular counterexample is
specified in the source section. -/
def HasLengthTwoPostnikovExtensionFailure : Prop :=
  ∃ (K K' : FinitePostnikovComplex C 2) (f : K ⟶ K')
    (P : PostnikovSystem K) (P' : PostnikovSystem K'),
    ¬ Nonempty (PostnikovSystemHom (P := P) (P' := P') f)

/-- The source's warning that existence can fail beyond length two. -/
def HasPostnikovExistenceFailure (n : ℕ) : Prop :=
  ∃ K : FinitePostnikovComplex C n, ¬ Nonempty (PostnikovSystem K)

/-- The source's warning that existence can fail for some length greater than
two. -/
def HasPostnikovExistenceFailureBeyondTwo : Prop :=
  ∃ n : ℕ, 2 < n ∧
    ∃ K : FinitePostnikovComplex C n, ¬ Nonempty (PostnikovSystem K)

/-! ## Vanishing hypotheses for maps of Postnikov systems -/

/-- The vanishing condition labelled `(P)` in the source. -/
def PostnikovVanishing
    {n : ℕ} (K K' : FinitePostnikovComplex C n) : Prop :=
  ∀ (i j : Fin (n + 1)), j.val + 1 < i.val →
    HomIsZero
      ((shiftFunctor C ((i.val : ℤ) - (j.val : ℤ) - 1)).obj (K.X i))
      (K'.X j)

/-- The shifted vanishing statement obtained for the `Y'_j`. -/
theorem postnikovSystem_vanishing_to_Y
    {n : ℕ} {K K' : FinitePostnikovComplex C n}
    (P' : PostnikovSystem K')
    (hP : PostnikovVanishing K K') :
    ∀ (i j : Fin (n + 1)), j.val + 1 < i.val →
      HomIsZero
        ((shiftFunctor C ((i.val : ℤ) - (j.val : ℤ) - 1)).obj (K.X i))
        (P'.Y j) := by
  sorry

/-- Under `(P)`, a map of complexes extends to a map of Postnikov systems. -/
theorem postnikovSystemHom_exists_of_vanishing
    {n : ℕ} {K K' : FinitePostnikovComplex C n}
    (f : K ⟶ K') (P : PostnikovSystem K) (P' : PostnikovSystem K')
    (hP : PostnikovVanishing K K') :
    Nonempty (PostnikovSystemHom (P := P) (P' := P') f) := by
  sorry

/-! ## The three uniqueness hypotheses -/

/-- The first uniqueness hypothesis in the source. -/
def PostnikovHomUniqueLeft
    {n : ℕ} (K K' : FinitePostnikovComplex C n)
    (P' : PostnikovSystem K') : Prop :=
  ∀ (i : Fin (n + 1)), 0 < i.val →
    HomIsZero
      ((shiftFunctor C (i.val : ℤ)).obj (K.X i))
      ((shiftFunctor C (n : ℤ)).obj (P'.Y (finitePostnikovLastIndex n)))

/-- The second uniqueness hypothesis in the source. -/
def PostnikovHomUniqueRight
    {n : ℕ} (K K' : FinitePostnikovComplex C n)
    (P : PostnikovSystem K) : Prop :=
  ∀ (i : Fin n),
    HomIsZero
      ((shiftFunctor C (n : ℤ)).obj (P.Y (finitePostnikovLastIndex n)))
      ((shiftFunctor C ((n - (i.val + 1) : ℕ) : ℤ)).obj
        (K'.X ⟨n - (i.val + 1), by omega⟩))

/-- The two-sided uniqueness hypothesis in the source. -/
def PostnikovHomUniqueTwoSided
    {n : ℕ} (K K' : FinitePostnikovComplex C n) : Prop :=
  ∀ (i : Fin n) (j : Fin (n + 1)) (hij : i.val + 1 ≤ j.val),
    HomIsZero
        ((shiftFunctor C (-((i.val + 1 : ℤ)) + 1)).obj
          (K.X (finitePostnikovSubIndex i j hij)))
        (K'.X j) ∧
      HomIsZero (K.X j)
        ((shiftFunctor C (-((i.val + 1 : ℤ)))).obj
          (K'.X (finitePostnikovSubIndex i j hij)))

/-- Under any one of the three source hypotheses, a map of Postnikov systems
is unique. -/
theorem postnikovSystemHom_unique_of_vanishing
    {n : ℕ} {K K' : FinitePostnikovComplex C n}
    (f : K ⟶ K') (P : PostnikovSystem K) (P' : PostnikovSystem K')
    (h : PostnikovHomUniqueLeft K K' P' ∨
      PostnikovHomUniqueRight K K' P ∨
      PostnikovHomUniqueTwoSided K K')
    (φ ψ : PostnikovSystemHom (P := P) (P' := P') f) :
    φ = ψ := by
  sorry

/-! ## Existence and uniqueness from vanishing of the complex terms -/

/-- The stronger vanishing condition used to construct a Postnikov system. -/
def PostnikovExistenceVanishing
    {n : ℕ} (K : FinitePostnikovComplex C n) : Prop :=
  ∀ (i j : Fin (n + 1)), j.val + 2 < i.val →
    HomIsZero
      ((shiftFunctor C ((i.val : ℤ) - (j.val : ℤ) - 2)).obj (K.X i))
      (K.X j)

/-- The stronger vanishing condition implies existence. -/
theorem postnikovSystem_exists_of_vanishing
    {n : ℕ} (K : FinitePostnikovComplex C n)
    (hK : PostnikovExistenceVanishing K) :
    Nonempty (PostnikovSystem K) := by
  sorry

/-- A pair of systems over the same complex is isomorphic when `(P)` holds. -/
theorem postnikovSystem_isomorphic_of_vanishing
    {n : ℕ} {K : FinitePostnikovComplex C n}
    (P P' : PostnikovSystem K)
    (hK : PostnikovVanishing K K) :
    Nonempty
      (PostnikovSystemIso (P := P) (P' := P') (𝟙 K)) := by
  sorry

/-! ## The abelian-category example and its homotopy colimit -/

/-- The chain complex obtained by embedding an `ℕ`-indexed chain complex into
the cochain complexes indexed by `ℤ`, with the `n`th term in degree `-n`. -/
noncomputable def chainComplexTotalization
    {A : Type u} [Category.{v} A] [Abelian A]
    (K : ChainComplex A ℕ) : CochainComplex A ℤ :=
  (ComplexShape.embeddingDownNat.extendFunctor A).obj K

/-- The chain complex of the terms `A_n` viewed in the derived category. -/
noncomputable def derivedChainComplex
    {A : Type u} [Category.{v} A] [Abelian A]
    [HasDerivedCategory.{w} A]
    (K : ChainComplex A ℕ) : ChainComplex (DerivedCategory A) ℕ where
  X n := (DerivedCategory.singleFunctor A 0).obj (K.X n)
  d i j := (DerivedCategory.singleFunctor A 0).map (K.d i j)
  shape i j hij := by
    rw [K.shape i j hij, Functor.map_zero]
  d_comp_d' i j k _ _ := by
    rw [← (DerivedCategory.singleFunctor A 0).map_comp, K.d_comp_d,
      Functor.map_zero]

/-- The finite derived object represented by the first `n + 1` terms of the
chain complex.  With Mathlib's cochain indexing this is the realization of
`(A_n → ⋯ → A_0)[-n]`. -/
noncomputable def abelianPostnikovTerm
    {A : Type u} [Category.{v} A] [Abelian A]
    [HasDerivedCategory.{w} A]
    (K : ChainComplex A ℕ) (n : ℕ) : DerivedCategory A :=
  (DerivedCategory.Q (C := A)).obj
    ((chainComplexTotalization K).truncGE (-(n : ℤ)))

/-- The infinite extension of the finite Postnikov-system structure. -/
structure InfinitePostnikovSystem
    {D : Type u} [Category.{v} D] [AdditiveCategory D]
    [HasShift D ℤ] [∀ k : ℤ, (shiftFunctor D k).Additive]
    [Pretriangulated D] [IsTriangulated D]
    (K : ChainComplex D ℕ) where
  Y : ℕ → D
  toX : ∀ i, Y i ⟶ K.X i
  baseIso : Y 0 ≅ K.X 0
  baseIso_hom : baseIso.hom = toX 0
  fromX : ∀ i, K.X (i + 1) ⟶ Y i
  connecting : ∀ i, Y i ⟶ (shiftFunctor D (1 : ℤ)).obj (Y (i + 1))
  distinguished : ∀ i,
    Triangle.mk (toX (i + 1)) (fromX i) (connecting i) ∈ distTriang D
  compatibility : ∀ i, fromX i ≫ toX i = K.d (i + 1) i

/-- The triangle at stage `i` of an infinite Postnikov system. -/
def InfinitePostnikovSystem.triangle
    {D : Type u} [Category.{v} D] [AdditiveCategory D]
    [HasShift D ℤ] [∀ k : ℤ, (shiftFunctor D k).Additive]
    [Pretriangulated D] [IsTriangulated D]
    {K : ChainComplex D ℕ} (P : InfinitePostnikovSystem K) (i : ℕ) :
    Triangle D :=
  Triangle.mk (P.toX (i + 1)) (P.fromX i) (P.connecting i)

/-- The transition map `Y_i[i] → Y_(i+1)[i+1]` in the infinite tower. -/
noncomputable def InfinitePostnikovSystem.totalizationTransition
    {D : Type u} [Category.{v} D] [AdditiveCategory D]
    [HasShift D ℤ] [∀ k : ℤ, (shiftFunctor D k).Additive]
    [Pretriangulated D] [IsTriangulated D]
    {K : ChainComplex D ℕ} (P : InfinitePostnikovSystem K) (i : ℕ) :
    (shiftFunctor D (i : ℤ)).obj (P.Y i) ⟶
      (shiftFunctor D ((i + 1 : ℕ) : ℤ)).obj (P.Y (i + 1)) :=
  P.connecting i⟦(i : ℤ)⟧' ≫
    (shiftFunctorAdd' D (1 : ℤ) (i : ℤ) ((i + 1 : ℕ) : ℤ) (by omega)).inv.app
      (P.Y (i + 1))

/-- The sequential system of shifted `Y_i` appearing in the hocolim formula. -/
noncomputable def InfinitePostnikovSystem.totalizationSystem
    {D : Type u} [Category.{v} D] [AdditiveCategory D]
    [HasShift D ℤ] [∀ k : ℤ, (shiftFunctor D k).Additive]
    [Pretriangulated D] [IsTriangulated D]
    {K : ChainComplex D ℕ} (P : InfinitePostnikovSystem K) : ℕ ⥤ D :=
  Functor.ofSequence (fun i => P.totalizationTransition i)

/-- The precise data in the abelian-category example, including the
finite truncation description and its derived homotopy-colimit identity. -/
structure AbelianPostnikovExample
    {A : Type u} [Category.{v} A] [Abelian A]
    [HasDerivedCategory.{w} A]
    [HasCountableCoproducts A] [CountableAB4 A]
    (K : ChainComplex A ℕ) where
  system : InfinitePostnikovSystem (derivedChainComplex K)
  Y_spec : ∀ n, Nonempty (system.Y n ≅ abelianPostnikovTerm K n)
  hocolim_spec : ∃ T : DerivedCategory A,
    IsDerivedColimit system.totalizationSystem T ∧
      Nonempty
        (T ≅ (DerivedCategory.Q (C := A)).obj (chainComplexTotalization K))

/-- The abelian chain-complex example from the source. -/
theorem exists_abelian_postnikov_example
    {A : Type u} [Category.{v} A] [Abelian A]
    [HasDerivedCategory.{w} A]
    [HasCountableCoproducts A] [CountableAB4 A]
    (K : ChainComplex A ℕ) :
    Nonempty (AbelianPostnikovExample K) := by
  sorry


end Formalization.Books.Derived.Unit41
