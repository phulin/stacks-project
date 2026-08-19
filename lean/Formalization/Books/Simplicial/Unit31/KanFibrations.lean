import Formalization.Books.Simplicial.Unit30
import Formalization.Books.Simplicial.Unit23.SimplicialObjectsAndChainComplexes
import Mathlib.Algebra.Category.Grp.Basic
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.AlgebraicTopology.ModelCategory.Instances
import Mathlib.AlgebraicTopology.SimplicialSet.KanComplex

/-!
# Simplicial Methods, Chapter 31: Kan fibrations

The horn `Λ[n, k]` is Mathlib's canonical `SSet.horn n k`, and the category
with fibrations on simplicial sets is Mathlib's canonical Quillen structure.
The standard simplex, its unique top simplex, and its face inclusions are
likewise provided by Mathlib's `SSet.stdSimplex` API.  Consequently the
source's Kan-fibration and Kan-complex definitions are recorded by the
corresponding canonical properties rather than by parallel lifting predicates.
The remaining declarations give the closure results and the
simplicial-group and simplicial-abelian-group applications from the source.
-/

noncomputable section

namespace Formalization.Books.Simplicial.Unit31

open CategoryTheory
open CategoryTheory.Limits
open Opposite
open scoped _root_.Simplicial
open SSet.modelCategoryQuillen

universe u v w

/-! ## Horns and the Kan lifting property

The source assumes `1 ≤ n` whenever it discusses an `n`-horn.  The canonical
`SSet.horn` supplies the generated subcomplex and its inclusion; the
`horn_obj_zero` lemma supplies the nonemptiness assertion in the positive
dimensions used below.
-/

/-- The source's Kan-fibration property, using Mathlib's canonical fibration
class for simplicial sets (whose generating lifting maps are the horn
inclusions). -/
abbrev KanFibration {X Y : SSet.{u}} (f : X ⟶ Y) : Prop :=
  HomotopicalAlgebra.Fibration f

/-- The source's Kan-complex property, using Mathlib's canonical fibrant
objects in simplicial sets. -/
abbrev KanComplex (X : SSet.{u}) : Prop :=
  SSet.KanComplex X

/-- Every positive-dimensional horn has a vertex. -/
theorem horn_nonempty (n : ℕ) (hn : 1 ≤ n) (k : Fin (n + 1)) :
    Nonempty ((SSet.horn n k : SSet.{u}) _⦋0⦌) := by
  obtain _ | n := n
  · omega
  obtain _ | n := n
  · fin_cases k
    · refine ⟨⟨SSet.stdSimplex.objEquiv.symm (⦋0⦌.const ⦋1⦌ 0), ?_⟩⟩
      rw [SSet.mem_horn_iff, SSet.stdSimplex.coe_asOrderHom_objEquiv_symm]
      intro h
      rw [Set.eq_univ_iff_forall] at h
      have h1 := h (1 : Fin 2)
      simp at h1
      change (0 : Fin 2) = 1 at h1
      exact Fin.zero_ne_one h1
    · refine ⟨⟨SSet.stdSimplex.objEquiv.symm (⦋0⦌.const ⦋1⦌ 1), ?_⟩⟩
      rw [SSet.mem_horn_iff, SSet.stdSimplex.coe_asOrderHom_objEquiv_symm]
      intro h
      rw [Set.eq_univ_iff_forall] at h
      have h0 := h (0 : Fin 2)
      simp at h0
      change (1 : Fin 2) = 0 at h0
      omega
  · have htop := SSet.horn_obj_zero n k
    refine ⟨⟨SSet.stdSimplex.objEquiv.symm (⦋0⦌.const ⦋n + 2⦌ 0), ?_⟩⟩
    rw [htop]
    simp

/-! The source's observation about the empty simplicial set is the vacuous
lifting property.  We retain it as a theorem interface; the implication from
trivial to ordinary Kan fibrations is the canonical inclusion of lifting
classes already present in Chapter 30 and Mathlib's model-category API. -/

theorem empty_to_kanFibration {Y : SSet.{u}} (f : (⊥_ SSet.{u}) ⟶ Y) :
    KanFibration f := by
  change HomotopicalAlgebra.Fibration f
  rw [SSet.modelCategoryQuillen.fibration_iff]
  intro A B i hi
  simp only [SSet.modelCategoryQuillen.J,
    CategoryTheory.MorphismProperty.iSup_iff] at hi
  obtain ⟨n, ⟨k⟩⟩ := hi
  refine ⟨fun {a} {b} sq => ?_⟩
  let x := (horn_nonempty (n + 1) (by omega) k).some
  let y := a.app (op ⦋0⦌) x
  let z₀ : (Δ[1] : SSet.{u}) _⦋0⦌ := SSet.stdSimplex.obj₀Equiv.symm 0
  let z₁ : (Δ[1] : SSet.{u}) _⦋0⦌ := SSet.stdSimplex.obj₀Equiv.symm 1
  have hconst : SSet.const (X := ⊥_ SSet.{u}) z₀ = SSet.const z₁ :=
    initialIsInitial.hom_ext _ _
  have hval := ConcreteCategory.congr_hom (congr_app hconst (op ⦋0⦌)) y
  have h01 : (0 : Fin 2) = 1 := by
    have hval' := congrArg SSet.stdSimplex.obj₀Equiv hval
    change (0 : Fin 2) = 1 at hval'
    exact hval'
  exact (Fin.zero_ne_one h01).elim

theorem trivialKanFibration_kanFibration
    {X Y : SSet.{u}} (f : X ⟶ Y)
    (hf : Formalization.Books.Simplicial.Unit30.TrivialKanFibration f) :
    KanFibration f := by
  change HomotopicalAlgebra.Fibration f
  rw [SSet.modelCategoryQuillen.fibration_iff]
  intro A B i hi
  simp only [SSet.modelCategoryQuillen.J,
    CategoryTheory.MorphismProperty.iSup_iff] at hi
  obtain ⟨n, ⟨k⟩⟩ := hi
  refine ⟨fun {a} {b} sq => ?_⟩
  obtain ⟨l, hl, hr⟩ :=
    Formalization.Books.Simplicial.Unit30.trivialKanFibration_lift f hf
      (SSet.horn (n + 1) k).ι
      (by
        intro d
        exact Subtype.val_injective) a b sq.w
  exact ⟨⟨{ l := l, fac_left := hl, fac_right := hr }⟩⟩

/-! ## Closure properties -/

/-- Kan fibrations are preserved by base change. -/
theorem kanFibration_baseChange
    {X Y Y' : SSet.{u}} (f : X ⟶ Y) (hf : KanFibration f)
    (g : Y' ⟶ Y) :
    KanFibration (pullback.fst f g) := by
  sorry

/-- The composite of Kan fibrations is a Kan fibration. -/
theorem kanFibration_comp
    {X Y Z : SSet.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (hf : KanFibration f) (hg : KanFibration g) :
    KanFibration (f ≫ g) := by
  sorry

/-- The projection from the inverse limit of a sequence of Kan fibrations to
its zeroth term is a Kan fibration. -/
theorem kanFibration_limit
    (U : ℕᵒᵖ ⥤ SSet.{u})
    (hU : ∀ n : ℕ,
      KanFibration
        (Formalization.Books.Simplicial.Unit30.inverseSequenceTransition U n)) :
    KanFibration (limit.π U (op 0)) := by
  sorry

/-- Products of Kan fibrations are Kan fibrations. -/
theorem kanFibration_product
    {T : Type w} {X Y : T → SSet.{u}}
    (hX : HasLimit (Discrete.functor X))
    (hY : HasLimit (Discrete.functor Y))
    (f : ∀ t, X t ⟶ Y t)
    (hf : ∀ t, KanFibration (f t)) :
    KanFibration
      (Formalization.Books.Simplicial.Unit26.indexedProductMap hX hY f) := by
  sorry

/-! ## Simplicial groups -/

/-- The underlying simplicial set of a simplicial group. -/
def underlyingSimplicialGroup
    (X : SimplicialObject CommGrpCat.{u}) : SSet.{u} :=
  ((SimplicialObject.whiskering CommGrpCat (Type u)).obj
    (CategoryTheory.forget CommGrpCat)).obj X

/-- The underlying simplicial map of a map of simplicial groups. -/
def underlyingSimplicialGroupMap
    {X Y : SimplicialObject CommGrpCat.{u}} (f : X ⟶ Y) :
    underlyingSimplicialGroup X ⟶ underlyingSimplicialGroup Y :=
  ((SimplicialObject.whiskering CommGrpCat (Type u)).obj
    (CategoryTheory.forget CommGrpCat)).map f

/-- Every simplicial group is a Kan complex. -/
theorem simplicialGroup_kanComplex
    (X : SimplicialObject CommGrpCat.{u}) :
    KanComplex (underlyingSimplicialGroup X) := by
  sorry

/-! ## Simplicial abelian groups -/

/-- The underlying simplicial set of a simplicial abelian group. -/
def underlyingSimplicialAbelianGroup
    (X : SimplicialObject AddCommGrpCat.{u}) : SSet.{u} :=
  ((SimplicialObject.whiskering AddCommGrpCat (Type u)).obj
    (CategoryTheory.forget AddCommGrpCat)).obj X

/-- The underlying simplicial map of a map of simplicial abelian groups. -/
def underlyingSimplicialAbelianGroupMap
    {X Y : SimplicialObject AddCommGrpCat.{u}} (f : X ⟶ Y) :
    underlyingSimplicialAbelianGroup X ⟶ underlyingSimplicialAbelianGroup Y :=
  ((SimplicialObject.whiskering AddCommGrpCat (Type u)).obj
    (CategoryTheory.forget AddCommGrpCat)).map f

/-- A termwise-surjective map of simplicial abelian groups is a Kan
fibration on underlying simplicial sets. -/
theorem termwiseSurjective_simplicialAbelianGroup_kanFibration
    {X Y : SimplicialObject AddCommGrpCat.{u}} (f : X ⟶ Y)
    (hf : ∀ n : ℕ,
      Function.Surjective (f.app (op (SimplexCategory.mk n)))) :
    KanFibration (underlyingSimplicialAbelianGroupMap f) := by
  sorry

/-- A termwise-surjective quasi-isomorphism of simplicial abelian groups is a
trivial Kan fibration. -/
theorem termwiseSurjective_quasiIso_simplicialAbelianGroup_trivialKanFibration
    {X Y : SimplicialObject AddCommGrpCat.{u}} (f : X ⟶ Y)
    (hf : ∀ n : ℕ,
      Function.Surjective (f.app (op (SimplexCategory.mk n))))
    (hquasi : QuasiIso
      (Formalization.Books.Simplicial.Unit23.associatedChainComplexMap f)) :
    Formalization.Books.Simplicial.Unit30.TrivialKanFibration
      (underlyingSimplicialAbelianGroupMap f) := by
  sorry

/-- A homotopy equivalence of the underlying simplicial sets of simplicial
abelian groups induces a quasi-isomorphism on the associated chain complexes. -/
theorem homotopyEquivalence_simplicialAbelianGroup_quasiIso
    {X Y : SimplicialObject AddCommGrpCat.{u}} (f : X ⟶ Y)
    (hf : Formalization.Books.Simplicial.Unit26.IsHomotopyEquivalence
      (underlyingSimplicialAbelianGroupMap f)) :
    QuasiIso
      (Formalization.Books.Simplicial.Unit23.associatedChainComplexMap f) := by
  sorry

end Formalization.Books.Simplicial.Unit31
