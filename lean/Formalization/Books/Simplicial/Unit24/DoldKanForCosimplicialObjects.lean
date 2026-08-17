import Formalization.Books.Simplicial.Unit24.DoldKan

/-!
# Simplicial Methods, Chapter 24: Dold--Kan for cosimplicial objects

The cochain complexes in this file use Mathlib's `CochainComplex C ℕ`, the
nonnegative-index model of the source's `CoCh_{≥ 0}(C)`.  The normalized terms
are defined by the source's cokernels of the first cofaces, and all maps use
the canonical cokernel and finite-coproduct APIs.
-/

noncomputable section

namespace Formalization.Books.Simplicial.Unit24

open CategoryTheory
open CategoryTheory.Limits
open Formalization.Books.Simplicial.Unit22
open Opposite
open HomologicalComplex
open scoped _root_.Simplicial
open scoped ZeroObject

universe v u

attribute [local instance] CategoryTheory.Abelian.hasFiniteBiproducts

/-! ## The two formal duality identifications -/

theorem cosimplicial_as_opposite_simplicial
    {C : Type u} [Category.{v} C] [Abelian C] :
    Nonempty (CosimplicialObject C ≌ (SimplicialObject Cᵒᵖ)ᵒᵖ) := by
  sorry

theorem cochain_as_opposite_chain
    {C : Type u} [Category.{v} C] [Abelian C] :
    Nonempty (CochainComplex C ℕ ≌ (ChainComplex Cᵒᵖ ℕ)ᵒᵖ) := by
  sorry

theorem dual_doldKan_induced_equivalence
    {C : Type u} [Category.{v} C] [Abelian C] :
    Nonempty (CosimplicialObject C ≌ CochainComplex C ℕ) := by
  sorry

/-! ## The associated cochain complex `s(U)` -/

/-- The alternating coface differential in degree `n`. -/
def cosimplicialAssociatedBoundary
    {C : Type u} [Category.{v} C] [Abelian C]
    (U : CosimplicialObject C) (n : ℕ) :
    U.obj ⦋n⦌ ⟶ U.obj ⦋n + 1⦌ :=
  ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) • U.δ i

theorem cosimplicialAssociatedBoundary_comp
    {C : Type u} [Category.{v} C] [Abelian C]
    (U : CosimplicialObject C) (n : ℕ) :
    cosimplicialAssociatedBoundary U n ≫
        cosimplicialAssociatedBoundary U (n + 1) = 0 := by
  sorry

/-- The nonnegative associated cochain complex `s(U)`. -/
noncomputable def cosimplicialAssociatedCochainComplex
    {C : Type u} [Category.{v} C] [Abelian C]
    (U : CosimplicialObject C) : CochainComplex C ℕ :=
  CochainComplex.of
    (fun n => U.obj ⦋n⦌)
    (cosimplicialAssociatedBoundary U)
    (cosimplicialAssociatedBoundary_comp U)

@[simp]
theorem cosimplicialAssociatedCochainComplex_X
    {C : Type u} [Category.{v} C] [Abelian C]
    (U : CosimplicialObject C) (n : ℕ) :
    (cosimplicialAssociatedCochainComplex U).X n = U.obj ⦋n⦌ :=
  rfl

@[simp]
theorem cosimplicialAssociatedCochainComplex_d
    {C : Type u} [Category.{v} C] [Abelian C]
    (U : CosimplicialObject C) (n : ℕ) :
    (cosimplicialAssociatedCochainComplex U).d n (n + 1) =
      cosimplicialAssociatedBoundary U n := by
  simp [cosimplicialAssociatedCochainComplex]

theorem cosimplicialAssociatedBoundary_naturality
    {C : Type u} [Category.{v} C] [Abelian C]
    {U V : CosimplicialObject C} (f : U ⟶ V) (n : ℕ) :
    cosimplicialAssociatedBoundary U n ≫ f.app ⦋n + 1⦌ =
      f.app ⦋n⦌ ≫ cosimplicialAssociatedBoundary V n := by
  sorry

theorem cosimplicialAssociatedCochainMap_comm
    {C : Type u} [Category.{v} C] [Abelian C]
    {U V : CosimplicialObject C} (f : U ⟶ V) :
    ∀ i j : ℕ, (ComplexShape.up ℕ).Rel i j →
      f.app ⦋i⦌ ≫ (cosimplicialAssociatedCochainComplex V).d i j =
        (cosimplicialAssociatedCochainComplex U).d i j ≫ f.app ⦋j⦌ := by
  sorry

/-- The cochain map induced by a morphism of cosimplicial objects. -/
def cosimplicialAssociatedCochainMap
    {C : Type u} [Category.{v} C] [Abelian C]
    {U V : CosimplicialObject C} (f : U ⟶ V) :
    cosimplicialAssociatedCochainComplex U ⟶
      cosimplicialAssociatedCochainComplex V :=
  { f := fun n => f.app ⦋n⦌
    comm' := cosimplicialAssociatedCochainMap_comm f }

@[simp]
theorem cosimplicialAssociatedCochainMap_f
    {C : Type u} [Category.{v} C] [Abelian C]
    {U V : CosimplicialObject C} (f : U ⟶ V) (n : ℕ) :
    (cosimplicialAssociatedCochainMap f).f n = f.app ⦋n⦌ :=
  rfl

/-- The functor `s : CoSimp(C) ⥤ CoCh_{≥0}(C)`. -/
def cosimplicialAssociatedCochainFunctor
    (C : Type u) [Category.{v} C] [Abelian C] :
    CosimplicialObject C ⥤ CochainComplex C ℕ where
  obj U := cosimplicialAssociatedCochainComplex U
  map f := cosimplicialAssociatedCochainMap f
  map_id U := by
    ext n
    rfl
  map_comp f g := by
    ext n
    rfl

theorem cosimplicialAssociatedCochainFunctor_exact
    {C : Type u} [Category.{v} C] [Abelian C] :
    exactFunctor (CosimplicialObject C) (CochainComplex C ℕ)
      (cosimplicialAssociatedCochainFunctor C) := by
  sorry

/-! ## The normalized cochain complex `Q(U)` -/

/-- The direct sum of the first `n` coface maps into degree `n`. -/
noncomputable def normalizedCochainIncoming
    {C : Type u} [Category.{v} C] [Abelian C]
    (U : CosimplicialObject C) (n : ℕ) :
    (∐ fun _ : Fin n => U.obj ⦋n - 1⦌) ⟶ U.obj ⦋n⦌ :=
  match n with
  | 0 => Sigma.desc (fun i => Fin.elim0 i)
  | n + 1 => Sigma.desc (fun i : Fin (n + 1) => U.δ (Fin.castSucc i))

/-- The normalized term, with degree zero written exactly as `U₀`. -/
noncomputable def normalizedCochainObject
    {C : Type u} [Category.{v} C] [Abelian C]
    (U : CosimplicialObject C) (n : ℕ) : C :=
  match n with
  | 0 => U.obj ⦋0⦌
  | n + 1 => cokernel (normalizedCochainIncoming U (n + 1))

@[simp]
theorem normalizedCochainObject_zero
    {C : Type u} [Category.{v} C] [Abelian C]
    (U : CosimplicialObject C) :
    normalizedCochainObject U 0 = U.obj ⦋0⦌ :=
  rfl

@[simp]
theorem normalizedCochainObject_succ
    {C : Type u} [Category.{v} C] [Abelian C]
    (U : CosimplicialObject C) (n : ℕ) :
    normalizedCochainObject U (n + 1) =
      cokernel (normalizedCochainIncoming U (n + 1)) :=
  rfl

/-- The canonical projection `U_n ⟶ Q(U)^n`. -/
noncomputable def normalizedCochainProjection
    {C : Type u} [Category.{v} C] [Abelian C]
    (U : CosimplicialObject C) (n : ℕ) :
    U.obj ⦋n⦌ ⟶ normalizedCochainObject U n :=
  match n with
  | 0 => 𝟙 _
  | n + 1 => cokernel.π (normalizedCochainIncoming U (n + 1))

@[simp]
theorem normalizedCochainProjection_zero
    {C : Type u} [Category.{v} C] [Abelian C]
    (U : CosimplicialObject C) :
    normalizedCochainProjection U 0 = 𝟙 (U.obj ⦋0⦌) :=
  rfl

@[simp]
theorem normalizedCochainProjection_succ
    {C : Type u} [Category.{v} C] [Abelian C]
    (U : CosimplicialObject C) (n : ℕ) :
    normalizedCochainProjection U (n + 1) =
      cokernel.π (normalizedCochainIncoming U (n + 1)) :=
  rfl

/-- The signed last-coface map before passing to the next cokernel. -/
noncomputable def normalizedCochainRawBoundary
    {C : Type u} [Category.{v} C] [Abelian C]
    (U : CosimplicialObject C) (n : ℕ) :
    U.obj ⦋n⦌ ⟶ normalizedCochainObject U (n + 1) :=
  ((-1 : ℤ) ^ (n + 1) • U.δ (Fin.last (n + 1))) ≫
    normalizedCochainProjection U (n + 1)

/-- The reader's descent condition for the signed last coface. -/
theorem normalizedCochainRawBoundary_condition
    {C : Type u} [Category.{v} C] [Abelian C]
    (U : CosimplicialObject C) (n : ℕ) :
    normalizedCochainIncoming U (n + 1) ≫
        normalizedCochainRawBoundary U (n + 1) = 0 := by
  sorry

/-- The differential on the normalized cochain terms. -/
noncomputable def normalizedCochainBoundary
    {C : Type u} [Category.{v} C] [Abelian C]
    (U : CosimplicialObject C) (n : ℕ) :
    normalizedCochainObject U n ⟶ normalizedCochainObject U (n + 1) :=
  match n with
  | 0 => normalizedCochainRawBoundary U 0
  | n + 1 =>
      cokernel.desc (normalizedCochainIncoming U (n + 1))
        (normalizedCochainRawBoundary U (n + 1))
        (normalizedCochainRawBoundary_condition U n)

theorem normalizedCochainBoundary_projection
    {C : Type u} [Category.{v} C] [Abelian C]
    (U : CosimplicialObject C) (n : ℕ) :
    normalizedCochainProjection U n ≫ normalizedCochainBoundary U n =
      normalizedCochainRawBoundary U n := by
  cases n with
  | zero =>
      exact Category.id_comp _
  | succ n =>
      simp [normalizedCochainProjection, normalizedCochainBoundary,
        normalizedCochainRawBoundary]

theorem normalizedCochainBoundary_comp
    {C : Type u} [Category.{v} C] [Abelian C]
    (U : CosimplicialObject C) (n : ℕ) :
    normalizedCochainBoundary U n ≫ normalizedCochainBoundary U (n + 1) = 0 := by
  sorry

/-- The normalized cochain complex associated to `U`. -/
noncomputable def normalizedCochainComplex
    {C : Type u} [Category.{v} C] [Abelian C]
    (U : CosimplicialObject C) : CochainComplex C ℕ :=
  CochainComplex.of
    (normalizedCochainObject U)
    (normalizedCochainBoundary U)
    (normalizedCochainBoundary_comp U)

@[simp]
theorem normalizedCochainComplex_X
    {C : Type u} [Category.{v} C] [Abelian C]
    (U : CosimplicialObject C) (n : ℕ) :
    (normalizedCochainComplex U).X n = normalizedCochainObject U n :=
  rfl

@[simp]
theorem normalizedCochainComplex_d
    {C : Type u} [Category.{v} C] [Abelian C]
    (U : CosimplicialObject C) (n : ℕ) :
    (normalizedCochainComplex U).d n (n + 1) = normalizedCochainBoundary U n := by
  exact CochainComplex.of_d (normalizedCochainObject U)
    (normalizedCochainBoundary U) (n)

theorem normalizedCochainComparison_comm
    {C : Type u} [Category.{v} C] [Abelian C]
    (U : CosimplicialObject C) :
    ∀ i j : ℕ, (ComplexShape.up ℕ).Rel i j →
      normalizedCochainProjection U i ≫ (normalizedCochainComplex U).d i j =
        (cosimplicialAssociatedCochainComplex U).d i j ≫
          normalizedCochainProjection U j := by
  sorry

/-- The canonical comparison `s(U) ⟶ Q(U)`. -/
def normalizedCochainComparison
    {C : Type u} [Category.{v} C] [Abelian C]
    (U : CosimplicialObject C) :
    cosimplicialAssociatedCochainComplex U ⟶ normalizedCochainComplex U :=
  { f := fun n => normalizedCochainProjection U n
    comm' := normalizedCochainComparison_comm U }

@[simp]
theorem normalizedCochainComparison_f
    {C : Type u} [Category.{v} C] [Abelian C]
    (U : CosimplicialObject C) (n : ℕ) :
    (normalizedCochainComparison U).f n = normalizedCochainProjection U n :=
  rfl

/-! ## Functoriality of the normalized construction -/

theorem normalizedCochainMap_condition
    {C : Type u} [Category.{v} C] [Abelian C]
    {U V : CosimplicialObject C} (f : U ⟶ V) (n : ℕ) :
    normalizedCochainIncoming U (n + 1) ≫ f.app ⦋n + 1⦌ ≫
        normalizedCochainProjection V (n + 1) = 0 := by
  sorry

noncomputable def normalizedCochainMapComponent
    {C : Type u} [Category.{v} C] [Abelian C]
    {U V : CosimplicialObject C} (f : U ⟶ V) (n : ℕ) :
    normalizedCochainObject U n ⟶ normalizedCochainObject V n :=
  match n with
  | 0 => f.app ⦋0⦌
  | n + 1 =>
      cokernel.desc (normalizedCochainIncoming U (n + 1))
        (f.app ⦋n + 1⦌ ≫ normalizedCochainProjection V (n + 1))
        (normalizedCochainMap_condition f n)

theorem normalizedCochainMap_comm
    {C : Type u} [Category.{v} C] [Abelian C]
    {U V : CosimplicialObject C} (f : U ⟶ V) :
    ∀ i j : ℕ, (ComplexShape.up ℕ).Rel i j →
      normalizedCochainMapComponent f i ≫
          (normalizedCochainComplex V).d i j =
        (normalizedCochainComplex U).d i j ≫
          normalizedCochainMapComponent f j := by
  sorry

noncomputable def normalizedCochainMap
    {C : Type u} [Category.{v} C] [Abelian C]
    {U V : CosimplicialObject C} (f : U ⟶ V) :
    normalizedCochainComplex U ⟶ normalizedCochainComplex V :=
  { f := fun n => normalizedCochainMapComponent f n
    comm' := normalizedCochainMap_comm f }

theorem normalizedCochainMap_id
    {C : Type u} [Category.{v} C] [Abelian C]
    (U : CosimplicialObject C) :
    normalizedCochainMap (𝟙 U) = 𝟙 (normalizedCochainComplex U) := by
  sorry

theorem normalizedCochainMap_comp
    {C : Type u} [Category.{v} C] [Abelian C]
    {U V W : CosimplicialObject C} (f : U ⟶ V) (g : V ⟶ W) :
    normalizedCochainMap (f ≫ g) =
      normalizedCochainMap f ≫ normalizedCochainMap g := by
  sorry

/-- The normalized cochain functor `Q`. -/
def normalizedCochainFunctor
    (C : Type u) [Category.{v} C] [Abelian C] :
    CosimplicialObject C ⥤ CochainComplex C ℕ where
  obj U := normalizedCochainComplex U
  map f := normalizedCochainMap f
  map_id U := normalizedCochainMap_id U
  map_comp f g := normalizedCochainMap_comp f g

theorem normalizedCochainFunctor_exact
    {C : Type u} [Category.{v} C] [Abelian C] :
    exactFunctor (CosimplicialObject C) (CochainComplex C ℕ)
      (normalizedCochainFunctor C) := by
  sorry

/-! ## The six assertions of the dual Dold--Kan lemma -/

noncomputable def cochainFunctorBiproduct
    {C : Type u} [Category.{v} C] [Abelian C]
    (F G : CosimplicialObject C ⥤ CochainComplex C ℕ) :
    CosimplicialObject C ⥤ CochainComplex C ℕ where
  obj U := F.obj U ⊞ G.obj U
  map f := biprod.map (F.map f) (G.map f)
  map_id U := by
    apply biprod.hom_ext <;> simp
  map_comp f g := by
    apply biprod.hom_ext' <;> simp

/-- A functorial witness for the source's cochain decomposition `s(U)=D(U)⊕Q(U)`. -/
structure NormalizedCochainDecomposition
    (C : Type u) [Category.{v} C] [Abelian C] where
  degenerate : CosimplicialObject C ⥤ CochainComplex C ℕ
  decomposition : Nonempty (cosimplicialAssociatedCochainFunctor C ≅
    cochainFunctorBiproduct degenerate (normalizedCochainFunctor C))

theorem normalizedCochain_decomposition_exists
    {C : Type u} [Category.{v} C] [Abelian C] :
    Nonempty (NormalizedCochainDecomposition C) := by
  sorry

theorem normalizedCochain_comparison_is_quasiIso
    {C : Type u} [Category.{v} C] [Abelian C]
    (U : CosimplicialObject C) :
    QuasiIso (normalizedCochainComparison U) := by
  sorry

theorem normalizedCochainFunctor_is_equivalence
    {C : Type u} [Category.{v} C] [Abelian C] :
    (normalizedCochainFunctor C).IsEquivalence := by
  sorry

/-- A categorical equivalence realizing the cosimplicial Dold--Kan theorem. -/
noncomputable def dualDoldKanEquivalence
    (C : Type u) [Category.{v} C] [Abelian C] :
    CosimplicialObject C ≌ CochainComplex C ℕ := by
  letI : (normalizedCochainFunctor C).IsEquivalence :=
    normalizedCochainFunctor_is_equivalence
  exact (normalizedCochainFunctor C).asEquivalence

end Formalization.Books.Simplicial.Unit24
