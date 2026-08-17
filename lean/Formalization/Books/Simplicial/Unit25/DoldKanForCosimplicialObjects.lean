import Formalization.Books.Simplicial.Unit24.DoldKanForCosimplicialObjects

/-!
# Simplicial Methods, Chapter 25: Dold--Kan for cosimplicial objects

This chapter-facing namespace reuses the canonical cosimplicial Dold--Kan
construction from Chapter 24.  The aliases below retain the source order and
provide the complete Chapter 25 interface without introducing a second set of
complexes, comparison maps, or equivalences.
-/

noncomputable section

namespace Formalization.Books.Simplicial.Unit25

open CategoryTheory
open CategoryTheory.Limits
open Formalization.Books.Simplicial.Unit22
open Formalization.Books.Simplicial.Unit24
open Opposite
open HomologicalComplex
open scoped _root_.Simplicial
open scoped ZeroObject

universe v u

attribute [local instance] CategoryTheory.Abelian.hasFiniteBiproducts

/-! ## The two formal duality identifications -/

theorem cosimplicial_as_opposite_simplicial
    {C : Type u} [Category.{v} C] [Abelian C] :
    Nonempty (CosimplicialObject C ≌ (SimplicialObject Cᵒᵖ)ᵒᵖ) :=
  Formalization.Books.Simplicial.Unit24.cosimplicial_as_opposite_simplicial

theorem cochain_as_opposite_chain
    {C : Type u} [Category.{v} C] [Abelian C] :
    Nonempty (CochainComplex C ℕ ≌ (ChainComplex Cᵒᵖ ℕ)ᵒᵖ) :=
  Formalization.Books.Simplicial.Unit24.cochain_as_opposite_chain

theorem dual_doldKan_induced_equivalence
    {C : Type u} [Category.{v} C] [Abelian C] :
    Nonempty (CosimplicialObject C ≌ CochainComplex C ℕ) :=
  Formalization.Books.Simplicial.Unit24.dual_doldKan_induced_equivalence

/-! ## The associated cochain complex `s(U)` -/

/-- The alternating coface differential in degree `n`. -/
abbrev cosimplicialAssociatedBoundary
    {C : Type u} [Category.{v} C] [Abelian C]
    (U : CosimplicialObject C) (n : ℕ) :
    U.obj ⦋n⦌ ⟶ U.obj ⦋n + 1⦌ :=
  Formalization.Books.Simplicial.Unit24.cosimplicialAssociatedBoundary U n

theorem cosimplicialAssociatedBoundary_comp
    {C : Type u} [Category.{v} C] [Abelian C]
    (U : CosimplicialObject C) (n : ℕ) :
    cosimplicialAssociatedBoundary U n ≫
        cosimplicialAssociatedBoundary U (n + 1) = 0 :=
  Formalization.Books.Simplicial.Unit24.cosimplicialAssociatedBoundary_comp U n

/-- The nonnegative associated cochain complex `s(U)`. -/
noncomputable abbrev cosimplicialAssociatedCochainComplex
    {C : Type u} [Category.{v} C] [Abelian C]
    (U : CosimplicialObject C) : CochainComplex C ℕ :=
  Formalization.Books.Simplicial.Unit24.cosimplicialAssociatedCochainComplex U

@[simp]
theorem cosimplicialAssociatedCochainComplex_X
    {C : Type u} [Category.{v} C] [Abelian C]
    (U : CosimplicialObject C) (n : ℕ) :
    (cosimplicialAssociatedCochainComplex U).X n = U.obj ⦋n⦌ :=
  Formalization.Books.Simplicial.Unit24.cosimplicialAssociatedCochainComplex_X U n

@[simp]
theorem cosimplicialAssociatedCochainComplex_d
    {C : Type u} [Category.{v} C] [Abelian C]
    (U : CosimplicialObject C) (n : ℕ) :
    (cosimplicialAssociatedCochainComplex U).d n (n + 1) =
      cosimplicialAssociatedBoundary U n :=
  Formalization.Books.Simplicial.Unit24.cosimplicialAssociatedCochainComplex_d U n

theorem cosimplicialAssociatedBoundary_naturality
    {C : Type u} [Category.{v} C] [Abelian C]
    {U V : CosimplicialObject C} (f : U ⟶ V) (n : ℕ) :
    cosimplicialAssociatedBoundary U n ≫ f.app ⦋n + 1⦌ =
      f.app ⦋n⦌ ≫ cosimplicialAssociatedBoundary V n :=
  Formalization.Books.Simplicial.Unit24.cosimplicialAssociatedBoundary_naturality f n

theorem cosimplicialAssociatedCochainMap_comm
    {C : Type u} [Category.{v} C] [Abelian C]
    {U V : CosimplicialObject C} (f : U ⟶ V) :
    ∀ i j : ℕ, (ComplexShape.up ℕ).Rel i j →
      f.app ⦋i⦌ ≫ (cosimplicialAssociatedCochainComplex V).d i j =
        (cosimplicialAssociatedCochainComplex U).d i j ≫ f.app ⦋j⦌ :=
  Formalization.Books.Simplicial.Unit24.cosimplicialAssociatedCochainMap_comm f

/-- The cochain map induced by a morphism of cosimplicial objects. -/
abbrev cosimplicialAssociatedCochainMap
    {C : Type u} [Category.{v} C] [Abelian C]
    {U V : CosimplicialObject C} (f : U ⟶ V) :
    cosimplicialAssociatedCochainComplex U ⟶
      cosimplicialAssociatedCochainComplex V :=
  Formalization.Books.Simplicial.Unit24.cosimplicialAssociatedCochainMap f

@[simp]
theorem cosimplicialAssociatedCochainMap_f
    {C : Type u} [Category.{v} C] [Abelian C]
    {U V : CosimplicialObject C} (f : U ⟶ V) (n : ℕ) :
    (cosimplicialAssociatedCochainMap f).f n = f.app ⦋n⦌ :=
  Formalization.Books.Simplicial.Unit24.cosimplicialAssociatedCochainMap_f f n

/- The functor `s : CoSimp(C) ⥤ CoCh_{≥0}(C)`. -/
abbrev cosimplicialAssociatedCochainFunctor
    (C : Type u) [Category.{v} C] [Abelian C] :
    CosimplicialObject C ⥤ CochainComplex C ℕ :=
  Formalization.Books.Simplicial.Unit24.cosimplicialAssociatedCochainFunctor C

theorem cosimplicialAssociatedCochainFunctor_exact
    {C : Type u} [Category.{v} C] [Abelian C] :
    exactFunctor (CosimplicialObject C) (CochainComplex C ℕ)
      (cosimplicialAssociatedCochainFunctor C) :=
  Formalization.Books.Simplicial.Unit24.cosimplicialAssociatedCochainFunctor_exact

/-! ## The normalized cochain complex `Q(U)` -/

/-- The direct sum of the first `n` coface maps into degree `n`. -/
noncomputable abbrev normalizedCochainIncoming
    {C : Type u} [Category.{v} C] [Abelian C]
    (U : CosimplicialObject C) (n : ℕ) :
    (∐ fun _ : Fin n => U.obj ⦋n - 1⦌) ⟶ U.obj ⦋n⦌ :=
  Formalization.Books.Simplicial.Unit24.normalizedCochainIncoming U n

/-- The normalized term, with degree zero written exactly as `U₀`. -/
noncomputable abbrev normalizedCochainObject
    {C : Type u} [Category.{v} C] [Abelian C]
    (U : CosimplicialObject C) (n : ℕ) : C :=
  Formalization.Books.Simplicial.Unit24.normalizedCochainObject U n

@[simp]
theorem normalizedCochainObject_zero
    {C : Type u} [Category.{v} C] [Abelian C]
    (U : CosimplicialObject C) :
    normalizedCochainObject U 0 = U.obj ⦋0⦌ :=
  Formalization.Books.Simplicial.Unit24.normalizedCochainObject_zero U

@[simp]
theorem normalizedCochainObject_succ
    {C : Type u} [Category.{v} C] [Abelian C]
    (U : CosimplicialObject C) (n : ℕ) :
    normalizedCochainObject U (n + 1) =
      cokernel (normalizedCochainIncoming U (n + 1)) :=
  Formalization.Books.Simplicial.Unit24.normalizedCochainObject_succ U n

/-- The canonical projection `U_n ⟶ Q(U)^n`. -/
noncomputable abbrev normalizedCochainProjection
    {C : Type u} [Category.{v} C] [Abelian C]
    (U : CosimplicialObject C) (n : ℕ) :
    U.obj ⦋n⦌ ⟶ normalizedCochainObject U n :=
  Formalization.Books.Simplicial.Unit24.normalizedCochainProjection U n

@[simp]
theorem normalizedCochainProjection_zero
    {C : Type u} [Category.{v} C] [Abelian C]
    (U : CosimplicialObject C) :
    normalizedCochainProjection U 0 = 𝟙 (U.obj ⦋0⦌) :=
  Formalization.Books.Simplicial.Unit24.normalizedCochainProjection_zero U

@[simp]
theorem normalizedCochainProjection_succ
    {C : Type u} [Category.{v} C] [Abelian C]
    (U : CosimplicialObject C) (n : ℕ) :
    normalizedCochainProjection U (n + 1) =
      cokernel.π (normalizedCochainIncoming U (n + 1)) :=
  Formalization.Books.Simplicial.Unit24.normalizedCochainProjection_succ U n

/-- The signed last-coface map before passing to the next cokernel. -/
noncomputable abbrev normalizedCochainRawBoundary
    {C : Type u} [Category.{v} C] [Abelian C]
    (U : CosimplicialObject C) (n : ℕ) :
    U.obj ⦋n⦌ ⟶ normalizedCochainObject U (n + 1) :=
  Formalization.Books.Simplicial.Unit24.normalizedCochainRawBoundary U n

/-- The descent condition needed to induce the signed last coface. -/
theorem normalizedCochainRawBoundary_condition
    {C : Type u} [Category.{v} C] [Abelian C]
    (U : CosimplicialObject C) (n : ℕ) :
    normalizedCochainIncoming U (n + 1) ≫
        normalizedCochainRawBoundary U (n + 1) = 0 :=
  Formalization.Books.Simplicial.Unit24.normalizedCochainRawBoundary_condition U n

/-- The differential on the normalized cochain terms. -/
noncomputable abbrev normalizedCochainBoundary
    {C : Type u} [Category.{v} C] [Abelian C]
    (U : CosimplicialObject C) (n : ℕ) :
    normalizedCochainObject U n ⟶ normalizedCochainObject U (n + 1) :=
  Formalization.Books.Simplicial.Unit24.normalizedCochainBoundary U n

theorem normalizedCochainBoundary_projection
    {C : Type u} [Category.{v} C] [Abelian C]
    (U : CosimplicialObject C) (n : ℕ) :
    normalizedCochainProjection U n ≫ normalizedCochainBoundary U n =
      normalizedCochainRawBoundary U n :=
  Formalization.Books.Simplicial.Unit24.normalizedCochainBoundary_projection U n

theorem normalizedCochainBoundary_comp
    {C : Type u} [Category.{v} C] [Abelian C]
    (U : CosimplicialObject C) (n : ℕ) :
    normalizedCochainBoundary U n ≫ normalizedCochainBoundary U (n + 1) = 0 :=
  Formalization.Books.Simplicial.Unit24.normalizedCochainBoundary_comp U n

/-- The normalized cochain complex associated to `U`. -/
noncomputable abbrev normalizedCochainComplex
    {C : Type u} [Category.{v} C] [Abelian C]
    (U : CosimplicialObject C) : CochainComplex C ℕ :=
  Formalization.Books.Simplicial.Unit24.normalizedCochainComplex U

@[simp]
theorem normalizedCochainComplex_X
    {C : Type u} [Category.{v} C] [Abelian C]
    (U : CosimplicialObject C) (n : ℕ) :
    (normalizedCochainComplex U).X n = normalizedCochainObject U n :=
  Formalization.Books.Simplicial.Unit24.normalizedCochainComplex_X U n

@[simp]
theorem normalizedCochainComplex_d
    {C : Type u} [Category.{v} C] [Abelian C]
    (U : CosimplicialObject C) (n : ℕ) :
    (normalizedCochainComplex U).d n (n + 1) = normalizedCochainBoundary U n :=
  Formalization.Books.Simplicial.Unit24.normalizedCochainComplex_d U n

theorem normalizedCochainComparison_comm
    {C : Type u} [Category.{v} C] [Abelian C]
    (U : CosimplicialObject C) :
    ∀ i j : ℕ, (ComplexShape.up ℕ).Rel i j →
      normalizedCochainProjection U i ≫ (normalizedCochainComplex U).d i j =
        (cosimplicialAssociatedCochainComplex U).d i j ≫
          normalizedCochainProjection U j :=
  Formalization.Books.Simplicial.Unit24.normalizedCochainComparison_comm U

/-- The canonical comparison `s(U) ⟶ Q(U)`. -/
abbrev normalizedCochainComparison
    {C : Type u} [Category.{v} C] [Abelian C]
    (U : CosimplicialObject C) :
    cosimplicialAssociatedCochainComplex U ⟶ normalizedCochainComplex U :=
  Formalization.Books.Simplicial.Unit24.normalizedCochainComparison U

@[simp]
theorem normalizedCochainComparison_f
    {C : Type u} [Category.{v} C] [Abelian C]
    (U : CosimplicialObject C) (n : ℕ) :
    (normalizedCochainComparison U).f n = normalizedCochainProjection U n :=
  Formalization.Books.Simplicial.Unit24.normalizedCochainComparison_f U n

/-! ## Functoriality of the normalized construction -/

theorem normalizedCochainMap_condition
    {C : Type u} [Category.{v} C] [Abelian C]
    {U V : CosimplicialObject C} (f : U ⟶ V) (n : ℕ) :
    normalizedCochainIncoming U (n + 1) ≫ f.app ⦋n + 1⦌ ≫
        normalizedCochainProjection V (n + 1) = 0 :=
  Formalization.Books.Simplicial.Unit24.normalizedCochainMap_condition f n

noncomputable abbrev normalizedCochainMapComponent
    {C : Type u} [Category.{v} C] [Abelian C]
    {U V : CosimplicialObject C} (f : U ⟶ V) (n : ℕ) :
    normalizedCochainObject U n ⟶ normalizedCochainObject V n :=
  Formalization.Books.Simplicial.Unit24.normalizedCochainMapComponent f n

theorem normalizedCochainMap_comm
    {C : Type u} [Category.{v} C] [Abelian C]
    {U V : CosimplicialObject C} (f : U ⟶ V) :
    ∀ i j : ℕ, (ComplexShape.up ℕ).Rel i j →
      normalizedCochainMapComponent f i ≫
          (normalizedCochainComplex V).d i j =
        (normalizedCochainComplex U).d i j ≫
          normalizedCochainMapComponent f j :=
  Formalization.Books.Simplicial.Unit24.normalizedCochainMap_comm f

noncomputable abbrev normalizedCochainMap
    {C : Type u} [Category.{v} C] [Abelian C]
    {U V : CosimplicialObject C} (f : U ⟶ V) :
    normalizedCochainComplex U ⟶ normalizedCochainComplex V :=
  Formalization.Books.Simplicial.Unit24.normalizedCochainMap f

theorem normalizedCochainMap_id
    {C : Type u} [Category.{v} C] [Abelian C]
    (U : CosimplicialObject C) :
    normalizedCochainMap (𝟙 U) = 𝟙 (normalizedCochainComplex U) :=
  Formalization.Books.Simplicial.Unit24.normalizedCochainMap_id U

theorem normalizedCochainMap_comp
    {C : Type u} [Category.{v} C] [Abelian C]
    {U V W : CosimplicialObject C} (f : U ⟶ V) (g : V ⟶ W) :
    normalizedCochainMap (f ≫ g) =
      normalizedCochainMap f ≫ normalizedCochainMap g :=
  Formalization.Books.Simplicial.Unit24.normalizedCochainMap_comp f g

/-- The normalized cochain functor `Q`. -/
abbrev normalizedCochainFunctor
    (C : Type u) [Category.{v} C] [Abelian C] :
    CosimplicialObject C ⥤ CochainComplex C ℕ :=
  Formalization.Books.Simplicial.Unit24.normalizedCochainFunctor C

theorem normalizedCochainFunctor_exact
    {C : Type u} [Category.{v} C] [Abelian C] :
    exactFunctor (CosimplicialObject C) (CochainComplex C ℕ)
      (normalizedCochainFunctor C) :=
  Formalization.Books.Simplicial.Unit24.normalizedCochainFunctor_exact

/-! ## The six assertions of the dual Dold--Kan lemma -/

noncomputable abbrev cochainFunctorBiproduct
    {C : Type u} [Category.{v} C] [Abelian C]
    (F G : CosimplicialObject C ⥤ CochainComplex C ℕ) :
    CosimplicialObject C ⥤ CochainComplex C ℕ :=
  Formalization.Books.Simplicial.Unit24.cochainFunctorBiproduct F G

/-- A functorial witness for the source's cochain decomposition `s(U)=D(U)⊕Q(U)`. -/
abbrev NormalizedCochainDecomposition
    (C : Type u) [Category.{v} C] [Abelian C] :=
  Formalization.Books.Simplicial.Unit24.NormalizedCochainDecomposition C

theorem normalizedCochain_decomposition_exists
    {C : Type u} [Category.{v} C] [Abelian C] :
    Nonempty (NormalizedCochainDecomposition C) :=
  Formalization.Books.Simplicial.Unit24.normalizedCochain_decomposition_exists

theorem normalizedCochain_comparison_is_quasiIso
    {C : Type u} [Category.{v} C] [Abelian C]
    (U : CosimplicialObject C) :
    QuasiIso (normalizedCochainComparison U) :=
  Formalization.Books.Simplicial.Unit24.normalizedCochain_comparison_is_quasiIso U

theorem normalizedCochainFunctor_is_equivalence
    {C : Type u} [Category.{v} C] [Abelian C] :
    (normalizedCochainFunctor C).IsEquivalence :=
  Formalization.Books.Simplicial.Unit24.normalizedCochainFunctor_is_equivalence

/-- A categorical equivalence realizing the cosimplicial Dold--Kan theorem. -/
noncomputable abbrev dualDoldKanEquivalence
    (C : Type u) [Category.{v} C] [Abelian C] :
    CosimplicialObject C ≌ CochainComplex C ℕ :=
  Formalization.Books.Simplicial.Unit24.dualDoldKanEquivalence C

end Formalization.Books.Simplicial.Unit25
