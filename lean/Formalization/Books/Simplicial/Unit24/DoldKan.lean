import Formalization.Books.Simplicial.Unit23.SimplicialObjectsAndChainComplexes
import Mathlib.CategoryTheory.Equivalence

/-!
# Simplicial Methods, Chapter 24: Dold--Kan

The source's `N` is the normalized chain-complex functor from Chapter 23.
This file records the formal criterion used in the proof and the reverse
construction on a nonnegative chain complex.  The finite coproducts below are
indexed by epimorphisms in the simplex category; this is the categorical form
of the source's maps whose image is an initial segment `[k]`.
-/

noncomputable section

namespace Formalization.Books.Simplicial.Unit24

open CategoryTheory
open CategoryTheory.Limits
open Formalization.Books.Simplicial.Unit18
open Formalization.Books.Simplicial.Unit22
open Formalization.Books.Simplicial.Unit23
open Opposite
open HomologicalComplex
open scoped _root_.Simplicial
open scoped ZeroObject

universe v u

attribute [local instance] CategoryTheory.Abelian.hasFiniteBiproducts

/-! ## The abstract quasi-inverse criterion -/

theorem exact_faithful_essentially_surjective_quasi_inverse
    {A : Type u} {B : Type v} [Category.{v, u} A] [Category.{u, v} B]
    [Abelian A] [Abelian B]
    (N : A ⥤ B) (S : B ⥤ A)
    (hN : exactFunctor A B N) (hS : exactFunctor B A S)
    (g : S ⋙ N ≅ 𝟭 B) (hfaithful : N.Faithful) (hessentiallySurjective : S.EssSurj) :
    N.IsEquivalence ∧ S.IsEquivalence := by
  sorry

/-! ## The reverse construction -/

/-- A source index in degree `X`: an epimorphism from `X` onto `[k]`. -/
abbrev DoldKanIndex (X : SimplexCategory) :=
  Σ k : Fin (X.len + 1), {α : X ⟶ ⦋k.1⦌ // Epi α}

noncomputable instance doldKanIndexFintype (X : SimplexCategory) :
    Fintype (DoldKanIndex X) := Fintype.ofFinite _

/-- The degree-`X` direct sum in the reverse Dold--Kan construction. -/
noncomputable def doldKanDegree
    {C : Type u} [Category.{v} C] [Abelian C]
    (A : ChainComplex C ℕ) (X : SimplexCategory) : C :=
  ∐ fun a : DoldKanIndex X => A.X a.1.1

@[simp]
theorem doldKanDegree_at_standard_simplex
    {C : Type u} [Category.{v} C] [Abelian C]
    (A : ChainComplex C ℕ) (n : ℕ) :
    doldKanDegree A ⦋n⦌ =
      ∐ fun a : DoldKanIndex ⦋n⦌ => A.X a.1.1 :=
  rfl

/-- The map on one source summand in the four cases of the source definition.

The `HEq` tests are needed because the target `[k]` varies with the index.
They express equality of the composite with the same-index map, or with the
last coface after dropping the index by one. -/
noncomputable def doldKanComponentMap
    {C : Type u} [Category.{v} C] [Abelian C]
    (A : ChainComplex C ℕ) {X Y : SimplexCategory} (f : X ⟶ Y)
    (a : DoldKanIndex Y) (b : DoldKanIndex X) :
    A.X a.1.1 ⟶ A.X b.1.1 :=
  by
    classical
    exact
      if h : a.1.1 = b.1.1 then
        if hcomp : HEq b.2.1 (f ≫ a.2.1) then
          eqToHom (congrArg A.X h)
        else 0
      else if h : a.1.1 = b.1.1 + 1 then
        if hcomp : HEq (f ≫ a.2.1)
            (b.2.1 ≫ SimplexCategory.δ (Fin.last (b.1.1 + 1))) then
          (-1 : ℤ) ^ a.1.1 • A.d a.1.1 b.1.1
        else 0
      else 0

theorem doldKanComponentMap_same_degree
    {C : Type u} [Category.{v} C] [Abelian C]
    (A : ChainComplex C ℕ) {X Y : SimplexCategory} (f : X ⟶ Y)
    (a : DoldKanIndex Y) (b : DoldKanIndex X)
    (hdegree : a.1.1 = b.1.1)
    (hcomp : HEq b.2.1 (f ≫ a.2.1)) :
    doldKanComponentMap A f a b = eqToHom (congrArg A.X hdegree) := by
  sorry

theorem doldKanComponentMap_drop_degree
    {C : Type u} [Category.{v} C] [Abelian C]
    (A : ChainComplex C ℕ) {X Y : SimplexCategory} (f : X ⟶ Y)
    (a : DoldKanIndex Y) (b : DoldKanIndex X)
    (hdegree : a.1.1 = b.1.1 + 1)
    (hcomp : HEq (f ≫ a.2.1)
      (b.2.1 ≫ SimplexCategory.δ (Fin.last (b.1.1 + 1)))) :
    doldKanComponentMap A f a b =
      (-1 : ℤ) ^ a.1.1 • A.d a.1.1 b.1.1 := by
  sorry

theorem doldKanComponentMap_zero_of_other_case
    {C : Type u} [Category.{v} C] [Abelian C]
    (A : ChainComplex C ℕ) {X Y : SimplexCategory} (f : X ⟶ Y)
    (a : DoldKanIndex Y) (b : DoldKanIndex X)
    (hdegree : a.1.1 ≠ b.1.1)
    (hdrop : a.1.1 ≠ b.1.1 + 1) :
    doldKanComponentMap A f a b = 0 := by
  sorry

/-- The map induced by `f : X ⟶ Y`, from the `Y`-degree to the `X`-degree. -/
noncomputable def doldKanMap
    {C : Type u} [Category.{v} C] [Abelian C]
    (A : ChainComplex C ℕ) {X Y : SimplexCategory} (f : X ⟶ Y) :
    doldKanDegree A Y ⟶ doldKanDegree A X :=
  Sigma.desc (fun a =>
    ∑ b : DoldKanIndex X,
      doldKanComponentMap A f a b ≫
        Sigma.ι (fun b : DoldKanIndex X => A.X b.1.1) b)

/- The source's four composition cases, and the cancellation of the two
   successive differential cases, are exactly the following functor laws. -/
theorem doldKanMap_id
    {C : Type u} [Category.{v} C] [Abelian C]
    (A : ChainComplex C ℕ) (X : SimplexCategory) :
    doldKanMap A (𝟙 X) = 𝟙 (doldKanDegree A X) := by
  sorry

theorem doldKanMap_comp
    {C : Type u} [Category.{v} C] [Abelian C]
    (A : ChainComplex C ℕ) {X Y Z : SimplexCategory}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    doldKanMap A (f ≫ g) = doldKanMap A g ≫ doldKanMap A f := by
  sorry

/-- The simplicial object `S(A_•)` from the source's reverse construction. -/
noncomputable def doldKanSimplicialObject
    {C : Type u} [Category.{v} C] [Abelian C]
    (A : ChainComplex C ℕ) : SimplicialObject C where
  obj X := doldKanDegree A X.unop
  map {X Y} f := doldKanMap A f.unop
  map_id X := doldKanMap_id A X.unop
  map_comp f g := by
    change doldKanMap A (g.unop ≫ f.unop) =
      doldKanMap A f.unop ≫ doldKanMap A g.unop
    exact doldKanMap_comp A g.unop f.unop

@[simp]
theorem doldKanSimplicialObject_obj
    {C : Type u} [Category.{v} C] [Abelian C]
    (A : ChainComplex C ℕ) (n : ℕ) :
    (doldKanSimplicialObject A).obj (op ⦋n⦌) = doldKanDegree A ⦋n⦌ :=
  rfl

/-! ## The identity and degenerate summands -/

/-- The index in degree `n` represented by `id_[n]`. -/
def doldKanIdentityIndex (n : ℕ) : DoldKanIndex ⦋n⦌ :=
  ⟨⟨n, Nat.lt_succ_self n⟩, ⟨𝟙 _, inferInstance⟩⟩

abbrev DoldKanDegenerateIndex (n : ℕ) :=
  {a : DoldKanIndex ⦋n⦌ // a.1.1 < n}

noncomputable instance doldKanDegenerateIndexFintype (n : ℕ) :
    Fintype (DoldKanDegenerateIndex n) := Fintype.ofFinite _

noncomputable def doldKanDegenerateDegree
    {C : Type u} [Category.{v} C] [Abelian C]
    (A : ChainComplex C ℕ) (n : ℕ) : C :=
  ∐ fun a : DoldKanDegenerateIndex n => A.X a.1.1.1

noncomputable def doldKanIdentitySummand
    {C : Type u} [Category.{v} C] [Abelian C]
    (A : ChainComplex C ℕ) (n : ℕ) :
    A.X n ⟶ doldKanDegree A ⦋n⦌ :=
  Sigma.ι (fun a : DoldKanIndex ⦋n⦌ => A.X a.1.1) (doldKanIdentityIndex n)

theorem doldKanIndex_eq_identity_of_degree_ge
    {n : ℕ} (a : DoldKanIndex ⦋n⦌) (h : n ≤ a.1.1) :
    a = doldKanIdentityIndex n := by
  sorry

theorem doldKanIndex_degree_ge_iff_identity
    {n : ℕ} (a : DoldKanIndex ⦋n⦌) :
    n ≤ a.1.1 ↔ a = doldKanIdentityIndex n := by
  sorry

theorem doldKan_identity_degenerate_decomposition
    {C : Type u} [Category.{v} C] [Abelian C]
    (A : ChainComplex C ℕ) (n : ℕ) :
    Nonempty (doldKanDegree A ⦋n⦌ ≅
      A.X n ⊞ doldKanDegenerateDegree A n) := by
  sorry

/-- The differential on the identity summand described in the source. -/
def doldKanIdentityDifferential
    {C : Type u} [Category.{v} C] [Abelian C]
    (A : ChainComplex C ℕ) (n : ℕ) :
    A.X (n + 1) ⟶ A.X n :=
  (-1 : ℤ) ^ (n + 1) • A.d (n + 1) n

theorem doldKanIdentitySummand_face_zero
    {C : Type u} [Category.{v} C] [Abelian C]
    (A : ChainComplex C ℕ) (n : ℕ) (i : Fin (n + 2))
    (hi : i ≠ Fin.last (n + 1)) :
    doldKanIdentitySummand A (n + 1) ≫
        doldKanMap A (SimplexCategory.δ i) = 0 := by
  sorry

theorem doldKanIdentitySummand_last_face
    {C : Type u} [Category.{v} C] [Abelian C]
    (A : ChainComplex C ℕ) (n : ℕ) :
    doldKanIdentitySummand A (n + 1) ≫
        doldKanMap A (SimplexCategory.δ (Fin.last (n + 1))) =
      doldKanIdentityDifferential A n ≫ doldKanIdentitySummand A n := by
  sorry

theorem doldKan_normalized_degree_formula
    {C : Type u} [Category.{v} C] [Abelian C]
    (A : ChainComplex C ℕ) (n : ℕ) :
    Nonempty (normalizedObject (doldKanSimplicialObject A) n ≅ A.X n) := by
  sorry

theorem doldKan_normalized_differential_formula
    {C : Type u} [Category.{v} C] [Abelian C]
    (A : ChainComplex C ℕ) (n : ℕ) :
    ∃ (e₁ : normalizedObject (doldKanSimplicialObject A) (n + 1) ≅ A.X (n + 1))
      (e₀ : normalizedObject (doldKanSimplicialObject A) n ≅ A.X n),
      e₁.inv ≫ (normalizedChainComplex (doldKanSimplicialObject A)).d (n + 1) n ≫
          e₀.hom = doldKanIdentityDifferential A n := by
  sorry

theorem doldKan_normalized_identity_differential
    {C : Type u} [Category.{v} C] [Abelian C]
    (A : ChainComplex C ℕ) :
    Nonempty (normalizedChainComplex (doldKanSimplicialObject A) ≅ A) := by
  sorry

/-! ## Functoriality in the chain complex -/

/-- The degreewise map induced by a chain map on the reverse construction. -/
noncomputable def doldKanChainMap
    {C : Type u} [Category.{v} C] [Abelian C]
    {A B : ChainComplex C ℕ} (f : A ⟶ B) (X : SimplexCategory) :
    doldKanDegree A X ⟶ doldKanDegree B X :=
  Sigma.desc (fun a =>
    f.f a.1.1 ≫ Sigma.ι (fun b : DoldKanIndex X => B.X b.1.1) a)

theorem doldKanChainMap_id
    {C : Type u} [Category.{v} C] [Abelian C]
    (A : ChainComplex C ℕ) (X : SimplexCategory) :
    doldKanChainMap (𝟙 A) X = 𝟙 (doldKanDegree A X) := by
  sorry

theorem doldKanChainMap_comp
    {C : Type u} [Category.{v} C] [Abelian C]
    {A B D : ChainComplex C ℕ} (f : A ⟶ B) (g : B ⟶ D)
    (X : SimplexCategory) :
    doldKanChainMap (f ≫ g) X =
      doldKanChainMap f X ≫ doldKanChainMap g X := by
  sorry

theorem doldKanChainMap_naturality
    {C : Type u} [Category.{v} C] [Abelian C]
    {A B : ChainComplex C ℕ} (f : A ⟶ B)
    {X Y : SimplexCategory} (g : X ⟶ Y) :
    doldKanMap A g ≫ doldKanChainMap f X =
      doldKanChainMap f Y ≫ doldKanMap B g := by
  sorry

/-! ## The comparison `S(N(U)) ⟶ U` -/

/-- The source's summandwise map from `S(N(U))` to `U`. -/
noncomputable def normalizedDoldKanComparisonComponent
    {C : Type u} [Category.{v} C] [Abelian C]
    (U : SimplicialObject C) (X : SimplexCategory) :
    doldKanDegree (normalizedChainComplex U) X ⟶ U.obj (op X) :=
  Sigma.desc (fun a =>
    (normalizedSubobject U a.1.1).arrow ≫ U.map a.2.1.op)

theorem normalizedDoldKanComparison_naturality
    {C : Type u} [Category.{v} C] [Abelian C]
    (U : SimplicialObject C) {X Y : SimplexCategory} (f : X ⟶ Y) :
    doldKanMap (normalizedChainComplex U) f ≫
        normalizedDoldKanComparisonComponent U X =
      normalizedDoldKanComparisonComponent U Y ≫ U.map f.op := by
  sorry

/-- The natural map `S(N(U)) ⟶ U` used in the proof of Dold--Kan. -/
def normalizedDoldKanComparison
    {C : Type u} [Category.{v} C] [Abelian C]
    (U : SimplicialObject C) :
    doldKanSimplicialObject (normalizedChainComplex U) ⟶ U :=
  { app := fun X => normalizedDoldKanComparisonComponent U X.unop
    naturality := by
      intro X Y f
      exact normalizedDoldKanComparison_naturality U f.unop }

@[simp]
theorem normalizedDoldKanComparison_app_standard
    {C : Type u} [Category.{v} C] [Abelian C]
    (U : SimplicialObject C) (n : ℕ) :
    (normalizedDoldKanComparison U).app (op ⦋n⦌) =
      normalizedDoldKanComparisonComponent U ⦋n⦌ :=
  rfl

theorem normalizedDoldKanComparison_isIso
    {C : Type u} [Category.{v} C] [Abelian C]
    (U : SimplicialObject C) :
    IsIso (normalizedDoldKanComparison U) := by
  sorry

/-- The reverse Dold--Kan functor on chain complexes. -/
def doldKanExtension
    (C : Type u) [Category.{v} C] [Abelian C] :
    ChainComplex C ℕ ⥤ SimplicialObject C where
  obj A := doldKanSimplicialObject A
  map f :=
    { app := fun X => doldKanChainMap f X.unop
      naturality := by
        intro X Y g
        exact doldKanChainMap_naturality f g.unop }
  map_id A := by
    ext X
    exact doldKanChainMap_id A X.unop
  map_comp f g := by
    ext X
    exact doldKanChainMap_comp f g X.unop

@[simp]
theorem doldKanExtension_obj
    {C : Type u} [Category.{v} C] [Abelian C]
    (A : ChainComplex C ℕ) :
    (doldKanExtension C).obj A = doldKanSimplicialObject A :=
  rfl

/-! ## The normalization functor and the Dold--Kan equivalence -/

theorem normalizedChainComplexFunctor_faithful
    {C : Type u} [Category.{v} C] [Abelian C] :
    (normalizedChainComplexFunctor C).Faithful := by
  sorry

theorem normalizedChainComplexFunctor_reflects_monomorphism
    {C : Type u} [Category.{v} C] [Abelian C]
    {U V : SimplicialObject C} (f : U ⟶ V)
    (hf : Mono ((normalizedChainComplexFunctor C).map f)) :
    Mono f := by
  sorry

theorem normalizedChainComplexFunctor_reflects_epimorphism
    {C : Type u} [Category.{v} C] [Abelian C]
    {U V : SimplicialObject C} (f : U ⟶ V)
    (hf : Epi ((normalizedChainComplexFunctor C).map f)) :
    Epi f := by
  sorry

theorem normalizedChainComplexFunctor_reflects_isomorphism
    {C : Type u} [Category.{v} C] [Abelian C]
    {U V : SimplicialObject C} (f : U ⟶ V)
    (hf : IsIso ((normalizedChainComplexFunctor C).map f)) :
    IsIso f := by
  sorry

theorem doldKan_normalization_is_equivalence
    {C : Type u} [Category.{v} C] [Abelian C] :
    (normalizedChainComplexFunctor C).IsEquivalence := by
  sorry

theorem doldKan_extension_is_equivalence
    {C : Type u} [Category.{v} C] [Abelian C] :
    (doldKanExtension C).IsEquivalence := by
  sorry

theorem doldKan_extension_normalization_iso_exists
    {C : Type u} [Category.{v} C] [Abelian C] :
    Nonempty (doldKanExtension C ⋙ normalizedChainComplexFunctor C ≅
      𝟭 (ChainComplex C ℕ)) := by
  sorry

theorem normalization_doldKan_extension_iso_exists
    {C : Type u} [Category.{v} C] [Abelian C] :
    Nonempty (normalizedChainComplexFunctor C ⋙ doldKanExtension C ≅
      𝟭 (SimplicialObject C)) := by
  sorry

end Formalization.Books.Simplicial.Unit24
