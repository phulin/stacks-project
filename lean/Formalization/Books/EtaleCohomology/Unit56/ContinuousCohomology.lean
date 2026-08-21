import Formalization.Books.EtaleCohomology.Unit55
import Mathlib.Algebra.Homology.HomologicalComplexAbelian
import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
import Mathlib.Algebra.Homology.ShortComplex.Homology
import Mathlib.Algebra.Category.Grp.Abelian
import Mathlib.Topology.ContinuousMap.Algebra
import Mathlib.Topology.Algebra.MulAction

/-!
# Étale Cohomology, Chapter 56: Tate's continuous cohomology

This file formalizes the continuous inhomogeneous cochain complex and the
source-facing interfaces for its exact-sequence and comparison properties.
The continuity and exactness proofs are intentionally deferred to the prove
stage; the definitions below select those proved interfaces rather than
introducing axioms or parallel cochain objects.
-/

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open Formalization.Books.EtaleCohomology.Unit55

universe u v

namespace Formalization.Books.EtaleCohomology.Unit56

variable (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-! ## Topological coefficient modules and continuous cochains -/

/-- A topological abelian group with a continuous action of `G`. -/
structure TopologicalGModule where
  carrier : Type u
  [addCommGroup : AddCommGroup carrier]
  [action : DistribMulAction G carrier]
  [topology : TopologicalSpace carrier]
  [isTopologicalAddGroup : IsTopologicalAddGroup carrier]
  continuous_action : ContinuousSMul G carrier

instance : CoeSort (TopologicalGModule G) (Type u) := ⟨TopologicalGModule.carrier⟩

attribute [coe] TopologicalGModule.carrier

instance (M : TopologicalGModule G) : AddCommGroup M := M.addCommGroup
instance (M : TopologicalGModule G) : DistribMulAction G M := M.action
instance (M : TopologicalGModule G) : TopologicalSpace M := M.topology
instance (M : TopologicalGModule G) : IsTopologicalAddGroup M := M.isTopologicalAddGroup
instance (M : TopologicalGModule G) : ContinuousSMul G M := M.continuous_action

/-- The topological module associated to a discrete continuous `G`-module. -/
def GModule.toTopologicalGModule (M : GModule G) : TopologicalGModule G :=
  ⟨M.carrier, M.continuous_action⟩

/-- The degree-`n` group of continuous inhomogeneous cochains.  Degree zero is
the coefficient group itself, as in the source; positive degrees are
continuous maps on `Fin n` copies of `G`. -/
abbrev ContinuousCochain (M : TopologicalGModule G) (n : ℕ) : Type u :=
  ContinuousMap (Fin n → G) M

noncomputable def continuousCochainDegreeZeroEquiv (M : TopologicalGModule G) :
    M ≃+ ContinuousCochain G M 0 where
  toFun m :=
    { toFun := fun _ => m
      continuous_toFun := continuous_const }
  invFun f := f (fun i => Fin.elim0 i)
  left_inv := by intro m; rfl
  right_inv := by
    intro f
    apply ContinuousMap.ext
    intro x
    have hx : x = (fun i => Fin.elim0 i) := Subsingleton.elim _ _
    rw [hx]
    rfl
  map_add' := by intro m n; rfl

/-- The coordinate map which multiplies the two entries at the `j`th face. -/
def combineCochainCoordinates {n : ℕ} (j : Fin (n + 1))
    (x : Fin (n + 2) → G) : Fin (n + 1) → G :=
  Fin.succAboveCases j
    (x (Fin.castSucc j) * x (Fin.succ j))
    (fun k =>
      if j < @Fin.succAbove n j k then
        x (Fin.succ (@Fin.succAbove n j k))
      else
        x (Fin.castSucc (@Fin.succAbove n j k)))

/-- The inhomogeneous differential formula in positive degree. -/
def cochainDifferentialFormula (M : TopologicalGModule G) (n : ℕ)
    (f : (Fin (n + 1) → G) → M) (x : Fin (n + 2) → G) : M :=
  x 0 • f (fun i => x (Fin.succ i)) +
    ∑ j : Fin (n + 1),
      ((-1 : ℤ) ^ (j.1 + 1)) •
        f (combineCochainCoordinates G j x) +
    ((-1 : ℤ) ^ (n + 1)) • f (fun i => x (Fin.castSucc i))

/-- The degree-zero differential formula, written in the continuous-map model
for the one-point space. -/
def zeroCochainDifferentialFormula (M : TopologicalGModule G)
    (f : ContinuousCochain G M 0) (x : Fin 1 → G) : M :=
  x 0 • f (fun i => Fin.elim0 i) - f (fun i => Fin.elim0 i)

/-! The continuity interface is the only deferred proof in the construction
of the differential.  Its statement is the precise fact that the displayed
source formula preserves continuous cochains. -/

theorem exists_zero_continuous_cochain_differential (M : TopologicalGModule G) :
    ∃ d : ContinuousCochain G M 0 →+ ContinuousCochain G M 1,
      ∀ (f : ContinuousCochain G M 0) (x : Fin 1 → G),
        (d f) x = zeroCochainDifferentialFormula G M f x := by
  sorry

theorem exists_succ_continuous_cochain_differential (M : TopologicalGModule G)
    (n : ℕ) :
    ∃ d : ContinuousCochain G M (n + 1) →+ ContinuousCochain G M (n + 2),
      ∀ (f : ContinuousCochain G M (n + 1)) (x : Fin (n + 2) → G),
        (d f) x = cochainDifferentialFormula G M n f.toFun x := by
  sorry

/-- The differential of the continuous inhomogeneous cochain complex. -/
noncomputable def continuousCochainDifferential (M : TopologicalGModule G)
    (n : ℕ) : ContinuousCochain G M n →+ ContinuousCochain G M (n + 1) :=
  match n with
  | 0 => Classical.choose (exists_zero_continuous_cochain_differential G M)
  | n + 1 => Classical.choose (exists_succ_continuous_cochain_differential G M n)

theorem continuousCochainDifferential_zero_apply (M : TopologicalGModule G)
    (f : ContinuousCochain G M 0) (x : Fin 1 → G) :
    (continuousCochainDifferential G M 0 f) x =
      zeroCochainDifferentialFormula G M f x :=
  Classical.choose_spec (exists_zero_continuous_cochain_differential G M) f x

theorem continuousCochainDifferential_on_coefficients_apply
    (M : TopologicalGModule G) (m : M) (x : Fin 1 → G) :
    (continuousCochainDifferential G M 0
      (continuousCochainDegreeZeroEquiv G M m)) x = x 0 • m - m := by
  sorry

theorem continuousCochainDifferential_succ_apply (M : TopologicalGModule G)
    (n : ℕ) (f : ContinuousCochain G M (n + 1)) (x : Fin (n + 2) → G) :
    (continuousCochainDifferential G M (n + 1) f) x =
      cochainDifferentialFormula G M n f.toFun x :=
  Classical.choose_spec (exists_succ_continuous_cochain_differential G M n) f x

/-! ## The cochain complex and continuous cohomology -/

theorem continuousCochainDifferential_square_zero (M : TopologicalGModule G)
    (n : ℕ) :
    (continuousCochainDifferential G M (n + 1)).comp
        (continuousCochainDifferential G M n) = 0 := by
  sorry

theorem continuousCochainDifferential_category_comp (M : TopologicalGModule G)
    (n : ℕ) :
    AddCommGrpCat.ofHom (continuousCochainDifferential G M n) ≫
        AddCommGrpCat.ofHom (continuousCochainDifferential G M (n + 1)) = 0 := by
  sorry

/-- Tate's complex of continuous inhomogeneous cochains. -/
noncomputable def continuousCochainComplex (M : TopologicalGModule G) :
    CochainComplex AddCommGrpCat ℕ :=
  CochainComplex.of
    (fun n => AddCommGrpCat.of (ContinuousCochain G M n))
    (fun n => AddCommGrpCat.ofHom (continuousCochainDifferential G M n))
    (fun n => continuousCochainDifferential_category_comp G M n)

/-- The `i`th continuous cohomology object. -/
noncomputable def continuousCohomologyObject (M : TopologicalGModule G) (i : ℕ) :
    AddCommGrpCat :=
  (HomologicalComplex.homologyFunctor AddCommGrpCat (ComplexShape.up ℕ) i).obj
    (continuousCochainComplex G M)

/-- The underlying additive group of `H^i_cont(G, M)`. -/
abbrev ContinuousCohomology (M : TopologicalGModule G) (i : ℕ) : Type u :=
  continuousCohomologyObject G M i

/-! ## Short exact sequences and the delta-functor assertion -/

/-- A concrete short exact sequence in the discrete continuous `G`-module
category.  This is used because Chapter 55 supplies the concrete category but
does not yet package it as an abelian category. -/
structure GModuleShortExact where
  X₁ : GModule G
  X₂ : GModule G
  X₃ : GModule G
  f : X₁ ⟶ X₂
  g : X₂ ⟶ X₃
  comp_zero : ∀ x, g.hom (f.hom x) = 0
  f_injective : Function.Injective f.hom
  g_surjective : Function.Surjective g.hom
  exact : ∀ y, g.hom y = 0 → ∃ x, f.hom x = y

/-- A categorical short-exact sequence of the continuous cochain complexes
whose maps are the cochainwise postcompositions induced by a short exact
sequence of discrete modules. -/
structure InducedContinuousCochainShortExact (S : GModuleShortExact G) where
  left_map :
    continuousCochainComplex G
        (Formalization.Books.EtaleCohomology.Unit56.GModule.toTopologicalGModule G S.X₁) ⟶
      continuousCochainComplex G
        (Formalization.Books.EtaleCohomology.Unit56.GModule.toTopologicalGModule G S.X₂)
  right_map :
    continuousCochainComplex G
        (Formalization.Books.EtaleCohomology.Unit56.GModule.toTopologicalGModule G S.X₂) ⟶
      continuousCochainComplex G
        (Formalization.Books.EtaleCohomology.Unit56.GModule.toTopologicalGModule G S.X₃)
  map_comp_zero : left_map ≫ right_map = 0
  left_components : ∀ (n : ℕ) (c : ContinuousCochain G
      (Formalization.Books.EtaleCohomology.Unit56.GModule.toTopologicalGModule G S.X₁) n)
      (x : Fin n → G),
      (show ContinuousCochain G
          (Formalization.Books.EtaleCohomology.Unit56.GModule.toTopologicalGModule G S.X₂) n
        from (left_map.f n).hom c) x = S.f.hom (c x)
  right_components : ∀ (n : ℕ) (c : ContinuousCochain G
      (Formalization.Books.EtaleCohomology.Unit56.GModule.toTopologicalGModule G S.X₂) n)
      (x : Fin n → G),
      (show ContinuousCochain G
          (Formalization.Books.EtaleCohomology.Unit56.GModule.toTopologicalGModule G S.X₃) n
        from (right_map.f n).hom c) x = S.g.hom (c x)
  short_exact : (ShortComplex.mk left_map right_map map_comp_zero).ShortExact

theorem discrete_short_exact_gmodule_gives_short_exact_continuous_cochains
    (S : GModuleShortExact G) : Nonempty (InducedContinuousCochainShortExact G S) := by
  sorry

/-- Exactness of an additive pair, used to state the long exact sequence of
cohomology without imposing an unproved abelian structure on `GModule`. -/
def AdditiveExactPair {A B C : Type u} [AddCommGroup A] [AddCommGroup B]
    [AddCommGroup C] (f : A →+ B) (g : B →+ C) : Prop :=
  (∀ x, g (f x) = 0) ∧ ∀ y, g y = 0 → ∃ x, f x = y

structure ContinuousLongExactData
    (F : ℕ → GModule G ⥤ AddCommGrpCat) (S : GModuleShortExact G) where
  delta : ∀ n : ℕ,
    ((F n).obj S.X₃ : Type u) →+
      ((F (n + 1)).obj S.X₁ : Type u)
  initial_injective : Function.Injective ((F 0).map S.f).hom
  exact_middle : ∀ n, AdditiveExactPair ((F n).map S.f).hom ((F n).map S.g).hom
  exact_left : ∀ n, AdditiveExactPair (delta n) ((F (n + 1)).map S.f).hom
  exact_right : ∀ n, AdditiveExactPair ((F n).map S.g).hom (delta n)

/-- The source's assertion that continuous cohomology on `Mod_G` is a
cohomological delta-functor, stated with an explicit objectwise identification
with the cohomology of the continuous cochain complex. -/
def ContinuousCohomologyIsCohomologicalDeltaFunctor : Prop :=
  ∃ F : ℕ → GModule G ⥤ AddCommGrpCat,
    (∀ (i : ℕ) (M : GModule G),
      Nonempty (((F i).obj M : Type u) ≃+
        ContinuousCohomology G
          (Formalization.Books.EtaleCohomology.Unit56.GModule.toTopologicalGModule G M) i)) ∧
    ∀ S : GModuleShortExact G, Nonempty (ContinuousLongExactData G F S)

theorem continuous_cohomology_is_cohomological_deltaFunctor :
    ContinuousCohomologyIsCohomologicalDeltaFunctor G := by
  sorry

/-! ## Comparison with ordinary group cohomology -/

theorem exists_continuous_cohomology_comparison_map
    (M : GModule G) (i : ℕ) [GroupCohomologyData G] :
    Nonempty (GroupCohomology G M i →+
      ContinuousCohomology G
        (Formalization.Books.EtaleCohomology.Unit56.GModule.toTopologicalGModule G M) i) := by
  sorry

/-- The canonical comparison map supplied by the universal delta-functor
property. -/
noncomputable def continuousCohomologyComparisonMap
    (M : GModule G) (i : ℕ) [GroupCohomologyData G] :
    GroupCohomology G M i →+
      ContinuousCohomology G
        (Formalization.Books.EtaleCohomology.Unit56.GModule.toTopologicalGModule G M) i :=
  Classical.choice (exists_continuous_cohomology_comparison_map G M i)

theorem continuous_cohomology_comparison_isIso_of_discrete
    [DiscreteTopology G] (M : GModule G) (i : ℕ) [GroupCohomologyData G] :
    ∃ e : GroupCohomology G M i ≃+
        ContinuousCohomology G
          (Formalization.Books.EtaleCohomology.Unit56.GModule.toTopologicalGModule G M) i,
      e.toAddMonoidHom = continuousCohomologyComparisonMap G M i := by
  sorry

theorem continuous_cohomology_comparison_isIso_of_profinite
    (hG : IsProfiniteGroup G) (M : GModule G) (i : ℕ)
    [GroupCohomologyData G] :
    ∃ e : GroupCohomology G M i ≃+
        ContinuousCohomology G
          (Formalization.Books.EtaleCohomology.Unit56.GModule.toTopologicalGModule G M) i,
      e.toAddMonoidHom = continuousCohomologyComparisonMap G M i := by
  sorry

end Formalization.Books.EtaleCohomology.Unit56
