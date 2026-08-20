import Mathlib.Algebra.Category.Grp.Basic
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.Algebra.GroupWithZero.Action.Defs
import Mathlib.Algebra.Module.Projective
import Mathlib.CategoryTheory.Limits.Shapes.Kernels
import Mathlib.GroupTheory.Torsion
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.Topology.Algebra.MulAction
import Mathlib.Topology.Connected.TotallyDisconnected
import Formalization.Books.Topology.Unit22.ProfiniteSpaces

/-!
# Étale Cohomology, Chapter 55: Group cohomology

This file records the discrete continuous-action module categories and the
source-facing interfaces for their right-derived invariant functors.  The
action, continuity, stabilizer, tensor, finite-dimensionality, and torsion
predicates use Mathlib's canonical APIs.
-/

namespace Formalization.Books.EtaleCohomology.Unit55

open CategoryTheory
open Set
open scoped TensorProduct

universe u v

variable (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-! ## Discrete continuous modules -/

/-- A discrete continuous `G`-module, with the additive action represented by
Mathlib's `DistribMulAction` and its joint continuity by `ContinuousSMul`. -/
structure GModule where
  carrier : Type u
  [addCommGroup : AddCommGroup carrier]
  [action : DistribMulAction G carrier]
  [topology : TopologicalSpace carrier]
  [discrete : DiscreteTopology carrier]
  continuous_action : ContinuousSMul G carrier

instance : CoeSort (GModule G) (Type u) := ⟨GModule.carrier⟩

attribute [coe] GModule.carrier

instance (M : GModule G) : AddCommGroup M := M.addCommGroup
instance (M : GModule G) : DistribMulAction G M := M.action
instance (M : GModule G) : TopologicalSpace M := M.topology
instance (M : GModule G) : DiscreteTopology M := M.discrete
instance (M : GModule G) : ContinuousSMul G M := M.continuous_action

/-- Construct the source's `G`-module object from a type carrying the required
canonical action and discrete topology. -/
def GModule.of (M : Type u) [AddCommGroup M] [DistribMulAction G M]
    [TopologicalSpace M] [DiscreteTopology M] [ContinuousSMul G M] : GModule G :=
  ⟨M, inferInstance⟩

/-- Morphisms in the category of discrete continuous `G`-modules. -/
structure GModuleHom (M N : GModule G) where
  hom : M →+ N
  equivariant : ∀ (g : G) (x : M), hom (g • x) = g • hom x

instance : Category (GModule G) where
  Hom M N := GModuleHom G M N
  id M :=
    { hom := AddMonoidHom.id M
      equivariant := by intro g x; rfl }
  comp f g :=
    { hom := g.hom.comp f.hom
      equivariant := by
        intro h x
        change g.hom (f.hom (h • x)) = h • g.hom (f.hom x)
        rw [f.equivariant, g.equivariant] }
  id_comp f := by cases f; rfl
  comp_id f := by cases f; rfl
  assoc f g h := by cases f; cases g; cases h; rfl

omit [IsTopologicalGroup G] in
@[ext]
theorem GModuleHom.ext {M N : GModule G} {f g : M ⟶ N}
    (h : f.hom = g.hom) : f = g := by
  cases f
  cases g
  cases h
  rfl

/-! The continuity criterion in the source is Mathlib's exact theorem. -/

theorem continuous_gmodule_iff_stabilizer_isOpen (M : GModule G) :
    ContinuousSMul G M ↔
      ∀ x : M, IsOpen (MulAction.stabilizer G x : Set G) :=
  continuousSMul_iff_stabilizer_isOpen

theorem continuous_action_of_discrete_group
    (M : Type u) [AddCommGroup M] [DistribMulAction G M]
    [TopologicalSpace M] [DiscreteTopology M] [DiscreteTopology G] :
    ContinuousSMul G M := by
  rw [continuousSMul_iff_stabilizer_isOpen]
  intro x
  exact isOpen_discrete _

def GModule.ofDiscrete (M : Type u) [AddCommGroup M] [DistribMulAction G M]
    [TopologicalSpace M] [DiscreteTopology M] [DiscreteTopology G] : GModule G :=
  ⟨M, continuous_action_of_discrete_group G M⟩

/-! ## Invariants and the module categories -/

/-- The invariant subgroup `M^G`. -/
def invariants (M : GModule G) : AddSubgroup M where
  carrier := {x | ∀ g : G, g • x = x}
  zero_mem' := by intro g; simp
  add_mem' := by
    intro x y hx hy g
    rw [smul_add, hx g, hy g]
  neg_mem' := by
    intro x hx g
    rw [smul_neg, hx g]

abbrev Invariants (M : GModule G) : Type u := invariants G M

instance invariantsAddCommGroup (M : GModule G) : AddCommGroup (Invariants G M) :=
  inferInstance

/-- The invariants map induced by an equivariant homomorphism. -/
def invariantsMap {M N : GModule G} (f : M ⟶ N) : Invariants G M →+ Invariants G N :=
  { toFun := fun x => ⟨f.hom x, fun g => by rw [← f.equivariant g x, x.property g]⟩
    map_zero' := by
      apply Subtype.ext
      exact f.hom.map_zero
    map_add' := by
      intro x y
      apply Subtype.ext
      exact f.hom.map_add _ _ }

/-- The invariants functor `Γ_G = (-)^G`. -/
def invariantsFunctor : GModule G ⥤ AddCommGrpCat where
  obj M := AddCommGrpCat.of (Invariants G M)
  map f := AddCommGrpCat.ofHom (invariantsMap G f)

/-- The source's category-level assertion that `Mod_G` has enough injectives,
written as the lifting property of injective objects in this concrete category. -/
def IsInjectiveGModule (I : GModule G) : Prop :=
  ∀ {M N : GModule G} (f : M ⟶ N), Function.Injective f.hom →
    ∀ (g : M ⟶ I), ∃ h : N ⟶ I, f ≫ h = g

def HasEnoughInjectivesGModule : Prop :=
  ∀ M : GModule G, ∃ I : GModule G, ∃ f : M ⟶ I,
    Function.Injective f.hom ∧ IsInjectiveGModule G I

theorem gmodule_has_enough_injectives : HasEnoughInjectivesGModule G := by
  sorry

/-! ## `R-G`-modules -/

variable {R : Type v} [Ring R]

/-- A discrete continuous `R-G`-module.  The commuting scalar actions express
that every `G`-action map is `R`-linear. -/
structure RGModule (R : Type v) [Ring R] where
  carrier : Type u
  [addCommGroup : AddCommGroup carrier]
  [module : Module R carrier]
  [action : DistribMulAction G carrier]
  [scalar_action_commutes : SMulCommClass R G carrier]
  [topology : TopologicalSpace carrier]
  [discrete : DiscreteTopology carrier]
  continuous_action : ContinuousSMul G carrier

instance : CoeSort (RGModule G R) (Type u) := ⟨RGModule.carrier⟩

attribute [coe] RGModule.carrier

instance (M : RGModule G R) : AddCommGroup M := M.addCommGroup
instance (M : RGModule G R) : Module R M := M.module
instance (M : RGModule G R) : DistribMulAction G M := M.action
instance (M : RGModule G R) : SMulCommClass R G M := M.scalar_action_commutes
instance (M : RGModule G R) : TopologicalSpace M := M.topology
instance (M : RGModule G R) : DiscreteTopology M := M.discrete
instance (M : RGModule G R) : ContinuousSMul G M := M.continuous_action

def RGModule.of (M : Type u) [AddCommGroup M] [Module R M]
    [DistribMulAction G M] [SMulCommClass R G M]
    [TopologicalSpace M] [DiscreteTopology M] [ContinuousSMul G M] : RGModule G R :=
  ⟨M, inferInstance⟩

/-- The integral scalar structure recovers the underlying `G`-module. -/
def GModule.toZRGModule (M : GModule G) : RGModule G ℤ :=
  RGModule.of G M

/-- Forget the scalar action on an `R-G`-module. -/
def RGModule.toGModule (M : RGModule G R) : GModule G :=
  ⟨M.carrier, M.continuous_action⟩

/-- Morphisms in `Mod_{R,G}`. -/
structure RGModuleHom (M N : RGModule G R) where
  hom : M →ₗ[R] N
  equivariant : ∀ (g : G) (x : M), hom (g • x) = g • hom x

instance : Category (RGModule G R) where
  Hom M N := RGModuleHom G M N
  id M :=
    { hom := LinearMap.id
      equivariant := by intro g x; rfl }
  comp f g :=
    { hom := g.hom.comp f.hom
      equivariant := by
        intro h x
        change g.hom (f.hom (h • x)) = h • g.hom (f.hom x)
        rw [f.equivariant, g.equivariant] }
  id_comp f := by cases f; rfl
  comp_id f := by cases f; rfl
  assoc f g h := by cases f; cases g; cases h; rfl

omit [IsTopologicalGroup G] in
@[ext]
theorem RGModuleHom.ext {M N : RGModule G R} {f g : M ⟶ N}
    (h : f.hom = g.hom) : f = g := by
  cases f
  cases g
  cases h
  rfl

/-! Forgetful functor from scalar modules to the underlying `G`-modules. -/

def rgModuleForget : RGModule G R ⥤ GModule G where
  obj M := RGModule.toGModule G M
  map f :=
    { hom := f.hom.toAddMonoidHom
      equivariant := f.equivariant }
  map_id := by intro M; rfl
  map_comp := by intro M N P f g; rfl

/-- The invariant elements of an `R-G`-module form an `R`-submodule. -/
def rgInvariants (M : RGModule G R) : Submodule R M where
  carrier := {x | ∀ g : G, g • x = x}
  zero_mem' := by intro g; simp
  add_mem' := by
    intro x y hx hy g
    rw [smul_add, hx g, hy g]
  smul_mem' := by
    intro r x hx g
    calc
      g • (r • x) = r • (g • x) :=
        (inferInstance : SMulCommClass R G M).smul_comm r g x |>.symm
      _ = r • x := by rw [hx g]

abbrev RGInvariants (M : RGModule G R) : Type u := rgInvariants G M

def rgInvariantsMap {M N : RGModule G R} (f : M ⟶ N) :
    RGInvariants G M →ₗ[R] RGInvariants G N where
  toFun := fun x => ⟨f.hom x, fun g => by rw [← f.equivariant g x, x.property g]⟩
  map_add' := by
    intro x y
    apply Subtype.ext
    exact f.hom.map_add _ _
  map_smul' := by
    intro r x
    apply Subtype.ext
    exact f.hom.map_smul r x

def rgInvariantsFunctor : RGModule G R ⥤ ModuleCat.{u} R where
  obj M := ModuleCat.of R (RGInvariants G M)
  map f := ModuleCat.ofHom (rgInvariantsMap G f)

/-! ## Cohomology interfaces -/

/-- The selected continuous group cohomology groups.  The first field is the
graded additive-valued functor, the second is its scalar-valued counterpart,
and `degree_zero` records the canonical identification with invariants. -/
class GroupCohomologyData where
  cohomology : ℕ → GModule G ⥤ AddCommGrpCat
  cohomologyR : ∀ (R : Type v) [Ring R], ℕ → RGModule G R ⥤ ModuleCat.{u} R
  degree_zero : ∀ (M : GModule G),
    Nonempty (((cohomology 0).obj M : Type u) ≃+ Invariants G M)
  degree_zeroR : ∀ (R : Type v) [Ring R] (M : RGModule G R),
    Nonempty (((cohomologyR R 0).obj M : Type u) ≃ₗ[R] RGInvariants G M)
  underlying_comparison : ∀ (R : Type v) [Ring R] (i : ℕ),
    Nonempty ((cohomologyR R i ⋙ forget₂ (ModuleCat.{u} R) AddCommGrpCat) ≅
      (rgModuleForget G ⋙ cohomology i))
  right_derived : Prop

abbrev GroupCohomology (M : GModule G) (i : ℕ) [GroupCohomologyData G] : Type u :=
  ((GroupCohomologyData.cohomology (G := G) i).obj M : Type u)

abbrev GroupCohomologyR (R : Type v) [Ring R] (M : RGModule G R) (i : ℕ)
    [GroupCohomologyData G] : Type u :=
  ((GroupCohomologyData.cohomologyR (G := G) R i).obj M : Type u)

omit [IsTopologicalGroup G] in
theorem group_cohomology_degree_zero (M : GModule G) [GroupCohomologyData G] :
    Nonempty (GroupCohomology G M 0 ≃+ Invariants G M) :=
  GroupCohomologyData.degree_zero M

omit [IsTopologicalGroup G] in
theorem group_cohomologyR_degree_zero (R : Type v) [Ring R]
    (M : RGModule G R) [GroupCohomologyData G] :
    Nonempty (GroupCohomologyR G R M 0 ≃ₗ[R] RGInvariants G M) :=
  GroupCohomologyData.degree_zeroR R M

omit [IsTopologicalGroup G] in
theorem group_cohomology_underlying_comparison
    (R : Type v) [Ring R] (i : ℕ) [GroupCohomologyData G] :
    Nonempty ((GroupCohomologyData.cohomologyR (G := G) R i ⋙
        forget₂ (ModuleCat.{u} R) AddCommGrpCat) ≅
      (rgModuleForget G ⋙ GroupCohomologyData.cohomology (G := G) i)) :=
  GroupCohomologyData.underlying_comparison R i

/-! The `RΓ_G` and `H^i(G, -)` nomenclature is exposed by the following
source-facing aliases. -/

abbrev GammaG (M : GModule G) := Invariants G M

def IsRightDerivedGroupCohomology [GroupCohomologyData G] : Prop :=
  GroupCohomologyData.right_derived (G := G)

/-! ## The finite-projective Ext comparison -/

/-- The action map on an `R-G`-module is `R`-linear. -/
def RGModule.actionLinearMap {R : Type v} [Ring R] (M : RGModule G R) (g : G) :
    M →ₗ[R] M where
  toFun x := g • x
  map_add' := by intro x y; exact smul_add g x y
  map_smul' := by
    intro r x
    exact (inferInstance : SMulCommClass R G M).smul_comm r g x |>.symm

/-- The contragredient action map on the linear dual, before packaging it as
an `R-G`-module. -/
def contragredientMap {R : Type v} [CommRing R] (M : RGModule G R) (g : G) :
    Module.Dual R M →ₗ[R] Module.Dual R M :=
  LinearMap.dualMap (RGModule.actionLinearMap G M g⁻¹)

/-- A source-facing package for the contragredient action and the diagonal
action on `M^∨ ⊗ N`. -/
structure DualTensorActionData {R : Type v} [CommRing R]
    (M N : RGModule G R) where
  dual : RGModule G R
  dual_underlying : dual.carrier ≃+ Module.Dual R M
  dual_action : G → Module.Dual R M → Module.Dual R M
  dual_action_formula : ∀ (g : G) (f : Module.Dual R M),
    dual_action g f = contragredientMap G M g f
  dual_action_compatibility : ∀ (g : G) (f : Module.Dual R M),
    dual_underlying (g • dual_underlying.symm f) = dual_action g f
  tensor : RGModule G R
  tensor_underlying : tensor.carrier ≃+ (Module.Dual R M ⊗[R] N)
  diagonal_action_formula : ∀ (g : G) (f : Module.Dual R M) (n : N),
    tensor_underlying (g • tensor_underlying.symm (f ⊗ₜ[R] n)) =
      contragredientMap G M g f ⊗ₜ[R] (g • n)
  tensor_with : RGModule G R → RGModule G R
  tensor_with_underlying : ∀ (E : RGModule G R),
    (tensor_with E).carrier ≃+ (Module.Dual R M ⊗[R] E)
  hom_tensor_iso : ∀ (E : RGModule G R),
    Nonempty ((E ⟶ tensor) ≃ (tensor_with E ⟶ N))

def IsFiniteProjective (R : Type v) (M : Type u) [Semiring R]
    [AddCommMonoid M] [Module R M] : Prop :=
  Module.Finite R M ∧ Module.Projective R M

/-! The project does not need a particular Ext implementation at the statement
stage, so this class records the canonical additive-valued Ext groups supplied
by the eventual derived-functor construction. -/
class RGExtData (R : Type v) [Ring R] where
  ext : RGModule G R → RGModule G R → ℕ → Type u
  extAddCommGroup : ∀ (M N : RGModule G R) (i : ℕ), AddCommGroup (ext M N i)

instance (M N : RGModule G R) (i : ℕ) [RGExtData G R] :
    AddCommGroup (RGExtData.ext (G := G) (R := R) M N i) :=
  RGExtData.extAddCommGroup M N i

abbrev RGExt (R : Type v) [Ring R] (M N : RGModule G R) (i : ℕ)
    [RGExtData G R] : Type u :=
  RGExtData.ext (G := G) (R := R) M N i

theorem ext_modules_hom {R : Type v} [CommRing R] [RGExtData G R]
    (M N : RGModule G R) (hM : IsFiniteProjective R M) (i : ℕ)
    [GroupCohomologyData G] :
    ∀ D : DualTensorActionData G M N,
      Nonempty (RGExt G R M N i ≃+ GroupCohomologyR G R D.tensor i) := by
  sorry

/-! ## Finiteness and profinite torsion -/

/-- Topological finite generation: the closure of a subgroup generated by a
finite list is the whole topological group. -/
def TopologicallyFinitelyGenerated : Prop :=
  ∃ n : ℕ, ∃ g : Fin n → G,
    Dense ((Subgroup.closure (Set.range g) : Subgroup G) : Set G)

theorem finite_dimensional_first_group_cohomology
    {k : Type v} [Field k] (V : RGModule G k)
    (hG : TopologicallyFinitelyGenerated G)
    (hV : Module.Finite k V) [GroupCohomologyData G] :
    Module.Finite k (GroupCohomologyR G k V 1) := by
  sorry

/-- The source's profinite hypothesis, reusing the earlier profinite-space API. -/
abbrev IsProfiniteGroup : Prop :=
  Formalization.Books.Topology.Unit22.IsProfiniteSpace G

theorem profinite_group_cohomology_is_torsion
    (hG : IsProfiniteGroup G) (M : GModule G) (i : ℕ) (hi : 0 < i)
    [GroupCohomologyData G] :
    IsAddTorsion (GroupCohomology G M i) := by
  sorry

theorem profinite_group_cohomology_rat_zero
    (hG : IsProfiniteGroup G) (M : RGModule G ℚ) (i : ℕ) (hi : 0 < i)
    [GroupCohomologyData G] :
    Subsingleton (GroupCohomologyR G ℚ M i) := by
  sorry

end Formalization.Books.EtaleCohomology.Unit55
