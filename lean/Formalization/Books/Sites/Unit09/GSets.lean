import Formalization.Books.Sites.Unit08.Refinements
import Mathlib.CategoryTheory.Action.Concrete

/-!
# Sites and Sheaves, Chapter 9: The example of G-sets

This file formalizes the precise constructions and assertions in the section
`The example of G-sets`.  A site of G-sets is represented by a full
subcategory of `Action (Type u) G`; the source's five properties are recorded
by `GroupActionSiteProperties`.  The presheaf and sheaf constructions use
Mathlib's canonical functor-category and site interfaces.
-/

namespace Formalization.Books.Sites.Unit09

open CategoryTheory CategoryTheory.Limits CategoryTheory.Presieve
open Formalization.Books.Sites.Unit02
open Formalization.Books.Sites.Unit06
open Formalization.Books.Sites.Unit07
open Formalization.Books.Sites.Unit08
open Opposite

universe u v w u₁ v₁ u₂ v₂

variable {G : Type u} [Group G]

/-! ## The five properties of the site -/

/-- The full subcategory of `G`-sets selected as the objects of the site. -/
abbrev GSetSubcategory (G : Type u) [Group G] (T : Set (GSet G)) :=
  ObjectProperty.FullSubcategory (fun X : GSet G => X ∈ T)

/-- The inclusion of the selected `G`-sets into all `G`-sets. -/
abbrev GSetSubcategoryInclusion (G : Type u) [Group G]
    (T : Set (GSet G)) : GSetSubcategory G T ⥤ GSet G :=
  ObjectProperty.ι (fun X : GSet G => X ∈ T)

/-- The underlying map of the action of `g` on a `G`-set. -/
def gSetActionMap (U : GSet G) (g : G) (x : U.V) : U.V :=
  U.ρ g x

/-- A subset of a `G`-set which is stable under the action. -/
def IsGInvariantSubset (U : GSet G) (O : Set U.V) : Prop :=
  ∀ (g : G) (x : U.V), x ∈ O → gSetActionMap U g x ∈ O

/-- The restricted `G`-set carried by an invariant subset. -/
def restrictedGSet {U : GSet G} {O : Set U.V}
    (hO : IsGInvariantSubset U O) : GSet G := by
  letI : MulAction G O := {
    smul := fun g x => ⟨gSetActionMap U g x.1, hO g x.1 x.2⟩
    one_smul := by
      intro x
      apply Subtype.ext
      change gSetActionMap U 1 x.1 = x.1
      simp [gSetActionMap, Action.ρ_one]
    mul_smul := by
      intro g h x
      apply Subtype.ext
      change gSetActionMap U (g * h) x.1 =
        gSetActionMap U g (gSetActionMap U h x.1)
      change U.ρ (g * h) x.1 = U.ρ g (U.ρ h x.1)
      rw [U.ρ.map_mul]
      rfl
  }
  exact Action.ofMulAction G O

/-- The source's five hypotheses on the chosen site of `G`-sets.

The ambient category is a full subcategory by construction.  The remaining
fields are, in source order: the regular `G`-set is present, fiber products
agree with those in all `G`-sets, invariant subsets have representatives, and
jointly-surjective families are combinatorially equivalent to coverings.
-/
structure GroupActionSiteProperties (T : Set (GSet G))
    [HasPullbacks (GSetSubcategory G T)]
    (J : Site (GSetSubcategory G T)) : Prop where
  contains_regular : T (leftRegularGSet G)
  fiber_products_agree :
    PreservesLimitsOfShape WalkingCospan
      (GSetSubcategoryInclusion G T)
  invariant_subset_represented :
    ∀ (U : GSetSubcategory G T) (O : Set U.1.V),
      (hO : IsGInvariantSubset U.1 O) →
        ∃ V : GSetSubcategory G T,
          Nonempty (V.1 ≅ restrictedGSet (U := U.1) (O := O) hO)
  jointly_surjective_families_are_coverings :
    ∀ {ι : Type u} (U : GSetSubcategory G T)
      (V : ι → GSetSubcategory G T)
      (f : ∀ i, V i ⟶ U),
      (∀ x : U.1.V, ∃ i y,
        ((Action.forget (Type u) G).map
          ((GSetSubcategoryInclusion G T).map (f i))) y = x) →
        ∃ 𝒱 : IndexedFamily.{u + 1, u, u} (GSetSubcategory G T) U,
          𝒱.presieve ∈ coverings J U ∧
          CombinatoriallyEquivalent
              { index := ι, domain := V, map := f } 𝒱

/-- The full-subcategory inclusion supplies the source's property (a). -/
theorem gSetSubcategory_inclusion_full (T : Set (GSet G)) :
    (GSetSubcategoryInclusion G T).Full := by
  infer_instance

/-! ## The regular `G`-set and its endomorphisms -/

/-- The regular object of the selected full subcategory. -/
def regularObject (T : Set (GSet G))
    (hT : T (leftRegularGSet G)) : GSetSubcategory G T :=
  ⟨leftRegularGSet G, hT⟩

/-- Right multiplication on the regular left `G`-set. -/
def rightMultiplication (g : G) :
    leftRegularGSet G ⟶ leftRegularGSet G := by
  let h : G → G := fun s => s * g
  exact { hom := TypeCat.ofHom h, comm := by sorry }

/-- Right multiplication viewed as an endomorphism in the full subcategory. -/
def rightMultiplicationInSubcategory (T : Set (GSet G))
    (hT : T (leftRegularGSet G)) (g : G) :
    regularObject T hT ⟶ regularObject T hT :=
  by
    exact ⟨rightMultiplication g⟩

/-- Evaluation at `1` from endomorphisms of the regular `G`-set to `Gᵐᵒᵖ`. -/
def regularEndomorphismEvaluation :
    (leftRegularGSet G ⟶ leftRegularGSet G) ≃ Gᵐᵒᵖ :=
  { toFun := fun φ => MulOpposite.op
      (show G from ConcreteCategory.hom φ.hom (1 : G))
    invFun := fun g => rightMultiplication g.unop
    left_inv := by sorry
    right_inv := by sorry }

/-- The inverse of evaluation at `1` sends `g` to right multiplication. -/
theorem regularEndomorphismEvaluation_inv (g : Gᵐᵒᵖ) :
    (regularEndomorphismEvaluation (G := G)).symm g =
      rightMultiplication g.unop := by
  rfl

/-- Evaluation at `1` reverses composition, as required by the opposite group
in the source. -/
theorem regularEndomorphismEvaluation_comp
    (φ ψ : leftRegularGSet G ⟶ leftRegularGSet G) :
    regularEndomorphismEvaluation (φ ≫ ψ) =
      regularEndomorphismEvaluation ψ * regularEndomorphismEvaluation φ := by
  sorry

/-! ## Evaluation of presheaves at the regular object -/

/-- The `G`-action on the value of a presheaf at the regular object. -/
def presheafRegularGSet (T : Set (GSet G))
    (hT : T (leftRegularGSet G))
    (F : Presheaf (GSetSubcategory G T)) : GSet G := by
  letI : MulAction G (F.obj (op (regularObject T hT))) := {
    smul := fun g s =>
      F.map (rightMultiplicationInSubcategory T hT g).op s
    one_smul := by
      intro s
      sorry
    mul_smul := by
      intro g h s
      sorry
  }
  exact Action.ofMulAction G (F.obj (op (regularObject T hT)))

/-- The action on evaluation at the regular object is the pullback action. -/
theorem presheafRegularGSet_action (T : Set (GSet G))
    (hT : T (leftRegularGSet G))
    (F : Presheaf (GSetSubcategory G T)) (g : G)
    (s : F.obj (op (regularObject T hT))) :
    (presheafRegularGSet T hT F).ρ g s =
      F.map (rightMultiplicationInSubcategory T hT g).op s := by
  rfl

/-- Evaluation at the regular object is a functor to `G`-sets. -/
def presheafEvaluationFunctor (T : Set (GSet G))
    (hT : T (leftRegularGSet G)) :
    PSh (GSetSubcategory G T) ⥤ GSet G :=
  { obj := fun F => presheafRegularGSet T hT F
    map := fun {F H} η => {
      hom := η.app (op (regularObject T hT))
      comm := by
        intro g
        sorry }
    map_id := by
      intro F
      apply Action.hom_ext
      rfl
    map_comp := by
      intro F H K η θ
      apply Action.hom_ext
      rfl }

/-- The representable presheaf evaluates at the regular object to its target. -/
theorem representable_presheaf_evaluation (T : Set (GSet G))
    (hT : T (leftRegularGSet G))
    (U : GSetSubcategory G T) :
    Nonempty ((presheafEvaluationFunctor T hT).obj
        (representablePresheaf U) ≅ U.1) := by
  sorry

/-! ## The presheaf associated to a `G`-set -/

/-- The presheaf `𝓕_S(U) = Hom_G(U,S)`. -/
def gSetPresheaf (T : Set (GSet G)) (S : GSet G) :
    Presheaf (GSetSubcategory G T) :=
  (GSetSubcategoryInclusion G T).op ⋙ yoneda.obj S

/-- Postcomposition by an equivariant map gives a map of the associated
presheaves. -/
def gSetPresheafMap (T : Set (GSet G)) {S₁ S₂ : GSet G}
    (f : S₁ ⟶ S₂) : gSetPresheaf T S₁ ⟶ gSetPresheaf T S₂ :=
  Functor.whiskerLeft (GSetSubcategoryInclusion G T).op
    (yoneda.map f)

/-- The associated presheaf is a sheaf for any site satisfying the source's
joint-surjectivity hypothesis. -/
theorem gSetPresheaf_isSheaf (T : Set (GSet G))
    [HasPullbacks (GSetSubcategory G T)]
    (J : Site (GSetSubcategory G T))
    (hT : GroupActionSiteProperties T J) (S : GSet G) :
    SetSheaf J (gSetPresheaf T S) := by
  sorry

/-- The functor from `G`-sets to sheaves sending `S` to `𝓕_S`. -/
def gSetToSheaves (T : Set (GSet G))
    [HasPullbacks (GSetSubcategory G T)]
    (J : Site (GSetSubcategory G T))
    (hT : GroupActionSiteProperties T J) :
    GSet G ⥤ Sheaves J :=
  { obj := fun S => ⟨gSetPresheaf T S, gSetPresheaf_isSheaf T J hT S⟩
    map := fun f => ⟨gSetPresheafMap T f⟩
    map_id := by
      intro S
      sorry
    map_comp := by
      intro S₁ S₂ S₃ f g
      sorry }

/-- The inclusion of sheaves into presheaves appearing in the source's
category diagram. -/
abbrev sheafInclusion (T : Set (GSet G))
    [HasPullbacks (GSetSubcategory G T)]
    (J : Site (GSetSubcategory G T)) :
    Sheaves J ⥤ Presheaf (GSetSubcategory G T) :=
  ObjectProperty.ι (SetSheaf J)

/-- Evaluation at the regular object recovers the original `G`-set from
`𝓕_S`, by evaluation at `1`. -/
theorem gSetPresheaf_evaluation (T : Set (GSet G))
    [HasPullbacks (GSetSubcategory G T)]
    (J : Site (GSetSubcategory G T))
    (hT : GroupActionSiteProperties T J) (S : GSet G) :
    Nonempty ((presheafEvaluationFunctor T
      (GroupActionSiteProperties.contains_regular hT)).obj
      (gSetPresheaf T S) ≅ S) := by
  sorry

/-! ## The canonical map for a sheaf -/

/-- The orbit map `α_u : {}_G G → U`, `g ↦ g • u`. -/
def orbitMap (U : GSet G) (u : U.V) : leftRegularGSet G ⟶ U := by
  let h : G → U.V := fun g => U.ρ g u
  exact { hom := TypeCat.ofHom h, comm := by sorry }

/-- The orbit map as a morphism in the full subcategory. -/
def orbitMapInSubcategory (T : Set (GSet G))
    (hT : T (leftRegularGSet G))
    (U : GSetSubcategory G T) (u : U.1.V) :
    regularObject T hT ⟶ U :=
  by
    exact ⟨orbitMap U.1 u⟩

/-- The stabilizer of a point in a `G`-set. -/
def stabilizer (U : GSet G) (u : U.V) : Subgroup G where
  carrier := {g | U.ρ g u = u}
  one_mem' := by sorry
  mul_mem' := by sorry
  inv_mem' := by sorry

/-- The elements of a `G`-set fixed by a subgroup. -/
def fixedBySubgroup (K : Subgroup G) (X : GSet G) : Set X.V :=
  {x | ∀ g : K, X.ρ g x = x}

/-- Equivariant maps out of a transitive orbit are determined by a fixed point
of its stabilizer.  This is the fixed-point identification used in the
source's proof of the canonical-map isomorphism. -/
theorem orbit_maps_eq_stabilizer_fixed_points (U X : GSet G) (u : U.V)
    (hOrbit : ∀ v : U.V, ∃ g : G, U.ρ g u = v) :
    Nonempty ((U ⟶ X) ≃
      {x : X.V // x ∈ fixedBySubgroup (stabilizer U u) X}) := by
  sorry

/-- The component function of the canonical map from a sheaf to the sheaf
associated to its value at the regular object. -/
def canonicalMapFunction (T : Set (GSet G))
    (hT : T (leftRegularGSet G))
    (H : Presheaf (GSetSubcategory G T))
  (U : GSetSubcategory G T) (s : H.obj (op U)) :
    (U.1 ⟶ presheafRegularGSet T hT H) :=
  { hom := TypeCat.ofHom (show U.1.V → H.obj (op (regularObject T hT)) from
        fun u => H.map (orbitMapInSubcategory T hT U u).op s)
    comm := by sorry }

/-- The canonical component is the source's formula
`u ↦ α_u^* s`. -/
theorem canonicalMapFunction_apply (T : Set (GSet G))
    (hT : T (leftRegularGSet G))
    (H : Presheaf (GSetSubcategory G T))
    (U : GSetSubcategory G T) (s : H.obj (op U)) (u : U.1.V) :
    (canonicalMapFunction T hT H U s).hom u =
      H.map (orbitMapInSubcategory T hT U u).op s := by
  rfl

/-- The canonical map is a morphism of presheaves. -/
def canonicalSheafMap (T : Set (GSet G))
    (hT : T (leftRegularGSet G))
    (H : Presheaf (GSetSubcategory G T)) :
  H ⟶ gSetPresheaf T (presheafRegularGSet T hT H) :=
  { app := fun U => TypeCat.ofHom (fun s => canonicalMapFunction T hT H U.unop s)
    naturality := by sorry }

/-- The canonical map is a morphism of sheaves when `H` is a sheaf. -/
def canonicalSheafMapInSheaves (T : Set (GSet G))
    [HasPullbacks (GSetSubcategory G T)]
    (J : Site (GSetSubcategory G T))
    (hT : GroupActionSiteProperties T J)
    (H : Sheaves J) :
    H ⟶ (gSetToSheaves T J hT).obj
        ((presheafEvaluationFunctor T
          (GroupActionSiteProperties.contains_regular hT)).obj H.obj) :=
  ⟨canonicalSheafMap T (GroupActionSiteProperties.contains_regular hT) H.obj⟩

/-! ## The equivalence of sheaves and `G`-sets -/

/-- A pair of functors is a quasi-inverse pair. -/
def IsQuasiInverse {C : Type v₁} {D : Type v₂}
    [Category.{u₁, v₁} C] [Category.{u₂, v₂} D]
    (F : C ⥤ D) (G : D ⥤ C) : Prop :=
  Nonempty (F ⋙ G ≅ 𝟭 C) ∧ Nonempty (G ⋙ F ≅ 𝟭 D)

/-- The evaluation and `S ↦ 𝓕_S` functors are quasi-inverse. -/
theorem sheaves_on_group_quasi_inverse (T : Set (GSet G))
    [HasPullbacks (GSetSubcategory G T)]
    (J : Site (GSetSubcategory G T))
    (hT : GroupActionSiteProperties T J) :
    IsQuasiInverse
      (ObjectProperty.ι (SetSheaf J) ⋙
        presheafEvaluationFunctor T
          (GroupActionSiteProperties.contains_regular hT))
      (gSetToSheaves T J hT) := by
  sorry

/-- Consequently, sheaves on the site are equivalent to `G`-sets. -/
theorem sheaves_on_group_equiv (T : Set (GSet G))
    [HasPullbacks (GSetSubcategory G T)]
    (J : Site (GSetSubcategory G T))
    (hT : GroupActionSiteProperties T J) :
    Nonempty (Sheaves J ≌ GSet G) := by
  sorry

end Formalization.Books.Sites.Unit09
