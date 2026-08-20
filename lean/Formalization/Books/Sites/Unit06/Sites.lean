import Formalization.Books.Sites.Unit02.Presheaves
import Mathlib.CategoryTheory.Action.Concrete
import Mathlib.CategoryTheory.Action.Limits
import Mathlib.CategoryTheory.Sites.JointlySurjective
import Mathlib.CategoryTheory.Sites.Pretopology
import Mathlib.CategoryTheory.Sites.Sheaf
import Mathlib.CategoryTheory.Sites.Spaces

/-!
# Sites and Sheaves, Chapter 6: Sites

The source calls a category together with a Grothendieck pretopology a
`site`.  Mathlib's `CategoryTheory.Pretopology` is the canonical interface
for this notion: its covering data are presieves, and `Presieve.ofArrows`
represents the indexed families used in the source.  This file keeps that
interface rather than introducing a second, equivalent site structure.

The source allows a pullback to exist only for the arrows in a covering
family.  Mathlib's pretopology interface assumes all pullbacks in the ambient
category; this is the standard small adaptation used by the library and is
automatic for the two examples formalized below.
-/

namespace Formalization.Books.Sites.Unit06

open CategoryTheory CategoryTheory.Limits CategoryTheory.Presieve
open TopologicalSpace

universe u v w

variable {C : Type u} [Category.{v} C]

/-! ## Families and sites -/

/-- A family of morphisms with fixed target, represented by a presieve. -/
abbrev FamilyOfMorphisms (U : C) := Presieve U

/-- The presieve represented by an indexed family of arrows with target `U`. -/
def familyOfArrows {ι : Type w} {U : C} (V : ι → C)
    (f : ∀ i, V i ⟶ U) : FamilyOfMorphisms U :=
  Presieve.ofArrows V f

/-- A site in the source's sense, using Mathlib's canonical pretopology API. -/
abbrev Site (C : Type u) [Category.{v} C] [HasPullbacks C] := Pretopology C

/-- The covering families of a site on `U`. -/
abbrev coverings [HasPullbacks C] (J : Site C) (U : C) : Set (FamilyOfMorphisms U) :=
  J U

/-- The singleton family of an isomorphism is covering. -/
theorem singleton_isIso_mem [HasPullbacks C] (J : Site C)
    {V U : C} (f : V ⟶ U) [IsIso f] :
    familyOfArrows (fun _ : PUnit => V) (fun _ => f) ∈ coverings J U := by
  rw [familyOfArrows, Presieve.ofArrows_pUnit]
  exact J.has_isos f

/-- Pulling back a covering family gives a covering family. -/
theorem pullback_family_mem [HasPullbacks C] (J : Site C)
    {U V : C} (f : V ⟶ U) (R : FamilyOfMorphisms U)
    (hR : R ∈ coverings J U) :
    R.pullbackArrows f ∈ coverings J V := by
  exact J.pullbacks f R hR

/-- Refining each member of a covering family preserves coveringness. -/
theorem bind_family_mem [HasPullbacks C] (J : Site C)
    {U : C} (R : FamilyOfMorphisms U)
    (T : ∀ ⦃V : C⦄ ⦃f : V ⟶ U⦄, R f → FamilyOfMorphisms V)
    (hR : R ∈ coverings J U)
    (hT : ∀ (V : C) (f : V ⟶ U) (hf : R f),
      T (f := f) hf ∈ coverings J V) :
    R.bind T ∈ coverings J U := by
  exact J.transitive R T hR (fun {V} f hf => hT V f hf)

/-!
The `Presieve` representation includes the empty family (`⊥`), and its
coverings are sets rather than proper classes.  Thus the set-sized and
small-category restrictions discussed in the source are built into the
ambient Mathlib types.
-/

/-! ## The site of open subsets of a topological space -/

/-- The category called `X_Zar` in the source. -/
abbrev topologicalSiteCategory (X : Type u) [TopologicalSpace X] := Opens X

/-- The canonical site of open subsets of `X`. -/
def topologicalSite (X : Type u) [TopologicalSpace X] :
    Site (topologicalSiteCategory X) :=
  Opens.pretopology X

/-- The source-facing union criterion for an indexed family of open subsets. -/
def topologicalFamilyCovers (X : Type u) [TopologicalSpace X]
    {ι : Type w} (U : ι → Opens X) (V : Opens X) : Prop :=
  (⋃ i, (U i : Set X)) = (V : Set X)

/-- Membership in the topological pretopology is the pointwise union criterion. -/
theorem topologicalSite_mem_iff (X : Type u) [TopologicalSpace X] {U : Opens X}
    (R : FamilyOfMorphisms U) :
    R ∈ topologicalSite X U ↔
      ∀ x : X, x ∈ U → ∃ (V : Opens X) (f : V ⟶ U), R f ∧ x ∈ V := by
  rfl

/-- An indexed family of opens covers its target exactly when their union is the target. -/
theorem topologicalSite_family_mem_iff [TopologicalSpace X]
    {ι : Type w} {U : ι → Opens X} {V : Opens X}
    (f : ∀ i, U i ⟶ V) :
    familyOfArrows U f ∈ topologicalSite X V ↔
      topologicalFamilyCovers X U V := by
  change (∀ x : X, x ∈ V →
      ∃ (W : Opens X) (g : W ⟶ V), familyOfArrows U f g ∧ x ∈ W) ↔ _
  constructor
  · intro h
    apply Set.Subset.antisymm
    · intro x hx
      obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp hx
      exact (f i).le hxi
    · intro x hx
      obtain ⟨W, g, hg, hxW⟩ := h x hx
      obtain ⟨i⟩ := hg
      exact Set.mem_iUnion.mpr ⟨i, hxW⟩
  · intro h x hx
    change (⋃ i, (U i : Set X)) = (V : Set X) at h
    change x ∈ (V : Set X) at hx
    rw [← h] at hx
    obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp hx
    exact ⟨U i, f i, Presieve.ofArrows.mk i, hxi⟩

/-- The empty family is a covering of the empty open. -/
def emptyOpenCoveringFamily (X : Type u) [TopologicalSpace X] :
  FamilyOfMorphisms (⊥ : Opens X) :=
  familyOfArrows (fun _i : Empty => (⊥ : Opens X)) (fun i => nomatch i)

theorem emptyOpenCoveringFamily_mem (X : Type u) [TopologicalSpace X] :
    emptyOpenCoveringFamily X ∈ topologicalSite X (⊥ : Opens X) := by
  change ∀ x : X, x ∈ (⊥ : Opens X) →
      ∃ (W : Opens X) (g : W ⟶ (⊥ : Opens X)),
        emptyOpenCoveringFamily X g ∧ x ∈ W
  simp

/-! ## The site of sets with a group action -/

/-- The universe-bounded category used for `G`-sets. -/
abbrev GSet (G : Type u) [Monoid G] := Action (Type u) G

/-- The jointly-surjective precoverage on `G`-sets, pulled back from `Type`. -/
def groupActionPrecoverage (G : Type u) [Group G] :
    Precoverage (GSet G) :=
  Types.jointlySurjectivePrecoverage.comap (Action.forget (Type u) G)

/-- The site of universe-bounded `G`-sets with jointly surjective covers. -/
def groupActionSite (G : Type u) [Group G] : Site (GSet G) :=
  let K : Precoverage (GSet G) := groupActionPrecoverage G
  letI : K.HasIsos := by
    constructor
    intro S T f hf
    dsimp [K, groupActionPrecoverage]
    rw [Precoverage.mem_comap_iff, Presieve.map_singleton]
    exact Types.singleton_mem_jointlySurjectivePrecoverage_iff.mpr
      (surjective_of_epi _)
  letI : K.IsStableUnderBaseChange := by
    dsimp [K, groupActionPrecoverage]
    infer_instance
  letI : K.IsStableUnderComposition := by
    dsimp [K, groupActionPrecoverage]
    infer_instance
  K.toPretopology

/-- The covering condition on a presieve of `G`-sets is joint surjectivity. -/
theorem groupActionSite_mem_iff (G : Type u) [Group G]
    {U : GSet G} (R : FamilyOfMorphisms U) :
    R ∈ groupActionSite G U ↔
      ∀ x : U.V, ∃ (V : GSet G) (f : V ⟶ U),
        R f ∧ x ∈ Set.range ((Action.forget (Type u) G).map f) := by
  change R ∈ groupActionPrecoverage G U ↔ _
  constructor
  · intro h x
    obtain ⟨Y, f, hf, y, hy⟩ :=
      (Presieve.mem_comap_jointlySurjectivePrecoverage_iff
        (F := Action.forget (Type u) G) (X := U) (R := R)).mp h x
    exact ⟨Y, f, hf, y, hy⟩
  · intro h
    apply (Presieve.mem_comap_jointlySurjectivePrecoverage_iff
      (F := Action.forget (Type u) G) (X := U) (R := R)).mpr
    intro x
    obtain ⟨Y, f, hf, y, hy⟩ := h x
    exact ⟨Y, f, hf, y, hy⟩

/-- The indexed-family form of joint surjectivity for `G`-sets. -/
theorem groupActionSite_family_mem_iff (G : Type u) [Group G]
    {ι : Type w} {U : ι → GSet G} {V : GSet G}
    (f : ∀ i, U i ⟶ V) :
    familyOfArrows U f ∈ groupActionSite G V ↔
      ∀ x : V.V, ∃ i, x ∈ Set.range ((Action.forget (Type u) G).map (f i)) := by
  change Presieve.ofArrows U f ∈
      Types.jointlySurjectivePrecoverage.comap (Action.forget (Type u) G) V ↔ _
  constructor
  · intro h x
    obtain ⟨i, y, hy⟩ :=
      (Presieve.ofArrows_mem_comap_jointlySurjectivePrecoverage_iff
        (F := Action.forget (Type u) G) (X := V) (Y := U) (f := f)).mp h x
    exact ⟨i, y, hy⟩
  · intro h
    apply (Presieve.ofArrows_mem_comap_jointlySurjectivePrecoverage_iff
      (F := Action.forget (Type u) G) (X := V) (Y := U) (f := f)).mpr
    intro x
    obtain ⟨i, y, hy⟩ := h x
    exact ⟨i, y, hy⟩

/-- The category of `G`-sets has fiber products. -/
theorem groupAction_has_fiber_products (G : Type u) [Group G] :
    HasPullbacks (GSet G) := by
  infer_instance

/-- The regular left `G`-set `{}_G G`. -/
def leftRegularGSet (G : Type u) [Group G] : GSet G :=
  Action.ofMulAction G G

/-- Its action is left multiplication. -/
theorem leftRegularGSet_action (G : Type u) [Group G] (g x : G) :
    (leftRegularGSet G).ρ g x = g * x := by
  change g • x = g * x
  rfl

/-! ## The countable special case -/

/-- The full subcategory of countable `G`-sets mentioned in the source. -/
abbrev CountableGSet (G : Type u) [Group G] :=
  ObjectProperty.FullSubcategory (fun X : GSet G => Countable X.V)

/-- The underlying-action functor from countable `G`-sets. -/
abbrev countableGSetUnderlying (G : Type u) [Group G] :
    CountableGSet G ⥤ GSet G :=
  ObjectProperty.ι _

/-- A countable family of morphisms of countable `G`-sets. -/
structure CountableGSetFamily (G : Type u) [Group G]
    (U : CountableGSet G) where
  index : Type u
  index_countable : Countable index
  domain : index → CountableGSet G
  map : ∀ i, domain i ⟶ U

/-- The presieve represented by a countable family. -/
def CountableGSetFamily.presieve {G : Type u} [Group G]
    {U : CountableGSet G} (F : CountableGSetFamily G U) : Presieve U :=
  Presieve.ofArrows F.domain F.map

/-- A countable family is jointly surjective on its target. -/
def CountableGSetFamily.JointlySurjective {G : Type u} [Group G]
    {U : CountableGSet G} (F : CountableGSetFamily G U) : Prop :=
  ∀ x : U.1.V, ∃ i,
    x ∈ Set.range
      ((Action.forget (Type u) G).map
        ((countableGSetUnderlying G).map (F.map i)))

/-! The countable-index covering data can be bundled as a precoverage. -/

/-- A presieve is generated by a countable jointly-surjective family. -/
def countableGSetCovering {G : Type u} [Group G]
    {U : CountableGSet G} (R : Presieve U) : Prop :=
  ∃ F : CountableGSetFamily G U,
    F.presieve = R ∧ F.JointlySurjective

/-- The covering presieves in the countable special case from the source. -/
def countableGSetPrecoverage (G : Type u) [Group G] :
    Precoverage (CountableGSet G) where
  coverings U := {R | countableGSetCovering (U := U) R}

theorem mem_countableGSetPrecoverage_iff (G : Type u) [Group G]
    {U : CountableGSet G} {R : Presieve U} :
    R ∈ countableGSetPrecoverage G U ↔ countableGSetCovering R := by
  rfl

/-! ## The indiscrete (chaotic) site -/

/-- The site whose only covering families are singleton isomorphisms. -/
def indiscreteSite (C : Type u) [Category.{v} C] [HasPullbacks C] : Site C :=
  Pretopology.trivial C

theorem indiscreteSite_mem_iff (C : Type u) [Category.{v} C] [HasPullbacks C]
    {U : C} (R : FamilyOfMorphisms U) :
    R ∈ indiscreteSite C U ↔
      ∃ (V : C) (f : V ⟶ U) (_ : IsIso f), R = Presieve.singleton f := by
  rfl

/-- The Grothendieck topology associated to the indiscrete site is trivial. -/
def indiscreteTopology (C : Type u) [Category.{v} C] [HasPullbacks C] :
    GrothendieckTopology C :=
  (indiscreteSite C).toGrothendieck

theorem indiscreteTopology_eq_bot (C : Type u) [Category.{v} C] [HasPullbacks C] :
    indiscreteTopology C = ⊥ := by
  change (Pretopology.trivial C).toGrothendieck = ⊥
  have h : Pretopology.trivial C = (⊥ : Pretopology C) := rfl
  rw [h]
  exact Pretopology.toGrothendieck_bot (C := C)

/-- Every set-valued presheaf is a sheaf for the indiscrete site. -/
theorem indiscreteSite_every_presheaf_isSheaf (C : Type u) [Category.{v} C]
    [HasPullbacks C] (F : Cᵒᵖ ⥤ Type v) :
    Presheaf.IsSheaf (indiscreteTopology C) F := by
  rw [indiscreteTopology_eq_bot]
  exact Presheaf.isSheaf_bot F

/-!
`CountableGSetFamily` records the source's countable-index covering data
without imposing a second site API; the ambient universe-bounded
`groupActionSite` above is the set-sized version used by later declarations.
-/

end Formalization.Books.Sites.Unit06
