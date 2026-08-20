import Formalization.Books.Sites.Unit06.Sites
import Mathlib.CategoryTheory.Sites.EqualizerSheafCondition
import Mathlib.Topology.Sheaves.Sheaf

/-!
# Sites and Sheaves, Chapter 7: Sheaves

This file formalizes the source section `Sheaves`.  The covering data are kept
in Mathlib's canonical pretopology interface from Chapter 6.  In particular,
the equalizer fork for an indexed family of arrows is Mathlib's
`Equalizer.Presieve.Arrows` construction, and the sheaf predicates are the
canonical `Presieve.IsSheaf` and `Presheaf.IsSheaf` predicates.
-/

namespace Formalization.Books.Sites.Unit07

open CategoryTheory CategoryTheory.Limits CategoryTheory.Presieve
open Formalization.Books.Sites.Unit02
open Formalization.Books.Sites.Unit06
open Opposite TopologicalSpace

universe u v u' v' w

variable {C : Type u} [Category.{v} C] [HasPullbacks C]

/-! ## Set-valued sheaves and the equalizer diagram -/

/-- The source's notion of a set-valued sheaf on a site. -/
abbrev SetValuedSheaf (J : Site C)
    (F : Cᵒᵖ ⥤ Type w) : Prop :=
  Presieve.IsSheaf J.toGrothendieck F

/-- The source's notion of a sheaf of sets on a site. -/
abbrev SetSheaf (J : Site C) (F : Presheaf C) : Prop :=
  SetValuedSheaf J F

/-- The set-valued sheaves form the full subcategory of presheaves. -/
abbrev Sheaves (J : Site C) :=
  ObjectProperty.FullSubcategory (SetSheaf J : Presheaf C → Prop)

/-- The full subcategory of set-valued sheaves, with the value universe
explicit so it can also be used for small topological sites. -/
abbrev SheavesOfTypes (J : Site C) :=
  ObjectProperty.FullSubcategory
    (fun F : Cᵒᵖ ⥤ Type w => SetValuedSheaf J F)

/-- The covering condition for a presieve is equivalent to the sheaf condition
for every covering family of the pretopology. -/
theorem setSheaf_iff_covering_presieves (J : Site C) (F : Presheaf C) :
    SetSheaf J F ↔
      ∀ {U : C} (R : FamilyOfMorphisms U), R ∈ coverings J U →
        IsSheafFor F R := by
  change Presieve.IsSheaf J.toGrothendieck F ↔ _
  exact Presieve.isSheaf_pretopology J

/-- Elementwise, a sheaf has a unique amalgamation for every compatible
family over every covering presieve. -/
theorem setSheaf_iff_elementwise (J : Site C) (F : Presheaf C) :
    SetSheaf J F ↔
      ∀ {U : C} (R : FamilyOfMorphisms U), R ∈ coverings J U →
        ∀ x : FamilyOfElements F R, x.Compatible →
          ∃! t, x.IsAmalgamation t := by
  rw [setSheaf_iff_covering_presieves]
  rfl

/-- The two restriction maps in the source's equalizer diagram are the
canonical maps in Mathlib's indexed-arrow fork. -/
theorem covering_restrictions_agree {I : Type w} [Small.{v} I]
    {U : C} {V : I → C} (f : ∀ i, V i ⟶ U)
    (F : Presheaf C) (s : F.obj (op U)) :
    (Equalizer.Presieve.Arrows.firstMap F V f)
          ((Equalizer.Presieve.Arrows.forkMap F V f) s) =
      (Equalizer.Presieve.Arrows.secondMap F V f)
          ((Equalizer.Presieve.Arrows.forkMap F V f) s) := by
  exact congrArg (fun q => q s) (Equalizer.Presieve.Arrows.w F V f)

/-- The source's equalizer diagram for an indexed family of arrows is the
canonical equalizer fork for `Presieve.ofArrows`. -/
theorem covering_sheaf_condition_iff_equalizer {I : Type w} [Small.{v} I]
    {U : C} {V : I → C} (f : ∀ i, V i ⟶ U) (F : Presheaf C) :
    IsSheafFor F (familyOfArrows V f) ↔
      Nonempty (IsLimit (Fork.ofι (Equalizer.Presieve.Arrows.forkMap F V f)
        (Equalizer.Presieve.Arrows.w F V f))) := by
  simpa [familyOfArrows] using
    (Equalizer.Presieve.Arrows.sheaf_condition F V f)

/-- A set-valued sheaf satisfies the displayed equalizer condition for every
covering indexed family. -/
theorem setSheaf_implies_covering_equalizer {I : Type w} [Small.{v} I]
    (J : Site C) (F : Presheaf C) {U : C} {V : I → C}
    (f : ∀ i, V i ⟶ U) (hcover : familyOfArrows V f ∈ coverings J U)
    (hF : SetSheaf J F) :
    Nonempty (IsLimit (Fork.ofι (Equalizer.Presieve.Arrows.forkMap F V f)
      (Equalizer.Presieve.Arrows.w F V f))) := by
  exact (covering_sheaf_condition_iff_equalizer f F).mp
    ((setSheaf_iff_covering_presieves J F).mp hF _ hcover)

/-- If an empty family covers `U`, then the sections over `U` form a
singleton type (equivalently, the value is terminal in `Type`). -/
theorem setSheaf_empty_cover_sections_singleton (J : Site C) (F : Presheaf C)
    {U : C} {R : FamilyOfMorphisms U} (hR : R ∈ coverings J U)
    (hEmpty : R = (⊥ : FamilyOfMorphisms U)) (hF : SetSheaf J F) :
    Nonempty (F.obj (op U)) ∧ Subsingleton (F.obj (op U)) := by
  have hR' : (⊥ : FamilyOfMorphisms U) ∈ coverings J U := by
    simpa [hEmpty] using hR
  have hFor : IsSheafFor F (⊥ : FamilyOfMorphisms U) :=
    ((setSheaf_iff_covering_presieves J F).mp hF) _ hR'
  let x : FamilyOfElements F (⊥ : FamilyOfMorphisms U) :=
    fun _ _ h => False.elim h
  have hx : x.Compatible := by
    intro Y₁ Y₂ Z g₁ g₂ f₁ f₂ h₁ h₂ _
    exact False.elim h₁
  obtain ⟨t, ht, htu⟩ := hFor x hx
  refine ⟨⟨t⟩, ?_⟩
  exact ⟨fun a b => (htu a (fun _ _ h => False.elim h)).trans
      (htu b (fun _ _ h => False.elim h)).symm⟩

/-! ## Topological examples -/

/-- On the canonical topological site, the site-theoretic definition agrees
with Mathlib's usual sheaf condition on a topological space. -/
theorem topologicalSite_setSheaf_iff {X : TopCat.{u}}
    (F : TopCat.Presheaf (Type u) X) :
    SetSheaf (topologicalSite (X : Type u)) F ↔
      TopCat.Presheaf.IsSheaf F := by
  change Presieve.IsSheaf (Opens.pretopology (X : Type u)).toGrothendieck F ↔
    Presheaf.IsSheaf (Opens.grothendieckTopology (X : Type u)) F
  rw [Opens.pretopology_toGrothendieck]
  exact (CategoryTheory.isSheaf_iff_isSheaf_of_type
    (J := Opens.grothendieckTopology (X : Type u)) (P := F)).symm

/-! ## Category-valued sheaves -/

/-- The set-valued presheaf obtained by evaluating an `A`-valued presheaf at
an object `X : A` via the Yoneda embedding. -/
def evaluatedPresheaf {A : Type u'} [Category.{v'} A]
    (F : PresheafWithValues C A) (X : A) : Cᵒᵖ ⥤ Type v' :=
  F ⋙ coyoneda.obj (op X)

/-- Mathlib's category-valued sheaf predicate, in the source's notation. -/
abbrev CategoryValuedSheaf {A : Type u'} [Category.{v'} A]
    (J : Site C) (F : PresheafWithValues C A) : Prop :=
  Presheaf.IsSheaf J.toGrothendieck F

/-- The category-valued definition is exactly the requirement that every
evaluated set-valued presheaf is a sheaf. -/
theorem categoryValuedSheaf_iff_evaluated {A : Type u'} [Category.{v'} A]
    (J : Site C) (F : PresheafWithValues C A) :
    CategoryValuedSheaf J F ↔ ∀ X : A,
      SetValuedSheaf J (evaluatedPresheaf F X) := by
  rfl

/-- Applying `Hom(X, -)` to the displayed fork gives the set-valued diagram
from the source. -/
def homEqualizerFork {A : Type u'} [Category.{v'} A]
    {E B D : A} (e : E ⟶ B) (f g : B ⟶ D) (h : e ≫ f = e ≫ g)
    (X : A) : Fork ((coyoneda.obj (op X)).map f) ((coyoneda.obj (op X)).map g) :=
  Fork.ofι ((coyoneda.obj (op X)).map e) (by
    simpa using congrArg (fun q => (coyoneda.obj (op X)).map q) h)

/-- A fork is an equalizer exactly when all representable set-valued
presheaves send it to an equalizer. -/
theorem equalizer_iff_all_hom_equalizers {A : Type u'} [Category.{v'} A]
    {E B D : A} (e : E ⟶ B) (f g : B ⟶ D) (h : e ≫ f = e ≫ g) :
    Nonempty (IsLimit (Fork.ofι e h)) ↔
      ∀ X : A, Nonempty (IsLimit (homEqualizerFork e f g h X)) := by
  sorry

/-! ## The modified topological example -/

/-- A covering family in the modified topological pretopology. -/
def nonemptyTopologicalCovering (X : Type u) [TopologicalSpace X]
    {U : Opens X} (R : FamilyOfMorphisms U) : Prop :=
  R ∈ topologicalSite X U ∧ (U ≠ (⊥ : Opens X) ∨ R ≠ (⊥ : FamilyOfMorphisms U))

/-- A modified topological covering family is nonempty. -/
theorem nonemptyTopologicalCovering_ne_bot (X : Type u) [TopologicalSpace X]
    {U : Opens X} {R : FamilyOfMorphisms U}
    (hR : nonemptyTopologicalCovering X R) : R ≠ (⊥ : FamilyOfMorphisms U) := by
  intro hbot
  rcases hR.2 with hU | hR
  · have hUset : (U : Set X) ≠ ∅ := by
      intro h
      apply hU
      ext x
      simp [h]
    obtain ⟨x, hx⟩ := Set.nonempty_iff_ne_empty.mpr hUset
    obtain ⟨V, g, hg, _⟩ := (topologicalSite_mem_iff X R).mp hR.1 x hx
    exact (bot_apply g).mp (hbot ▸ hg)
  · exact hR hbot

/-- The topological pretopology with the empty presieve removed from the
empty open. -/
def topologicalSiteWithoutEmptyCover (X : Type u) [TopologicalSpace X] :
    Site (Opens X) := by
  refine
    { coverings := fun U => {R | nonemptyTopologicalCovering X R}
      has_isos := ?_
      pullbacks := ?_
      transitive := ?_ }
  · intro U V f hf
    refine ⟨(topologicalSite X).has_isos f, ?_⟩
    rcases eq_or_ne U (⊥ : Opens X) with hU | hU
    · right
      intro hbot
      have hmem := Presieve.singleton_self f
      rw [hbot] at hmem
      exact (bot_apply f).mp hmem
    · left
      exact hU
  · intro U V f R hR
    refine ⟨pullback_family_mem (topologicalSite X) f R hR.1, ?_⟩
    rcases eq_or_ne V (⊥ : Opens X) with hV | hV
    · right
      intro hbot
      have hRne := nonemptyTopologicalCovering_ne_bot X hR
      obtain ⟨W, g, hg⟩ : ∃ (W : Opens X) (g : W ⟶ U), R g := by
        by_contra h
        apply hRne
        funext W g
        apply propext
        constructor
        · intro hg
          exact False.elim (h ⟨W, g, hg⟩)
        · intro hg
          exact False.elim hg
      have hmem := Presieve.pullbackArrows.mk (f := f) W g hg
      exact (bot_apply _).mp (hbot ▸ hmem)
    · left
      exact hV
  · intro U R T hR hT
    refine ⟨bind_family_mem (topologicalSite X) R T hR.1
      (fun Y f hf => (hT f hf).1), ?_⟩
    rcases eq_or_ne U (⊥ : Opens X) with hU | hU
    · right
      intro hbot
      have hRne := nonemptyTopologicalCovering_ne_bot X hR
      obtain ⟨Y, f, hf⟩ : ∃ (Y : Opens X) (f : Y ⟶ U), R f := by
        by_contra h
        apply hRne
        funext Y f
        apply propext
        constructor
        · intro hf
          exact False.elim (h ⟨Y, f, hf⟩)
        · intro hf
          exact False.elim hf
      have hTne := nonemptyTopologicalCovering_ne_bot X (hT f hf)
      obtain ⟨Z, g, hg⟩ : ∃ (Z : Opens X) (g : Z ⟶ Y), (T (f := f) hf) g := by
        by_contra h
        apply hTne
        funext Z g
        apply propext
        constructor
        · intro hg
          exact False.elim (h ⟨Z, g, hg⟩)
        · intro hg
          exact False.elim hg
      have hmem := Presieve.bind_comp (S := R) (R := T) f hf hg
      exact (bot_apply _).mp (hbot ▸ hmem)
    · left
      exact hU

/-- The topology on `X ⊔ {η}` whose nonempty opens are precisely
`U ∪ {η}` for opens `U` of `X`. -/
@[instance_reducible]
def adjoinedPointTopology (X : Type u) [TopologicalSpace X] :
    TopologicalSpace (X ⊕ PUnit) :=
  TopologicalSpace.generateFrom
    {S | ∃ U : Opens X,
      S = Sum.inl '' (U : Set X) ∪ ({Sum.inr PUnit.unit} : Set (X ⊕ PUnit))}

/-- The opens of the adjoined-point topology are exactly the empty set and
the opens containing the new generic point. -/
theorem adjoinedPointTopology_isOpen_iff (X : Type u) [TopologicalSpace X]
    (S : Set (X ⊕ PUnit)) :
    @IsOpen (X ⊕ PUnit) (adjoinedPointTopology X) S ↔
      S = ∅ ∨ ∃ U : Opens X,
        S = Sum.inl '' (U : Set X) ∪ ({Sum.inr PUnit.unit} : Set (X ⊕ PUnit)) := by
  sorry

/-- The Grothendieck topology of the adjoined-point space. -/
def adjoinedPointGrothendieckTopology (X : Type u) [TopologicalSpace X] :
    GrothendieckTopology (@Opens (X ⊕ PUnit) (adjoinedPointTopology X)) :=
  letI : TopologicalSpace (X ⊕ PUnit) := adjoinedPointTopology X
  Opens.grothendieckTopology (X ⊕ PUnit)

/-- The category of sheaves on the space obtained by adjoining a generic
point. -/
abbrev adjoinedPointSheaves (X : Type u) [TopologicalSpace X] :=
  CategoryTheory.Sheaf (adjoinedPointGrothendieckTopology X) (Type u)

/-- The general identification of sheaves for the modified site with sheaves
on the space obtained by adjoining a generic point. -/
theorem nonemptySite_sheaves_equiv_adjoinedPoint (X : Type u) [TopologicalSpace X] :
    Nonempty
      (SheavesOfTypes (topologicalSiteWithoutEmptyCover X) ≌
        adjoinedPointSheaves X) := by
  sorry

/-- Removing only the empty covering family leaves all presheaves as sheaves
when the underlying topological space is a singleton. -/
theorem singleton_without_empty_cover_all_presheaves (F : (Opens PUnit)ᵒᵖ ⥤ Type v) :
    Presieve.IsSheaf (topologicalSiteWithoutEmptyCover (PUnit : Type) |>.toGrothendieck) F := by
  sorry

/-- The modified singleton site has strictly more sheaves than the usual
topological site. -/
theorem singleton_without_empty_cover_has_extra_sheaf :
    ∃ F : (Opens PUnit)ᵒᵖ ⥤ Type v,
      Presieve.IsSheaf
          (topologicalSiteWithoutEmptyCover (PUnit : Type) |>.toGrothendieck) F ∧
        ¬ Presieve.IsSheaf
          (topologicalSite (PUnit : Type) |>.toGrothendieck) F := by
  sorry

/-- In the singleton case, the preceding equivalence is the source's
two-point-space description. -/
theorem singleton_without_empty_cover_equiv_two_point_space :
    Nonempty
      (SheavesOfTypes
          (topologicalSiteWithoutEmptyCover (PUnit : Type)) ≌
        adjoinedPointSheaves (PUnit : Type)) := by
  exact nonemptySite_sheaves_equiv_adjoinedPoint (PUnit : Type)

end Formalization.Books.Sites.Unit07
