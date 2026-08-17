import Formalization.Books.Categories.Unit17.CofinalAndInitialCategories
import Mathlib.Algebra.Category.Grp.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.CategoryTheory.ConnectedComponents
import Mathlib.CategoryTheory.Filtered.Basic
import Mathlib.CategoryTheory.Filtered.Connected
import Mathlib.CategoryTheory.Filtered.Final
import Mathlib.CategoryTheory.Limits.FilteredColimitCommutesFiniteLimit
import Mathlib.CategoryTheory.Limits.Shapes.FunctorToTypes
import Mathlib.CategoryTheory.Limits.Shapes.SingleObj
import Mathlib.CategoryTheory.Limits.Types.ColimitTypeFiltered
import Mathlib.CategoryTheory.Limits.Types.Filtered
import Mathlib.CategoryTheory.Quotient
import Mathlib.Data.ZMod.Basic

/-!
# Categories, Chapter 19: Filtered colimits

This file formalizes the definitions, comparison statements, examples, and
counterexamples in the `Filtered colimits` section of `books/categories.tex`.
The proofs of the substantive textbook lemmas are intentionally left for the
proof stage.
-/

namespace Formalization.Books.Categories.Unit19

open CategoryTheory
open CategoryTheory.Limits

universe u v u' v' w w'

noncomputable section

/-! ## Filtered diagrams -/

/-- A diagram is filtered when its index is nonempty, pairs of index objects
have common targets, and parallel index maps become equal after applying the
diagram.  This is the diagram-level notion used in the source. -/
def IsFilteredDiagram {I : Type u} [Category.{v} I]
    {C : Type u'} [Category.{v'} C] (M : I ⥤ C) : Prop :=
  Nonempty I ∧
    (∀ x y : I, ∃ z : I, Nonempty (x ⟶ z) ∧ Nonempty (y ⟶ z)) ∧
    (∀ {x y : I} (a b : x ⟶ y), ∃ (z : I) (c : y ⟶ z),
      M.map (a ≫ c) = M.map (b ≫ c))

/-- `Directed` is the synonymous terminology used by the source. -/
abbrev IsDirectedDiagram {I : Type u} [Category.{v} I]
    {C : Type u'} [Category.{v'} C] (M : I ⥤ C) : Prop :=
  IsFilteredDiagram M

/-- The object part of the filtered-index condition. -/
def HasCommonUpperBounds (I : Type u) [Category.{v} I] : Prop :=
  ∀ x y : I, ∃ z : I, Nonempty (x ⟶ z) ∧ Nonempty (y ⟶ z)

/-- Every span in `I` can be completed to a commuting square. -/
def HasCoconesForSpans (I : Type u) [Category.{v} I] : Prop :=
  ∀ {x y z : I} (a : x ⟶ y) (b : x ⟶ z),
    ∃ (w : I) (c : y ⟶ w) (d : z ⟶ w), a ≫ c = b ≫ d

/-- Every parallel pair in `I` has a common post-equalizer. -/
def HasParallelEqualizers (I : Type u) [Category.{v} I] : Prop :=
  ∀ {x y : I} (a b : x ⟶ y), ∃ (z : I) (c : y ⟶ z), a ≫ c = b ≫ c

/-- The source's index-category definition is Mathlib's canonical class. -/
theorem isFiltered_iff_id_isFilteredDiagram
    (I : Type u) [Category.{v} I] :
    IsFiltered I ↔ IsFilteredDiagram (𝟭 I) := by
  sorry

/-- A diagram over a filtered index category is filtered in the diagram-level
sense. -/
theorem isFilteredDiagram_of_isFiltered
    {I : Type u} [Category.{v} I]
    {C : Type u'} [Category.{v'} C] (M : I ⥤ C)
    [IsFiltered I] :
    IsFilteredDiagram M := by
  refine ⟨IsFiltered.nonempty, ?_, ?_⟩
  · intro x y
    obtain ⟨z, f, g, _⟩ := IsFilteredOrEmpty.cocone_objs x y
    exact ⟨z, ⟨f⟩, ⟨g⟩⟩
  · intro x y a b
    obtain ⟨z, c, h⟩ := IsFilteredOrEmpty.cocone_maps a b
    exact ⟨z, c, congrArg M.map h⟩

/-- The span and parallel-pair hypotheses assemble into the filtered-or-empty
index-category interface. -/
theorem isFilteredOrEmpty_of_common_upper_bounds_and_parallel
    {I : Type u} [Category.{v} I]
    (hupper : HasCommonUpperBounds I) (heq : HasParallelEqualizers I) :
    IsFilteredOrEmpty I := by
  refine { cocone_objs := ?_, cocone_maps := ?_ }
  intro x y
  obtain ⟨z, ⟨c⟩, ⟨d⟩⟩ := hupper x y
  exact ⟨z, c, d, trivial⟩
  · intro X Y f g
    exact heq f g

/-! ## The quotient filtered index category -/

/-- The canonical quotient index category identifying exactly those parallel
maps that the diagram already identifies. -/
abbrev FilteredDiagramQuotient
    {I : Type u} [Category.{v} I]
    {C : Type u'} [Category.{v'} C] (M : I ⥤ C) :=
  Quotient M.homRel

/-- The quotient projection of a filtered diagram. -/
def filteredDiagramQuotientProjection
    {I : Type u} [Category.{v} I]
    {C : Type u'} [Category.{v'} C] (M : I ⥤ C) :
    I ⥤ FilteredDiagramQuotient M :=
  Quotient.functor M.homRel

/-- The factor of a diagram through its quotient index category. -/
def filteredDiagramQuotientFactor
    {I : Type u} [Category.{v} I]
    {C : Type u'} [Category.{v'} C] (M : I ⥤ C) :
  FilteredDiagramQuotient M ⥤ C :=
  CategoryTheory.Quotient.lift M.homRel M (fun _ _ _ _ h => h)

/-- The quotient factorization is strict at the functor level. -/
theorem filteredDiagramQuotient_factorization
    {I : Type u} [Category.{v} I]
    {C : Type u'} [Category.{v'} C] (M : I ⥤ C) :
    filteredDiagramQuotientProjection M ⋙ filteredDiagramQuotientFactor M = M :=
  by simpa only [filteredDiagramQuotientProjection, filteredDiagramQuotientFactor] using
    (CategoryTheory.Quotient.lift_spec M.homRel M (fun _ _ _ _ h => h))

/-- The quotient index category is filtered when the original diagram is
filtered. -/
theorem isFiltered_filteredDiagramQuotient
    {I : Type u} [Category.{v} I]
    {C : Type u'} [Category.{v'} C] (M : I ⥤ C)
    (hM : IsFilteredDiagram M) :
    IsFiltered (FilteredDiagramQuotient M) := by
  sorry

/-- The quotient projection is final, so it preserves the relevant colimit. -/
theorem filteredDiagramQuotientProjection_isFinal
    {I : Type u} [Category.{v} I]
    {C : Type u'} [Category.{v'} C] (M : I ⥤ C)
    (hM : IsFilteredDiagram M) :
    Functor.Final (filteredDiagramQuotientProjection M) := by
  sorry

/-- Factoring a filtered diagram through the quotient does not change whether
its colimit exists. -/
theorem hasColimit_filteredDiagramQuotient_iff
    {I : Type u} [Category.{v} I]
    {C : Type u'} [Category.{v'} C] (M : I ⥤ C)
    (hM : IsFilteredDiagram M) :
    HasColimit M ↔ HasColimit (filteredDiagramQuotientFactor M) := by
  let hfinal : Functor.Final (filteredDiagramQuotientProjection M) :=
    filteredDiagramQuotientProjection_isFinal M hM
  simpa only [filteredDiagramQuotient_factorization M] using
    (@Functor.Final.hasColimit_comp_iff _ _ _ _
      (filteredDiagramQuotientProjection M) hfinal _ _
      (filteredDiagramQuotientFactor M))

/-- The canonical comparison between the two colimits after quotienting the
index category. -/
noncomputable def filteredDiagramQuotient_colimitIso
    {I : Type u} [Category.{v} I]
    {C : Type u'} [Category.{v'} C] (M : I ⥤ C)
    (hM : IsFilteredDiagram M) [HasColimit M]
    [HasColimit (filteredDiagramQuotientFactor M)] :
    colimit M ≅ colimit (filteredDiagramQuotientFactor M) := by
  let hfinal : Functor.Final (filteredDiagramQuotientProjection M) :=
    filteredDiagramQuotientProjection_isFinal M hM
  simpa only [filteredDiagramQuotient_factorization M] using
    (@Functor.Final.colimitIso _ _ _ _
      (filteredDiagramQuotientProjection M) hfinal _ _
      (filteredDiagramQuotientFactor M) inferInstance)

/-! ## Filtered colimits of sets -/

/-- The chosen set-valued colimit is the quotient of the disjoint union of
the stages; `ColimitType` is Mathlib's canonical quotient model. -/
noncomputable def filtered_colimit_quotient_equiv
    {I : Type v} [Category.{w} I] (M : I ⥤ Type u) [HasColimit M] :
    colimit M ≃ M.ColimitType :=
  Types.colimitEquivColimitType M

/-- Eventual equality in the explicit filtered-colimit presentation for a
genuinely filtered index category. -/
theorem filtered_colimit_eventual_equality_iff
    {I : Type v} [Category.{w} I] [IsFilteredOrEmpty I]
    (M : I ⥤ Type u) [HasColimit M]
    {i j : I} {x : M.obj i} {y : M.obj j} :
    colimit.ι M i x = colimit.ι M j y ↔
      ∃ (k : I) (f : i ⟶ k) (g : j ⟶ k), M.map f x = M.map g y :=
  Types.FilteredColimit.colimit_eq_iff M

/-- The same-stage form supplied by Mathlib's explicit `ColimitType`
presentation. -/
theorem filtered_colimitType_eventual_equality_iff
    {I : Type v} [Category.{w} I] [IsFiltered I]
    (M : I ⥤ Type u) {i j : I} (x : M.obj i) (y : M.obj j) :
    M.ιColimitType i x = M.ιColimitType j y ↔
      ∃ (k : I) (f : i ⟶ k) (g : j ⟶ k), M.map f x = M.map g y :=
  Functor.ιColimitType_eq_iff_of_isFiltered M x y

/-- The source's diagram-level version of eventual equality.  The extra
diagram hypothesis is weaker than an `IsFiltered` instance on `I`. -/
theorem filtered_diagram_colimit_eventual_equality_iff
    {I : Type v} [Category.{w} I] (M : I ⥤ Type u)
    (hM : IsFilteredDiagram M) [HasColimit M]
    {i j : I} {x : M.obj i} {y : M.obj j} :
    colimit.ι M i x = colimit.ι M j y ↔
      ∃ (k : I) (f : i ⟶ k) (g : j ⟶ k), M.map f x = M.map g y := by
  sorry

/-! ## Finite-limit commutation -/

/-- Filtered colimits of sets commute with finite limits. -/
noncomputable def filtered_colimit_finite_limit_iso
    {I : Type v} [Category.{w} I] [Small.{u} I] [IsFiltered I]
    {J : Type v'} [SmallCategory J] [FinCategory J]
    (M : J ⥤ I ⥤ Type u) :
    colimit (limit M) ≅ limit (colimit M.flip) :=
  colimitLimitIso M

/-- The displayed equality in the source is represented by the canonical
isomorphism; its binary-product, pullback, and equalizer cases are obtained by
specializing the finite diagram `J`. -/
theorem filtered_colimit_commutes_finite_limits
    {I : Type v} [Category.{w} I] [Small.{u} I] [IsFiltered I]
    {J : Type v'} [SmallCategory J] [FinCategory J]
    (M : J ⥤ I ⥤ Type u) :
    Nonempty (colimit (limit M) ≅ limit (colimit M.flip)) := by
  exact ⟨filtered_colimit_finite_limit_iso M⟩

/-- The increasing finite-stage diagram used for the infinite-product
counterexample: stage `i` is the set with `i + 1` elements, and the maps are
the evident inclusions. -/
def finiteStageDiagram : ℕ ⥤ Type where
  obj i := Fin (i + 1)
  map f := ↾fun x => Fin.castLE (Nat.succ_le_succ (leOfHom f)) x
  map_id := by
    intro i
    ext x
    rfl
  map_comp := by
    intro i j k f g
    ext x
    rfl

/-- The stage diagram is constant in the discrete `ℕ`-direction. -/
def infiniteProductCounterexampleDiagram : Discrete ℕ ⥤ ℕ ⥤ Type :=
  (Functor.const (Discrete ℕ)).obj finiteStageDiagram

/-- The union of the finite-stage powers, written as the type of bounded
natural-valued sequences. -/
def BoundedNaturalSequence : Type :=
  {f : ℕ → ℕ // ∃ n : ℕ, ∀ j : ℕ, f j < n + 1}

theorem infinite_product_left_is_bounded_sequences :
    Nonempty
      (colimit (limit infiniteProductCounterexampleDiagram) ≃
        BoundedNaturalSequence) := by
  sorry

theorem infinite_product_right_is_all_sequences :
    Nonempty
      (limit (colimit infiniteProductCounterexampleDiagram.flip) ≃
        (ℕ → ℕ)) := by
  sorry

/-- For the infinite discrete diagram, the two orders of taking colimits and
limits are not isomorphic: the right side contains arbitrary sequences of
natural numbers, while the left side contains only bounded sequences. -/
theorem infinite_product_colimit_limit_not_isomorphic :
    ¬ Nonempty
        (colimit (limit infiniteProductCounterexampleDiagram) ≅
          limit (colimit infiniteProductCounterexampleDiagram.flip)) := by
  sorry

/-! ## Cofinal filtered subcategories -/

/-- A full subcategory meeting every object by an outgoing arrow is filtered
and cofinal.  `P.FullSubcategory` is the canonical full-subcategory API. -/
theorem filtered_full_subcategory_isFiltered_and_isFinal
    {I : Type u} [Category.{v} I] (P : ObjectProperty I)
    [IsFiltered I]
    (hP : ∀ i : I, ∃ j : P.FullSubcategory, Nonempty (i ⟶ P.ι.obj j)) :
    IsFiltered P.FullSubcategory ∧ Functor.Final P.ι := by
  sorry

/-! ## Common upper bounds and product comparisons -/

/-- The canonical map from the colimit of pointwise products to the product
of colimits. -/
noncomputable def colimitProductComparison
    {I : Type v} [Category.{w} I] [Small.{u} I]
    (M N : I ⥤ Type u) :
    colimit (FunctorToTypes.prod M N) → colimit M × colimit N :=
  colimit.desc (FunctorToTypes.prod M N)
    { pt := colimit M × colimit N
      ι :=
        { app := fun i => ↾fun x : M.obj i × N.obj i =>
            (colimit.ι M i x.1, colimit.ι N i x.2)
          naturality := by
            intro i j f
            ext x
            change
              (colimit.ι M j (M.map f x.1), colimit.ι N j (N.map f x.2)) =
                (colimit.ι M i x.1, colimit.ι N i x.2)
            exact Prod.ext (colimit.w_apply M f x.1) (colimit.w_apply N f x.2) } }

/-- Common upper bounds make the product comparison surjective. -/
theorem colimitProductComparison_surjective
    {I : Type v} [Category.{w} I] [Small.{u} I]
    (hI : HasCommonUpperBounds I) (M N : I ⥤ Type u) :
    Function.Surjective (colimitProductComparison M N) := by
  sorry

/-- The one-object translation diagram used for the finite-product
counterexample. -/
def translationDiagram (G : Type u) [Group G] : SingleObj G ⥤ Type u where
  obj _ := G
  map g := ↾fun x => g * x
  map_id := by
    intro X
    ext x
    simp [SingleObj.id_as_one]
  map_comp := by
    intro X Y Z f g
    ext x
    change (g * f) * x = g * (f * x)
    simp [mul_assoc]

/-- The one-object translation colimit is the orbit quotient `G / G`. -/
noncomputable def translation_colimit_orbitEquiv
    (G : Type u) [Group G] :
    colimit (translationDiagram G) ≃
      MulAction.orbitRel.Quotient G G :=
  SingleObj.Types.colimitEquivQuotient (translationDiagram G)

/-- The product translation colimit is the diagonal orbit quotient of
`G × G`. -/
noncomputable def translation_product_colimit_orbitEquiv
    (G : Type u) [Group G] :
    colimit (FunctorToTypes.prod (translationDiagram G) (translationDiagram G)) ≃
      MulAction.orbitRel.Quotient G (G × G) :=
  SingleObj.Types.colimitEquivQuotient
    (FunctorToTypes.prod (translationDiagram G) (translationDiagram G))

/-- Translation identifies every point in the one-object colimit, whereas the
diagonal translation action on the product need not do so. -/
theorem translation_product_colimits_not_isomorphic
    (G : Type u) [Group G] (hG : Nontrivial G) :
    ¬ Nonempty
        (colimit (FunctorToTypes.prod (translationDiagram G) (translationDiagram G)) ≅
          colimit (translationDiagram G) × colimit (translationDiagram G)) := by
  sorry

/-! ## Abelian-group colimits viewed as sets -/

/-- The underlying set of an abelian-group colimit receives the canonical map
from the colimit of the underlying set diagram. -/
noncomputable def colimitTypeToAbelianColimit
    {I : Type v} [Category.{w} I] [Small.{u} I]
    (M : I ⥤ Ab) :
    colimit (M ⋙ (forget Ab)) → (colimit M).carrier :=
  colimit.desc _ ((forget Ab).mapCocone (colimit.cocone M))

/-- Common upper bounds make this underlying-set map surjective. -/
theorem colimitTypeToAbelianColimit_surjective
    {I : Type v} [Category.{w} I] [Small.{u} I]
    (hI : HasCommonUpperBounds I) (M : I ⥤ Ab) :
    Function.Surjective (colimitTypeToAbelianColimit M) := by
  sorry

/-! ## Connected-component decompositions -/

/-- The canonical disjoint-union decomposition of an index category into its
connected full subcategories. -/
def connectedComponentDecomposition
    {I : Type u} [Category.{v} I] :
  Decomposed I ≌ I :=
  decomposedEquiv

/-- Span completion restricts to every connected component. -/
theorem span_completion_on_connected_components
    {I : Type u} [Category.{v} I]
    (hspan : HasCoconesForSpans I)
    (j : ConnectedComponents I) :
    HasCoconesForSpans j.Component := by
  sorry

/-- The source's first decomposition lemma: the canonical disjoint union of
components is empty exactly when the index category is empty, and every
component inherits span completion. -/
theorem span_completion_connected_component_decomposition
    {I : Type u} [Category.{v} I]
    (hspan : HasCoconesForSpans I) :
    (IsEmpty I ∨ Nonempty I) ∧
      ∀ j : ConnectedComponents I, HasCoconesForSpans j.Component := by
  sorry

/-! ## Preservation of injections -/

/-- The map on type-valued colimits induced by a natural transformation. -/
noncomputable def colimitMapOfTypes
    {I : Type v} [Category.{w} I] [Small.{u} I]
    {M N : I ⥤ Type u} (α : M ⟶ N) :
    colimit M → colimit N :=
  colim.map α

/-- Span completion preserves injectivity of pointwise-injective maps of set
diagrams after taking colimits. -/
theorem colimitMapOfTypes_injective_of_span_completion
    {I : Type v} [Category.{w} I] [Small.{u} I]
    (hspan : HasCoconesForSpans I)
    {M N : I ⥤ Type u} (α : M ⟶ N)
    (hα : ∀ i : I, Function.Injective (α.app i)) :
    Function.Injective (colimitMapOfTypes α) := by
  sorry

/-- The first-summand embedding in the abelian-group counterexample. -/
def zmodTwoFirstSummand :
    AddCommGrpCat.of (ZMod 2) ⟶ AddCommGrpCat.of (ZMod 2 × ZMod 2) :=
  AddCommGrpCat.ofHom
    (AddMonoidHom.mk' (fun x => (x, 0)) (by
      intro x y
      simp))

/-- The shear automorphism used for the nontrivial element of the order-two
group in the abelian-group counterexample. -/
def zmodTwoShear :
    AddCommGrpCat.of (ZMod 2 × ZMod 2) ⟶ AddCommGrpCat.of (ZMod 2 × ZMod 2) :=
  AddCommGrpCat.ofHom
    (AddMonoidHom.mk' (fun p => (p.1 + p.2, p.2)) (by
      intro x y
      ext <;> simp [add_left_comm, add_comm]))

/-- Book-facing data for the order-two abelian-group counterexample.  The
equivalences identify the source and target with `Z/2` and
`(Z/2) × (Z/2)`, the map is the first summand, the source action is trivial,
and the nontrivial target action is the shear. -/
structure AbelianColimitInjectionCounterexample where
  Mdiagram : SingleObj (Multiplicative (ZMod 2)) ⥤ Ab
  Ndiagram : SingleObj (Multiplicative (ZMod 2)) ⥤ Ab
  α : Mdiagram ⟶ Ndiagram
  eM : Mdiagram.obj (SingleObj.star (Multiplicative (ZMod 2))) ≅
    AddCommGrpCat.of (ZMod 2)
  eN : Ndiagram.obj (SingleObj.star (Multiplicative (ZMod 2))) ≅
    AddCommGrpCat.of (ZMod 2 × ZMod 2)
  α_is_first_summand :
    eM.inv ≫ α.app _ ≫ eN.hom = zmodTwoFirstSummand
  M_action_is_trivial :
    ∀ g : Multiplicative (ZMod 2),
      eM.inv ≫ Mdiagram.map g ≫ eM.hom = 𝟙 _
  N_action_is_shear :
    eN.inv ≫ Ndiagram.map (Multiplicative.ofAdd (1 : ZMod 2)) ≫ eN.hom =
      zmodTwoShear
  pointwise_injective : ∀ i, Function.Injective (α.app i)
  colimit_map_not_injective :
    ¬ Function.Injective
      (colimitMapOfTypes
        (M := Mdiagram ⋙ forget Ab) (N := Ndiagram ⋙ forget Ab)
        (Functor.whiskerRight α (forget Ab)))

/-- The source's explicit order-two abelian-group counterexample exists. -/
theorem exists_abelian_colimit_injective_counterexample :
    Nonempty AbelianColimitInjectionCounterexample := by
  sorry

/-! ## Splitting into filtered components -/

/-- The two hypotheses in the source's filtered-component lemma. -/
def HasCommonCoconesForMorphisms (I : Type u) [Category.{v} I] : Prop :=
  ∀ {w x y : I} (a : w ⟶ x) (b : w ⟶ y),
    ∃ (z : I) (c : x ⟶ z) (d : y ⟶ z), a ≫ c = b ≫ d

/-- Under the two source hypotheses, every connected component is a filtered
index category; the canonical decomposition is the required disjoint union. -/
theorem filtered_connected_component_decomposition
    {I : Type u} [Category.{v} I]
    (hspan : HasCommonCoconesForMorphisms I)
    (heq : HasParallelEqualizers I) :
    ∀ j : ConnectedComponents I, IsFiltered j.Component := by
  sorry

/-! ## Finite connected limits for almost-directed colimits -/

/-- Colimits over an index category satisfying the two splitting hypotheses
commute with finite connected limits of sets. -/
theorem almost_directed_colimit_commutes_finite_connected_limits
    {I : Type v} [Category.{w} I] [Small.{u} I]
    (hspan : HasCommonCoconesForMorphisms I)
    (heq : HasParallelEqualizers I)
    {J : Type v'} [SmallCategory J] [FinCategory J]
    [IsConnected J] (M : J ⥤ I ⥤ Type u) :
    Nonempty (colimit (limit M) ≅ limit (colimit M.flip)) := by
  sorry

/-- The coproduct pullback and coproduct equalizer identities displayed in the
source are the set-theoretic special cases of the preceding finite connected
limit statement, including the empty coproduct case. -/
def SetFiberProduct {X Y Z : Type u} (f : X → Y) (g : Z → Y) : Type u :=
  {p : X × Z // f p.1 = g p.2}

def SetEqualizer {X Y : Type u} (f g : X → Y) : Type u :=
  {x : X // f x = g x}

def CoproductMap {J : Type v'} {A B : J → Type u}
    (f : ∀ j, A j → B j) : (Σ j, A j) → (Σ j, B j) :=
  fun x => ⟨x.1, f x.1 x.2⟩

theorem coproduct_fibreProduct_equiv
    {J : Type v'} {A B C : J → Type u}
    (f : ∀ j, A j → B j) (g : ∀ j, C j → B j) :
    Nonempty
      (SetFiberProduct (CoproductMap f) (CoproductMap g) ≃
        (Σ j, SetFiberProduct (f j) (g j))) := by
  sorry

theorem coproduct_equalizer_equiv
    {J : Type v'} {A B : J → Type u}
    (f g : ∀ j, A j → B j) :
    Nonempty
      (SetEqualizer (CoproductMap f) (CoproductMap g) ≃
        (Σ j, SetEqualizer (f j) (g j))) := by
  sorry

theorem almost_directed_colimit_commutes_fibre_products_and_equalizers
    {J : Type v'} :
    ∀ {A B C : J → Type u}
      (f : ∀ j, A j → B j) (g : ∀ j, C j → B j),
      Nonempty
        (SetFiberProduct (CoproductMap f) (CoproductMap g) ≃
          (Σ j, SetFiberProduct (f j) (g j))) ∧
      ∀ {A B : J → Type u} (f g : ∀ j, A j → B j),
        Nonempty
          (SetEqualizer (CoproductMap f) (CoproductMap g) ≃
            (Σ j, SetEqualizer (f j) (g j))) := by
  intro A B C f g
  exact ⟨coproduct_fibreProduct_equiv f g, by
    intro A B f g
    exact coproduct_equalizer_equiv f g⟩

end

end Formalization.Books.Categories.Unit19
