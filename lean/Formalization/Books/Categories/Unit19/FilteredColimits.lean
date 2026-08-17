import Formalization.Books.Categories.Unit17.CofinalAndInitialCategories
import Mathlib.Algebra.Category.Grp.Colimits
import Mathlib.CategoryTheory.ConnectedComponents
import Mathlib.CategoryTheory.Filtered.Basic
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
  constructor
  · intro h
    refine ⟨h.nonempty, ?_, ?_⟩
    · intro x y
      obtain ⟨z, f, g, _⟩ := h.cocone_objs x y
      exact ⟨z, ⟨f⟩, ⟨g⟩⟩
    · intro x y a b
      obtain ⟨z, c, h⟩ := h.cocone_maps a b
      exact ⟨z, c, congrArg (𝟭 I).map h⟩
  · rintro ⟨hne, hobj, hmap⟩
    refine { nonempty := hne, cocone_objs := ?_, cocone_maps := ?_ }
    · intro x y
      obtain ⟨z, ⟨f⟩, ⟨g⟩⟩ := hobj x y
      exact ⟨z, f, g, trivial⟩
    · intro x y a b
      obtain ⟨z, c, h⟩ := hmap a b
      exact ⟨z, c, h⟩

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
  refine
    { nonempty := Nonempty.map (fun i => (⟨i⟩ : FilteredDiagramQuotient M)) hM.1
      cocone_objs := ?_
      cocone_maps := ?_ }
  · intro x y
    obtain ⟨z, ⟨f⟩, ⟨g⟩⟩ := hM.2.1 x.as y.as
    exact ⟨⟨z⟩, Quotient.functor M.homRel |>.map f,
      Quotient.functor M.homRel |>.map g, trivial⟩
  · intro X Y f g
    refine Quot.inductionOn f (fun a => Quot.inductionOn g (fun b => ?_))
    obtain ⟨z, c, h⟩ := hM.2.2 a b
    refine ⟨⟨z⟩, Quotient.functor M.homRel |>.map c, ?_⟩
    exact Quot.sound (HomRel.CompClosure.of h)

/-- The quotient projection is final, so it preserves the relevant colimit. -/
theorem filteredDiagramQuotientProjection_isFinal
    {I : Type u} [Category.{v} I]
    {C : Type u'} [Category.{v'} C] (M : I ⥤ C)
    (hM : IsFilteredDiagram M) :
    Functor.Final (filteredDiagramQuotientProjection M) := by
  refine ⟨fun d => ?_⟩
  let hne : Nonempty (StructuredArrow d (filteredDiagramQuotientProjection M)) :=
    ⟨StructuredArrow.mk (𝟙 d)⟩
  apply @zigzag_isConnected _ _ hne
  intro X Y
  rcases X with ⟨leftX, rightX, homX⟩
  rcases Y with ⟨leftY, rightY, homY⟩
  refine Quot.inductionOn homX (fun f => Quot.inductionOn homY (fun g => ?_))
  change d.as ⟶ rightX at f
  change d.as ⟶ rightY at g
  obtain ⟨k, ⟨c⟩, ⟨e⟩⟩ := hM.2.1 rightX rightY
  obtain ⟨l, t, ht⟩ := hM.2.2 (f ≫ c) (g ≫ e)
  let q := Quotient.functor M.homRel
  let Z : StructuredArrow d q := StructuredArrow.mk (q.map ((f ≫ c) ≫ t))
  have hXY : q.map ((f ≫ c) ≫ t) = q.map ((g ≫ e) ≫ t) := by
    exact Quot.sound (HomRel.CompClosure.of ht)
  have hX : Nonempty ((⟨leftX, rightX, Quot.mk _ f⟩ :
      StructuredArrow d q) ⟶ Z) := by
    refine ⟨StructuredArrow.homMk (c ≫ t) ?_⟩
    change q.map f ≫ q.map (c ≫ t) = q.map ((f ≫ c) ≫ t)
    calc
      q.map f ≫ q.map (c ≫ t) = q.map (f ≫ (c ≫ t)) :=
        (q.map_comp f (c ≫ t)).symm
      _ = q.map ((f ≫ c) ≫ t) := by rw [Category.assoc]
  have hY : Nonempty ((⟨leftY, rightY, Quot.mk _ g⟩ :
      StructuredArrow d q) ⟶ Z) := by
    refine ⟨StructuredArrow.homMk (e ≫ t) ?_⟩
    change q.map g ≫ q.map (e ≫ t) = q.map ((f ≫ c) ≫ t)
    calc
      q.map g ≫ q.map (e ≫ t) = q.map (g ≫ (e ≫ t)) :=
        (q.map_comp g (e ≫ t)).symm
      _ = q.map ((g ≫ e) ≫ t) := by rw [Category.assoc]
      _ = q.map ((f ≫ c) ≫ t) := hXY.symm
  exact Relation.ReflTransGen.trans
    (Relation.ReflTransGen.single (Or.inl hX))
    (Relation.ReflTransGen.single (Or.inr hY))

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
  have hR : _root_.Equivalence (Types.FilteredColimit.Rel M) := {
    refl := fun p => ⟨p.1, 𝟙 _, 𝟙 _, rfl⟩
    symm := by
      intro p q hp
      rcases hp with ⟨k, f, g, h⟩
      exact ⟨k, g, f, h.symm⟩
    trans := by
      intro p q r hp hq
      rcases hp with ⟨k, f, g, h⟩
      rcases hq with ⟨k', f', g', h'⟩
      obtain ⟨l, ⟨fl⟩, ⟨gl⟩⟩ := hM.2.1 k k'
      obtain ⟨m, n, hn⟩ := hM.2.2 (g ≫ fl) (f' ≫ gl)
      refine ⟨m, f ≫ fl ≫ n, g' ≫ gl ≫ n, ?_⟩
      calc
        M.map (f ≫ fl ≫ n) p.2 = M.map (fl ≫ n) (M.map f p.2) := by simp
        _ = M.map (fl ≫ n) (M.map g q.2) := by rw [h]
        _ = M.map ((g ≫ fl) ≫ n) q.2 := by simp
        _ = M.map ((f' ≫ gl) ≫ n) q.2 := by rw [hn]
        _ = M.map (gl ≫ n) (M.map f' q.2) := by simp
        _ = M.map (gl ≫ n) (M.map g' r.2) := by rw [h']
        _ = M.map (g' ≫ gl ≫ n) r.2 := by simp
  }
  have hrel_eq :
      Types.FilteredColimit.Rel M = Relation.EqvGen M.ColimitTypeRel := by
    ext p q
    constructor
    · intro hp
      exact Types.FilteredColimit.eqvGen_colimitTypeRel_of_rel M p q hp
    · intro hp
      apply (hR.eqvGen_iff).mp
      exact Relation.EqvGen.mono
        (Types.FilteredColimit.rel_of_colimitTypeRel M) p q hp
  have hquot :
      colimit.ι M i x = colimit.ι M j y ↔
        M.ιColimitType i x = M.ιColimitType j y := by
    constructor
    · intro h
      have h' := congrArg (Types.colimitEquivColimitType M) h
      simpa only [Types.colimitEquivColimitType_apply, Functor.ιColimitType] using h'
    · intro h
      apply (Types.colimitEquivColimitType M).injective
      simpa only [Types.colimitEquivColimitType_apply, Functor.ιColimitType] using h
  rw [hquot, Functor.ιColimitType_eq_iff, ← hrel_eq]
  rfl

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
  let F := infiniteProductCounterexampleDiagram
  let L := F.flip ⋙ lim
  let e : limit F ≅ L := limitIsoFlipCompLim F
  let ePoint : ∀ i : ℕ, L.obj i ≃
      (∀ j : ℕ, (F.flip.obj i).obj (Discrete.mk j)) :=
    fun i =>
      (Types.limitEquivSections (F.flip.obj i)).trans
        { toFun := fun s j => by
            exact s.1 (Discrete.mk j)
          invFun := fun f =>
            ⟨fun d => f d.as, by
              intro d d' q
              rcases d with ⟨d⟩
              rcases d' with ⟨d'⟩
              rcases q with ⟨⟨q⟩⟩
              cases q
              rfl⟩
          left_inv := by
            intro s
            apply Subtype.ext
            funext d
            rfl
          right_inv := by
            intro f
            funext j
            rfl }
  have ePoint_apply (i : ℕ) (x : L.obj i) (j : ℕ) :
      ePoint i x j =
        (Types.limitEquivSections (F.flip.obj i) x).1 (Discrete.mk j) := by
    rfl
  let finPoint : ∀ i : ℕ, L.obj i → ℕ → Fin (i + 1) :=
    fun i x j =>
      (ePoint i x j)
  let natPoint : ∀ i : ℕ, L.obj i → ℕ → ℕ :=
    fun i x j => (finPoint i x j : ℕ)
  let cL : Cocone L :=
    { pt := BoundedNaturalSequence
      ι :=
        { app := fun i => ↾fun x =>
            ⟨fun j => natPoint i x j,
              ⟨i, fun j => by
                change natPoint i x j < i + 1
                change (finPoint i x j : ℕ) < i + 1
                exact (finPoint i x j).isLt⟩⟩
          naturality := by
            intro i j f
            ext z
            apply Subtype.ext
            funext k
            change
              natPoint j (L.map f z) k = natPoint i z k
            have h := limMap_π_apply (F.flip.map f) (Discrete.mk k) z
            have hfin : finPoint j (L.map f z) k =
                Fin.castLE (Nat.succ_le_succ (leOfHom f)) (finPoint i z k) := by
              apply Fin.ext
              have hraw : ePoint j (L.map f z) k =
                  (F.flip.map f).app (Discrete.mk k) (ePoint i z k) := by
                rw [ePoint_apply, ePoint_apply]
                exact h
              dsimp [F, infiniteProductCounterexampleDiagram, finiteStageDiagram,
                L] at hraw ⊢
              exact congrArg Fin.val hraw
            exact congrArg Fin.val hfin } }
  let c : Cocone (limit F) :=
    { pt := BoundedNaturalSequence
      ι :=
        { app := fun i => e.hom.app i ≫ cL.ι.app i
          naturality := by
            intro i j f
            simp only [Functor.const_obj_map]
            rw [← Category.assoc, e.hom.naturality, Category.assoc]
            rw [cL.ι.naturality]
            simp } }
  have hcL_inj : ∀ (i j : ℕ) (x : L.obj i) (y : L.obj j),
      cL.ι.app i x = cL.ι.app j y →
        ∃ (k : ℕ) (f : i ⟶ k) (g : j ⟶ k), L.map f x = L.map g y := by
    intro i j x y hxy
    let k := max i j
    let f : i ⟶ k := homOfLE (le_max_left _ _)
    let g : j ⟶ k := homOfLE (le_max_right _ _)
    refine ⟨k, f, g, ?_⟩
    apply (ePoint k).injective
    funext d
    apply Fin.ext
    have hxy' : natPoint i x d = natPoint j y d :=
      congrFun (congrArg Subtype.val hxy) d
    have hf := limMap_π_apply (F.flip.map f) (Discrete.mk d) x
    have hg := limMap_π_apply (F.flip.map g) (Discrete.mk d) y
    have hfinf : finPoint k (L.map f x) d =
        Fin.castLE (Nat.succ_le_succ (leOfHom f)) (finPoint i x d) := by
      apply Fin.ext
      have hraw : ePoint k (L.map f x) d =
          (F.flip.map f).app (Discrete.mk d) (ePoint i x d) := by
        rw [ePoint_apply, ePoint_apply]
        exact hf
      dsimp [F, infiniteProductCounterexampleDiagram, finiteStageDiagram, L] at hraw ⊢
      exact congrArg Fin.val hraw
    have hfing : finPoint k (L.map g y) d =
        Fin.castLE (Nat.succ_le_succ (leOfHom g)) (finPoint j y d) := by
      apply Fin.ext
      have hraw : ePoint k (L.map g y) d =
          (F.flip.map g).app (Discrete.mk d) (ePoint j y d) := by
        rw [ePoint_apply, ePoint_apply]
        exact hg
      dsimp [F, infiniteProductCounterexampleDiagram, finiteStageDiagram, L] at hraw ⊢
      exact congrArg Fin.val hraw
    calc
      natPoint k (L.map f x) d = natPoint i x d := by
        exact congrArg Fin.val hfinf
      _ = natPoint j y d := hxy'
      _ = natPoint k (L.map g y) d := by
        exact (congrArg Fin.val hfing).symm
  have hc : IsColimit c := by
    apply Types.FilteredColimit.isColimitOf (limit F) c
    · intro x
      rcases x with ⟨x, ⟨i, hi⟩⟩
      let xi : L.obj i :=
        (ePoint i).symm (fun j => ⟨x j, hi j⟩)
      refine ⟨i, e.inv.app i xi, ?_⟩
      apply Subtype.ext
      funext j
      change x j = (cL.ι.app i (e.hom.app i (e.inv.app i xi))).1 j
      have he : e.hom.app i (e.inv.app i xi) = xi := by
        exact ConcreteCategory.congr_hom (e.inv_hom_id_app i) xi
      rw [he]
      dsimp [cL]
      change x j = natPoint i xi j
      have hxi := congrArg (fun s => s j)
        ((ePoint i).apply_symm_apply (fun j => ⟨x j, hi j⟩))
      dsimp [ePoint, F, infiniteProductCounterexampleDiagram, finiteStageDiagram, L] at hxi
      exact (congrArg Fin.val hxi).symm
    · intro i j x y hxy
      change cL.ι.app i (e.hom.app i x) = cL.ι.app j (e.hom.app j y) at hxy
      obtain ⟨k, f, g, hfg⟩ :=
        hcL_inj i j (e.hom.app i x) (e.hom.app j y) hxy
      refine ⟨k, f, g, ?_⟩
      have hE : e.hom.app k ((limit F).map f x) =
          e.hom.app k ((limit F).map g y) := by
        calc
          e.hom.app k ((limit F).map f x) = L.map f (e.hom.app i x) := by
            exact ConcreteCategory.congr_hom (e.hom.naturality f) x
          _ = L.map g (e.hom.app j y) := hfg
          _ = e.hom.app k ((limit F).map g y) := by
            exact (ConcreteCategory.congr_hom (e.hom.naturality g) y).symm
      have hE' := congrArg (fun z => e.inv.app k z) hE
      simpa using hE'
  exact ⟨(IsColimit.coconePointUniqueUpToIso (colimit.isColimit (limit F)) hc).toEquiv⟩

theorem infinite_product_right_is_all_sequences :
    Nonempty
      (limit (colimit infiniteProductCounterexampleDiagram.flip) ≃
        (ℕ → ℕ)) := by
  let c : Cocone finiteStageDiagram :=
    { pt := ℕ
      ι :=
        { app := fun i => ↾fun x : Fin (i + 1) => (x : ℕ)
          naturality := by
            intro i j f
            ext x
            rfl } }
  have hc : IsColimit c :=
    Types.FilteredColimit.isColimitOf finiteStageDiagram c (by
      intro n
      refine ⟨n, ⟨n, Nat.lt_succ_self n⟩, ?_⟩
      rfl) (by
      intro i j x y h
      refine ⟨max i j, homOfLE (le_max_left _ _), homOfLE (le_max_right _ _), ?_⟩
      apply Fin.ext
      change x.val = y.val
      exact h)
  let eStage : colimit finiteStageDiagram ≃ ℕ :=
    (IsColimit.coconePointUniqueUpToIso (colimit.isColimit finiteStageDiagram) hc).toEquiv
  let ePoint : ∀ j : ℕ, (infiniteProductCounterexampleDiagram ⋙ colim).obj (Discrete.mk j) ≃ ℕ :=
    fun _ => by simpa [infiniteProductCounterexampleDiagram] using eStage
  let discreteLimitEquiv (X : Discrete ℕ ⥤ Type) :
      limit X ≃ (∀ j : ℕ, X.obj (Discrete.mk j)) :=
    (Types.limitEquivSections X).trans
      { toFun := fun s j => s.1 (Discrete.mk j)
        invFun := fun f =>
          ⟨fun d => f d.as, by
            intro d d' q
            rcases d with ⟨d⟩
            rcases d' with ⟨d'⟩
            rcases q with ⟨⟨q⟩⟩
            have hdd : d = d' := q
            cases hdd
            simp⟩
        left_inv := by
          intro s
          apply Subtype.ext
          rfl
        right_inv := by
          intro f
          funext j
          rfl }
  exact ⟨
    (HasLimit.isoOfNatIso (colimitFlipIsoCompColim infiniteProductCounterexampleDiagram)).toEquiv.trans
      ((discreteLimitEquiv (infiniteProductCounterexampleDiagram ⋙ colim)).trans
        (Equiv.piCongrRight ePoint))⟩

/-- Bounded sequences do not exhaust all natural-valued sequences: the
identity sequence is not in the image of the subtype inclusion.  This is the
set-level obstruction exhibited by the infinite-product counterexample. -/
theorem bounded_natural_sequence_inclusion_not_surjective :
    ¬ Function.Surjective
        (fun f : BoundedNaturalSequence => f.1) := by
  intro h
  obtain ⟨f, hf⟩ := h (fun n => n)
  obtain ⟨n, hn⟩ := f.2
  have hfn : f.1 (n + 1) = n + 1 := congrFun hf (n + 1)
  have hlt := hn (n + 1)
  rw [hfn] at hlt
  exact (Nat.lt_irrefl (n + 1)) hlt

/-! ## Cofinal filtered subcategories -/

/-- A full subcategory meeting every object by an outgoing arrow is filtered
and cofinal.  `P.FullSubcategory` is the canonical full-subcategory API. -/
theorem filtered_full_subcategory_isFiltered_and_isFinal
    {I : Type u} [Category.{v} I] (P : ObjectProperty I)
    [IsFiltered I]
    (hP : ∀ i : I, ∃ j : P.FullSubcategory, Nonempty (i ⟶ P.ι.obj j)) :
    IsFiltered P.FullSubcategory ∧ Functor.Final P.ι := by
  exact ⟨IsFiltered.of_exists_of_isFiltered_of_fullyFaithful P.ι hP,
    Functor.final_of_exists_of_isFiltered_of_fullyFaithful P.ι hP⟩

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
  rintro ⟨x, y⟩
  obtain ⟨i, xi, hxi⟩ := Types.jointly_surjective_of_isColimit (colimit.isColimit M) x
  obtain ⟨j, yj, hyj⟩ := Types.jointly_surjective_of_isColimit (colimit.isColimit N) y
  obtain ⟨k, ⟨f⟩, ⟨g⟩⟩ := hI i j
  let z : (FunctorToTypes.prod M N).obj k := (M.map f xi, N.map g yj)
  refine ⟨colimit.ι (FunctorToTypes.prod M N) k z, ?_⟩
  have hpair :
      (colimit.ι M k (M.map f xi), colimit.ι N k (N.map g yj)) = (x, y) :=
    Prod.ext ((colimit.w_apply M f xi).trans hxi) ((colimit.w_apply N g yj).trans hyj)
  let c : Cocone (FunctorToTypes.prod M N) :=
    { pt := colimit M × colimit N
      ι :=
        { app := fun i => ↾fun z : M.obj i × N.obj i =>
            (colimit.ι M i z.1, colimit.ι N i z.2)
          naturality := by
            intro i j q
            ext z
            change
              (colimit.ι M j (M.map q z.1), colimit.ι N j (N.map q z.2)) =
                (colimit.ι M i z.1, colimit.ι N i z.2)
            exact Prod.ext (colimit.w_apply M q z.1) (colimit.w_apply N q z.2) } }
  change
    (colimit.desc (FunctorToTypes.prod M N) c)
        (colimit.ι (FunctorToTypes.prod M N) k z) = (x, y)
  rw [colimit.ι_desc_apply]
  change (colimit.ι M k (M.map f xi), colimit.ι N k (N.map g yj)) = (x, y)
  exact hpair

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
  obtain ⟨x, y, hxy⟩ := hG.exists_pair_ne
  obtain ⟨g, hg⟩ : ∃ g : G, g ≠ 1 := by
    by_cases hx : x = 1
    · exact ⟨y, by simpa [hx] using hxy.symm⟩
    · exact ⟨x, hx⟩
  let E : colimit (translationDiagram G) ≃
      MulAction.orbitRel.Quotient G G :=
    translation_colimit_orbitEquiv G
  let Eprod : colimit (FunctorToTypes.prod (translationDiagram G) (translationDiagram G)) ≃
      MulAction.orbitRel.Quotient G (G × G) :=
    translation_product_colimit_orbitEquiv G
  let q0 : MulAction.orbitRel.Quotient G (G × G) := Quotient.mk'' (1, 1)
  let q1 : MulAction.orbitRel.Quotient G (G × G) := Quotient.mk'' (1, g)
  have hq : q0 ≠ q1 := by
    intro h
    have horb : MulAction.orbitRel G (G × G) (1, 1) (1, g) :=
      Quotient.eq''.mp h
    rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff] at horb
    rcases horb with ⟨h, hh⟩
    have hfirst : h = 1 := by
      simpa using congrArg Prod.fst hh
    have hsecond : g = 1 := by
      simpa [hfirst] using congrArg Prod.snd hh
    exact hg hsecond
  rintro ⟨e⟩
  have hsub : Subsingleton (MulAction.orbitRel.Quotient G G) :=
    (MulAction.pretransitive_iff_subsingleton_quotient G G).mp inferInstance
  have heq : e.hom (Eprod.symm q0) = e.hom (Eprod.symm q1) := by
    apply Prod.ext
    · apply E.injective
      exact @Subsingleton.elim _ hsub _ _
    · apply E.injective
      exact @Subsingleton.elim _ hsub _ _
  have hs : Eprod.symm q0 = Eprod.symm q1 := by
    have hs' := congrArg (fun z => e.inv z) heq
    simpa using hs'
  apply hq
  have := congrArg Eprod hs
  simpa using this

/-! ## Abelian-group colimits viewed as sets -/

/-- The underlying set of an abelian-group colimit receives the canonical map
from the colimit of the underlying set diagram. -/
noncomputable def colimitTypeToAbelianColimit
    {I : Type v} [Category.{w} I] [Small.{u} I]
    (M : I ⥤ Ab) :
    colimit (M ⋙ (forget Ab)) → (colimit M).carrier :=
  colimit.desc _ ((forget Ab).mapCocone (colimit.cocone M))

/-- Common upper bounds and a nonempty index make this underlying-set map
surjective. -/
theorem colimitTypeToAbelianColimit_surjective
    {I : Type v} [Category.{w} I] [Small.{u} I]
    (hI : HasCommonUpperBounds I) (hI_nonempty : Nonempty I) (M : I ⥤ Ab) :
    Function.Surjective (colimitTypeToAbelianColimit M) := by
  classical
  let S : AddSubgroup (colimit M).carrier :=
    { carrier := {x | ∃ (i : I) (y : M.obj i), colimit.ι M i y = x}
      zero_mem' := by
        obtain ⟨i⟩ := hI_nonempty
        exact ⟨i, 0, by simp⟩
      add_mem' := by
        rintro x y ⟨i, a, rfl⟩ ⟨j, b, rfl⟩
        obtain ⟨k, ⟨f⟩, ⟨g⟩⟩ := hI i j
        refine ⟨k, M.map f a + M.map g b, ?_⟩
        simp only [map_add]
        rw [colimit.w_apply, colimit.w_apply]
      neg_mem' := by
        rintro x ⟨i, a, rfl⟩
        exact ⟨i, -a, by simp⟩ }
  have hS : S = ⊤ := by
    apply top_unique
    intro x _
    let q : (colimit M).carrier →+ (colimit M).carrier ⧸ S :=
      QuotientAddGroup.mk' S
    let qcat : colimit M ⟶ AddCommGrpCat.of ((colimit M).carrier ⧸ S) :=
      AddCommGrpCat.ofHom q
    have hqcat : qcat = 0 := by
      apply (colimit.isColimit M).hom_ext
      intro i
      ext y
      change q (colimit.ι M i y) = 0
      change ((↑(colimit.ι M i y) : (colimit M).carrier ⧸ S) = 0)
      rw [QuotientAddGroup.eq_zero_iff]
      exact ⟨i, y, rfl⟩
    have hqx : q x = 0 := by
      have h := congrArg (fun f => f.hom x) hqcat
      exact h
    change ((↑x : (colimit M).carrier ⧸ S) = 0) at hqx
    exact (QuotientAddGroup.eq_zero_iff (N := S) x).mp hqx
  intro x
  have hx : x ∈ S := by
    rw [hS]
    trivial
  rcases hx with ⟨i, y, rfl⟩
  refine ⟨colimit.ι (M ⋙ (forget Ab)) i y, ?_⟩
  change
    colimit.desc (M ⋙ (forget Ab)) ((forget Ab).mapCocone (colimit.cocone M))
        (colimit.ι (M ⋙ (forget Ab)) i y) = colimit.ι M i y
  rw [colimit.ι_desc_apply]
  rfl

/-! ## Connected-component decompositions -/

/- The canonical decomposition into connected full subcategories is already
   provided by Mathlib's `decomposedEquiv`; the results below add the source's
   hypotheses on that established decomposition. -/

/-- Span completion restricts to every connected component. -/
theorem span_completion_on_connected_components
    {I : Type u} [Category.{v} I]
    (hspan : HasCoconesForSpans I)
    (j : ConnectedComponents I) :
    HasCoconesForSpans j.Component := by
  intro x y z a b
  obtain ⟨w, c, d, h⟩ := hspan a.1 b.1
  have hyw :
      (@Quotient.mk'' I (Zigzag.setoid I) y.1 : ConnectedComponents I) =
        Quotient.mk'' w :=
    Quotient.sound' (Zigzag.of_hom c)
  have hw : Quotient.mk'' w = j := hyw.symm.trans y.2
  refine ⟨⟨w, hw⟩, ⟨c⟩, ⟨d⟩, ?_⟩
  apply ObjectProperty.hom_ext
  exact h

/-- The source's first decomposition lemma: the canonical disjoint union of
components is empty exactly when the index category is empty, and every
component inherits span completion. -/
theorem span_completion_connected_component_decomposition
    {I : Type u} [Category.{v} I]
    (hspan : HasCoconesForSpans I) :
    (IsEmpty I ∨ Nonempty I) ∧
      ∀ j : ConnectedComponents I, HasCoconesForSpans j.Component := by
  exact ⟨isEmpty_or_nonempty I, fun j => span_completion_on_connected_components hspan j⟩

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
  have hrel_eq : ∀ F : I ⥤ Type u,
      Types.FilteredColimit.Rel F = Relation.EqvGen F.ColimitTypeRel := by
    intro F
    have hR : _root_.Equivalence (Types.FilteredColimit.Rel F) := {
      refl := fun p => ⟨p.1, 𝟙 _, 𝟙 _, rfl⟩
      symm := by
        intro p q hp
        rcases hp with ⟨k, f, g, h⟩
        exact ⟨k, g, f, h.symm⟩
      trans := by
        intro p q r hp hq
        rcases hp with ⟨k, f, g, h⟩
        rcases hq with ⟨k', f', g', h'⟩
        obtain ⟨l, a, b, hab⟩ := hspan g f'
        refine ⟨l, f ≫ a, g' ≫ b, ?_⟩
        calc
          F.map (f ≫ a) p.2 = F.map a (F.map f p.2) := by simp
          _ = F.map a (F.map g q.2) := by rw [h]
          _ = F.map (g ≫ a) q.2 := by simp
          _ = F.map (f' ≫ b) q.2 := by rw [hab]
          _ = F.map b (F.map f' q.2) := by simp
          _ = F.map b (F.map g' r.2) := by rw [h']
          _ = F.map (g' ≫ b) r.2 := by simp }
    ext p q
    constructor
    · intro hp
      exact Types.FilteredColimit.eqvGen_colimitTypeRel_of_rel F p q hp
    · intro hp
      apply (hR.eqvGen_iff).mp
      exact Relation.EqvGen.mono
        (Types.FilteredColimit.rel_of_colimitTypeRel F) p q hp
  intro a b hab
  obtain ⟨i, x, hx⟩ := Types.jointly_surjective_of_isColimit (colimit.isColimit M) a
  obtain ⟨j, y, hy⟩ := Types.jointly_surjective_of_isColimit (colimit.isColimit M) b
  have hab0 := hab
  rw [← hx, ← hy] at hab0
  change colim.map α (colimit.ι M i x) = colim.map α (colimit.ι M j y) at hab0
  have hab' :
      colimit.ι N i (α.app i x) = colimit.ι N j (α.app j y) := by
    exact (colimit.ι_map_apply α i x).symm.trans
      (hab0.trans (colimit.ι_map_apply α j y))
  have hNrel : Types.FilteredColimit.Rel N ⟨i, α.app i x⟩ ⟨j, α.app j y⟩ := by
    rw [hrel_eq N]
    exact Types.colimit_eq hab'
  rcases hNrel with ⟨k, f, g, h⟩
  have hαk : α.app k (M.map f x) = α.app k (M.map g y) := by
    calc
      α.app k (M.map f x) = N.map f (α.app i x) :=
        ConcreteCategory.congr_hom (α.naturality f) x
      _ = N.map g (α.app j y) := h
      _ = α.app k (M.map g y) := (ConcreteCategory.congr_hom (α.naturality g) y).symm
  have hMrel : Types.FilteredColimit.Rel M ⟨i, x⟩ ⟨j, y⟩ :=
    ⟨k, f, g, hα k hαk⟩
  have hMgen : Relation.EqvGen M.ColimitTypeRel ⟨i, x⟩ ⟨j, y⟩ := by
    rw [← hrel_eq M]
    exact hMrel
  have hMquot : M.ιColimitType i x = M.ιColimitType j y :=
    (Functor.ιColimitType_eq_iff _ _ _).2 hMgen
  apply (Types.colimitEquivColimitType M).injective
  rw [← hx, ← hy]
  change
    (Types.colimitEquivColimitType M) (colimit.ι M i x) =
      (Types.colimitEquivColimitType M) (colimit.ι M j y)
  rw [Types.colimitEquivColimitType_apply, Types.colimitEquivColimitType_apply]
  change M.ιColimitType i x = M.ιColimitType j y
  exact hMquot

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
  /-- The induced map on colimits in `Ab` is not injective (indeed, it is zero). -/
  colimit_map_not_injective :
    ¬ Function.Injective (colim.map α)
  colimit_map_is_zero : colim.map α = 0

/-- The source's explicit order-two abelian-group counterexample exists. -/
theorem exists_abelian_colimit_injective_counterexample :
    Nonempty AbelianColimitInjectionCounterexample := by
  let G := Multiplicative (ZMod 2)
  let Mdiagram : SingleObj G ⥤ Ab :=
    { obj _ := AddCommGrpCat.of (ZMod 2)
      map _ := 𝟙 _
      map_id := by simp
      map_comp := by intros; simp }
  let Nmap (g : G) :
      AddCommGrpCat.of (ZMod 2 × ZMod 2) ⟶ AddCommGrpCat.of (ZMod 2 × ZMod 2) :=
    AddCommGrpCat.ofHom
      (AddMonoidHom.mk' (fun p => (p.1 + g.toAdd * p.2, p.2)) (by
        intro p q
        ext <;> simp [mul_add, add_assoc, add_left_comm]))
  let Ndiagram : SingleObj G ⥤ Ab :=
    { obj _ := AddCommGrpCat.of (ZMod 2 × ZMod 2)
      map g := Nmap g
      map_id := by
        intro X
        ext p
        all_goals dsimp [Nmap, AddMonoidHom.mk']
        all_goals simp [SingleObj.id_as_one]
      map_comp := by
        intro X Y Z f g
        ext p <;> dsimp [Nmap, AddMonoidHom.mk']
        · change p.1 + (f ≫ g).toAdd * p.2 =
            p.1 + f.toAdd * p.2 + g.toAdd * p.2
          change p.1 + (g.toAdd + f.toAdd) * p.2 =
            p.1 + f.toAdd * p.2 + g.toAdd * p.2
          ring }
  let α : Mdiagram ⟶ Ndiagram :=
    { app _ := zmodTwoFirstSummand
      naturality := by
        intro X Y f
        ext x <;>
          simp [Mdiagram, Ndiagram, Nmap, zmodTwoFirstSummand,
            AddMonoidHom.mk'] }
  have hkill : ∀ x : ZMod 2,
      colimit.ι Ndiagram (SingleObj.star G) (x, 0) = 0 := by
    intro x
    have hw := colimit.w_apply Ndiagram
      (j := SingleObj.star G) (j' := SingleObj.star G)
      (Multiplicative.ofAdd (1 : ZMod 2)) (0, x)
    have hw' :
        colimit.ι Ndiagram (SingleObj.star G) (x, x) =
          colimit.ι Ndiagram (SingleObj.star G) (0, x) := by
      simpa [Ndiagram, Nmap] using hw
    have hsum :
        colimit.ι Ndiagram (SingleObj.star G) (x, 0) +
            colimit.ι Ndiagram (SingleObj.star G) (0, x) =
          colimit.ι Ndiagram (SingleObj.star G) (0, x) := by
      calc
        colimit.ι Ndiagram (SingleObj.star G) (x, 0) +
              colimit.ι Ndiagram (SingleObj.star G) (0, x) =
        colimit.ι Ndiagram (SingleObj.star G) ((x, 0) + (0, x)) := by
              rw [map_add]
        _ = colimit.ι Ndiagram (SingleObj.star G) (x, x) := by
          rw [show (x, 0) + (0, x) = (x, x) by ext <;> simp]
        _ = colimit.ι Ndiagram (SingleObj.star G) (0, x) := hw'
    apply add_right_cancel (b := colimit.ι Ndiagram (SingleObj.star G) (0, x))
    simpa using hsum
  have hzero : colim.map α = 0 := by
    apply (colimit.isColimit Mdiagram).hom_ext
    intro i
    change colimit.ι Mdiagram i ≫ colim.map α = colimit.ι Mdiagram i ≫ 0
    rw [colimit.ι_map]
    ext x
    have hi : i = SingleObj.star G := Subsingleton.elim _ _
    subst i
    simpa [α, zmodTwoFirstSummand, G] using hkill x
  let cM : Cocone Mdiagram :=
    { pt := AddCommGrpCat.of (ZMod 2)
      ι :=
        { app := fun _ => 𝟙 _
          naturality := by
            intros
            change 𝟙 _ ≫ 𝟙 _ = 𝟙 _ ≫ 𝟙 _
            simp } }
  let dM : colimit Mdiagram ⟶ AddCommGrpCat.of (ZMod 2) :=
    (colimit.isColimit Mdiagram).desc cM
  have hMne :
      colimit.ι Mdiagram (SingleObj.star G) (1 : ZMod 2) ≠
        colimit.ι Mdiagram (SingleObj.star G) 0 := by
    intro h
    have h1 : dM.hom (colimit.ι Mdiagram (SingleObj.star G) (1 : ZMod 2)) = 1 := by
      have hf := ConcreteCategory.congr_hom
        ((colimit.isColimit Mdiagram).fac cM (SingleObj.star G)) (1 : ZMod 2)
      convert hf using 1 <;> simp [cM, dM]
    have h0 : dM.hom (colimit.ι Mdiagram (SingleObj.star G) 0) = 0 := by
      have hf := ConcreteCategory.congr_hom
        ((colimit.isColimit Mdiagram).fac cM (SingleObj.star G)) (0 : ZMod 2)
      convert hf using 1 <;> simp [cM, dM]
    have := congrArg dM.hom h
    rw [h1, h0] at this
    exact one_ne_zero this
  refine ⟨
    { Mdiagram := Mdiagram
      Ndiagram := Ndiagram
      α := α
      eM := Iso.refl _
      eN := Iso.refl _
      α_is_first_summand := by
        change 𝟙 _ ≫ zmodTwoFirstSummand = zmodTwoFirstSummand
        rw [Category.id_comp]
      M_action_is_trivial := by
        intro g
        change 𝟙 _ ≫ 𝟙 _ ≫ 𝟙 _ = 𝟙 _
        simp
      N_action_is_shear := by
        simp only [Iso.refl_inv, Iso.refl_hom]
        rw [Category.id_comp, Category.comp_id]
        change Ndiagram.map (Multiplicative.ofAdd (1 : ZMod 2)) = zmodTwoShear
        ext p
        all_goals dsimp [Ndiagram, Nmap, zmodTwoShear, AddMonoidHom.mk']
        all_goals simp
      pointwise_injective := by
        intro i x y hxy
        exact congrArg Prod.fst hxy
      colimit_map_not_injective := by
        intro hinj
        apply hMne
        apply hinj
        rw [hzero]
        simp
      colimit_map_is_zero := hzero }⟩

/-! ## Splitting into filtered components -/

/-- Under the two source hypotheses, every connected component is a filtered
index category; the canonical decomposition is the required disjoint union. -/
theorem filtered_connected_component_decomposition
    {I : Type u} [Category.{v} I]
    (hspan : HasCoconesForSpans I)
    (heq : HasParallelEqualizers I) :
    ∀ j : ConnectedComponents I, IsFiltered j.Component := by
  have common_of_zigzag : ∀ {a b : I}, Zigzag a b →
      ∃ (w : I) (f : a ⟶ w) (g : b ⟶ w), True := by
    intro a b hab
    induction hab with
    | refl => exact ⟨a, 𝟙 _, 𝟙 _, trivial⟩
    | @tail b c hab hbc ih =>
        rcases ih with ⟨w, f, g, _⟩
        rcases hbc with ⟨⟨hbc⟩⟩ | ⟨⟨hcb⟩⟩
        · obtain ⟨u, p, q, hpq⟩ :=
            hspan (x := b) (y := w) (z := c) g hbc
          refine ⟨u, f ≫ p, ?_, trivial⟩
          exact q
        · exact ⟨w, f, hcb ≫ g, trivial⟩
  intro j
  refine
    { nonempty := inferInstance
      cocone_objs := ?_
      cocone_maps := ?_ }
  · intro x y
    have hxy : Zigzag x.1 y.1 := Quotient.exact' (x.2.trans y.2.symm)
    obtain ⟨w, f, g, _⟩ := common_of_zigzag hxy
    have hw : Quotient.mk'' w = j :=
      (Quotient.sound' (Zigzag.of_hom f)).symm.trans x.2
    exact ⟨⟨w, hw⟩, ⟨f⟩, ⟨g⟩, trivial⟩
  · intro x y a b
    obtain ⟨z, c, h⟩ := heq a.1 b.1
    have hz : Quotient.mk'' z = j :=
      (Quotient.sound' (Zigzag.of_hom c)).symm.trans y.2
    refine ⟨⟨z, hz⟩, ⟨c⟩, ?_⟩
    apply ObjectProperty.hom_ext
    exact h

/-- Span completion alone gives the eventual-equality description of a
type-valued colimit.  Parallel equalizers are only needed to make each
connected component filtered. -/
theorem almost_directed_colimit_eventual_equality_iff
    {I : Type v} [Category.{w} I] [Small.{u} I]
    (hspan : HasCoconesForSpans I) (F : I ⥤ Type u)
    {i j : I} {x : F.obj i} {y : F.obj j} :
    colimit.ι F i x = colimit.ι F j y ↔
      ∃ (k : I) (f : i ⟶ k) (g : j ⟶ k), F.map f x = F.map g y := by
  have hrel_eq : Types.FilteredColimit.Rel F = Relation.EqvGen F.ColimitTypeRel := by
    have hR : _root_.Equivalence (Types.FilteredColimit.Rel F) := {
      refl := fun p => ⟨p.1, 𝟙 _, 𝟙 _, rfl⟩
      symm := by
        intro p q hp
        rcases hp with ⟨k, f, g, h⟩
        exact ⟨k, g, f, h.symm⟩
      trans := by
        intro p q r hp hq
        rcases hp with ⟨k, f, g, h⟩
        rcases hq with ⟨k', f', g', h'⟩
        obtain ⟨l, a, b, hab⟩ := hspan g f'
        refine ⟨l, f ≫ a, g' ≫ b, ?_⟩
        calc
          F.map (f ≫ a) p.2 = F.map a (F.map f p.2) := by simp
          _ = F.map a (F.map g q.2) := by rw [h]
          _ = F.map (g ≫ a) q.2 := by simp
          _ = F.map (f' ≫ b) q.2 := by rw [hab]
          _ = F.map b (F.map f' q.2) := by simp
          _ = F.map b (F.map g' r.2) := by rw [h']
          _ = F.map (g' ≫ b) r.2 := by simp }
    ext p q
    constructor
    · intro hp
      exact Types.FilteredColimit.eqvGen_colimitTypeRel_of_rel F p q hp
    · intro hp
      apply (hR.eqvGen_iff).mp
      exact Relation.EqvGen.mono
        (Types.FilteredColimit.rel_of_colimitTypeRel F) p q hp
  have hquot :
      colimit.ι F i x = colimit.ι F j y ↔
        F.ιColimitType i x = F.ιColimitType j y := by
    constructor
    · intro h
      have h' := congrArg (Types.colimitEquivColimitType F) h
      simpa only [Types.colimitEquivColimitType_apply, Functor.ιColimitType] using h'
    · intro h
      apply (Types.colimitEquivColimitType F).injective
      simpa only [Types.colimitEquivColimitType_apply, Functor.ιColimitType] using h
  rw [hquot, Functor.ιColimitType_eq_iff, ← hrel_eq]
  rfl

/-! ## Finite connected limits for almost-directed colimits -/

/-- Colimits over an index category satisfying the two splitting hypotheses
commute with finite connected limits of sets. -/
theorem almost_directed_colimit_commutes_finite_connected_limits
    {I : Type v} [Category.{w} I] [Small.{u} I]
    (hspan : HasCoconesForSpans I)
    (heq : HasParallelEqualizers I)
    {J : Type v'} [SmallCategory J] [FinCategory J]
    [IsConnected J] (M : J ⥤ I ⥤ Type u) :
    Nonempty (colimit (limit M) ≅ limit (colimit M.flip)) := by
  classical
  let P : J × I ⥤ Type u := Functor.uncurry.obj M
  have hq_inj : Function.Injective (colimitLimitToLimitColimit P) := by
    cases nonempty_fintype J
    intro x y hxy
    obtain ⟨kx, x, rfl⟩ := Types.jointly_surjective' x
    obtain ⟨ky, y, rfl⟩ := Types.jointly_surjective' y
    dsimp at x y
    have h (j : J) :
        colimit.ι ((Functor.curry.obj P).obj j) kx
          ((limit.π ((Functor.curry.obj (CategoryTheory.Prod.swap I J ⋙ P)).obj kx) j) x) =
        colimit.ι ((Functor.curry.obj P).obj j) ky
          ((limit.π ((Functor.curry.obj (CategoryTheory.Prod.swap I J ⋙ P)).obj ky) j) y) := by
      simpa using! ConcreteCategory.congr_arg
        (limit.π (Functor.curry.obj P ⋙ colim) j) hxy
    have h' (j : J) :
        ∃ (k : I) (f : kx ⟶ k) (g : ky ⟶ k),
          ((Functor.curry.obj P).obj j).map f
              ((limit.π ((Functor.curry.obj (CategoryTheory.Prod.swap I J ⋙ P)).obj kx) j) x) =
            ((Functor.curry.obj P).obj j).map g
              ((limit.π ((Functor.curry.obj (CategoryTheory.Prod.swap I J ⋙ P)).obj ky) j) y) :=
      (almost_directed_colimit_eventual_equality_iff hspan
        ((Functor.curry.obj P).obj j)).mp (h j)
    let k (j : J) := (h' j).choose
    let f : ∀ j, kx ⟶ k j := fun j => (h' j).choose_spec.choose
    let g : ∀ j, ky ⟶ k j := fun j => (h' j).choose_spec.choose_spec.choose
    have w :
        ∀ j, P.map (CategoryTheory.Prod.mkHom (𝟙 j) (f j))
            ((limit.π ((Functor.curry.obj (CategoryTheory.Prod.swap I J ⋙ P)).obj kx) j) x) =
          P.map (CategoryTheory.Prod.mkHom (𝟙 j) (g j))
            ((limit.π ((Functor.curry.obj (CategoryTheory.Prod.swap I J ⋙ P)).obj ky) j) y) :=
      fun j => (h' j).choose_spec.choose_spec.choose_spec
    let j₀ : J := Classical.choice (inferInstance : Nonempty J)
    let comp : ConnectedComponents I := Quotient.mk'' kx
    let hfiltered : IsFiltered comp.Component :=
      filtered_connected_component_decomposition hspan heq comp
    let hfilteredOrEmpty : IsFilteredOrEmpty comp.Component := IsFiltered.toIsFilteredOrEmpty
    have hk (j : J) : Quotient.mk'' (k j) = comp := by
      simpa [comp] using (Quotient.sound' (Zigzag.of_hom (f j))).symm
    have hky : Quotient.mk'' ky = comp := by
      exact (Quotient.sound' (Zigzag.of_hom (g j₀))).trans (hk j₀)
    let kx' : comp.Component := ⟨kx, rfl⟩
    let ky' : comp.Component := ⟨ky, hky⟩
    let k' (j : J) : comp.Component := ⟨k j, hk j⟩
    let ff (j : J) : kx' ⟶ k' j := ObjectProperty.homMk (f j)
    let gg (j : J) : ky' ⟶ k' j := ObjectProperty.homMk (g j)
    let O : Finset comp.Component := Finset.univ.image k' ∪ {kx', ky'}
    have kxO : kx' ∈ O := Finset.mem_union.mpr (Or.inr (by simp))
    have kyO : ky' ∈ O := Finset.mem_union.mpr (Or.inr (by simp))
    have kjO : ∀ j, k' j ∈ O := fun j => Finset.mem_union.mpr (Or.inl (by simp))
    let H : Finset
        (Σ' (X Y : comp.Component) (_ : X ∈ O) (_ : Y ∈ O), X ⟶ Y) :=
      Finset.univ.image (fun j : J =>
        ⟨kx', k' j, kxO, kjO j, ff j⟩) ∪
      Finset.univ.image (fun j : J =>
        ⟨ky', k' j, kyO, kjO j, gg j⟩)
    obtain ⟨S, T, W⟩ := IsFiltered.sup_exists O H
    have fH : ∀ j, (⟨kx', k' j, kxO, kjO j, ff j⟩ :
        Σ' (X Y : comp.Component) (_ : X ∈ O) (_ : Y ∈ O), X ⟶ Y) ∈ H := fun j =>
      Finset.mem_union.mpr (Or.inl (by
        simp only [Finset.mem_univ, Finset.mem_image]
        exact ⟨j, trivial, rfl⟩))
    have gH : ∀ j, (⟨ky', k' j, kyO, kjO j, gg j⟩ :
        Σ' (X Y : comp.Component) (_ : X ∈ O) (_ : Y ∈ O), X ⟶ Y) ∈ H := fun j =>
      Finset.mem_union.mpr (Or.inr (by
        simp only [Finset.mem_univ, Finset.mem_image]
        exact ⟨j, trivial, rfl⟩))
    have hWf (j : J) : f j ≫ (T (kjO j)).hom = (T kxO).hom := by
      simpa [ff] using congrArg (fun q => q.hom) (W _ _ (fH j))
    have hWg (j : J) : g j ≫ (T (kjO j)).hom = (T kyO).hom := by
      simpa [gg] using congrArg (fun q => q.hom) (W _ _ (gH j))
    apply Types.colimit_sound' (T kxO).hom (T kyO).hom
    ext j
    simp only [Functor.comp_map]
    rw [← hWf j, ← hWg j]
    simpa using! congrArg _ (w j)
  have hq_surj : Function.Surjective (colimitLimitToLimitColimit P) := by
    intro z
    have zrep := fun j => Types.jointly_surjective'
      (limit.π (Functor.curry.obj P ⋙ colim) j z)
    let k : J → I := fun j => (zrep j).choose
    let y : ∀ j, P.obj (j, k j) := fun j => (zrep j).choose_spec.choose
    have e : ∀ j,
        colimit.ι ((Functor.curry.obj P).obj j) (k j) (y j) =
          limit.π (Functor.curry.obj P ⋙ colim) j z :=
      fun j => (zrep j).choose_spec.choose_spec
    have hcoh : ∀ {j j' : J} (f : j ⟶ j'),
        colimit.ι ((Functor.curry.obj P).obj j') (k j') (y j') =
          colimit.ι ((Functor.curry.obj P).obj j') (k j)
            (P.map (CategoryTheory.Prod.mkHom f (𝟙 (k j))) (y j)) := by
      intro j j' f
      calc
        colimit.ι ((Functor.curry.obj P).obj j') (k j') (y j') =
            limit.π (Functor.curry.obj P ⋙ colim) j' z := e j'
        _ = colim.map ((Functor.curry.obj P).map f)
              (limit.π (Functor.curry.obj P ⋙ colim) j z) := by
          symm
          exact ConcreteCategory.congr_hom
            (limit.w (Functor.curry.obj P ⋙ colim) f) z
        _ = colim.map ((Functor.curry.obj P).map f)
              (colimit.ι ((Functor.curry.obj P).obj j) (k j) (y j)) := by rw [e j]
        _ = colimit.ι ((Functor.curry.obj P).obj j') (k j)
              (((Functor.curry.obj P).map f).app (k j) (y j)) := by
          exact ConcreteCategory.congr_hom
            (colimit.ι_map ((Functor.curry.obj P).map f) (k j)) (y j)
        _ = colimit.ι ((Functor.curry.obj P).obj j') (k j)
              (P.map (CategoryTheory.Prod.mkHom f (𝟙 (k j))) (y j)) := by
          rfl
    let j₀ : J := Classical.choice (inferInstance : Nonempty J)
    have hcomp_hom {j j' : J} (f : j ⟶ j') :
        (@Quotient.mk'' I (Zigzag.setoid I) (k j) : ConnectedComponents I) =
          Quotient.mk'' (k j') := by
      obtain ⟨l, a, b, hab⟩ :=
        (almost_directed_colimit_eventual_equality_iff hspan
          ((Functor.curry.obj P).obj j')).mp (hcoh f)
      exact (Quotient.sound' (Zigzag.of_hom b)).trans
        (Quotient.sound' (Zigzag.of_hom a)).symm
    let comp : ConnectedComponents I := Quotient.mk'' (k j₀)
    have hk (j : J) : Quotient.mk'' (k j) = comp := by
      induction isPreconnected_zigzag j₀ j with
      | refl => rfl
      | @tail b c hab hbc ih =>
          rcases hbc with ⟨⟨hbc⟩⟩ | ⟨⟨hcb⟩⟩
          · exact (hcomp_hom (j := b) (j' := c) hbc).symm.trans ih
          · exact (hcomp_hom (j := c) (j' := b) hcb).trans ih
    let hfiltered : IsFiltered comp.Component :=
      filtered_connected_component_decomposition hspan heq comp
    let hfilteredOrEmpty : IsFilteredOrEmpty comp.Component := IsFiltered.toIsFilteredOrEmpty
    let kObj (j : J) : comp.Component := ⟨k j, hk j⟩
    let O : Finset comp.Component := Finset.univ.image kObj
    let k' : comp.Component := IsFiltered.sup O ∅
    let g (j : J) : kObj j ⟶ k' :=
      IsFiltered.toSup O ∅ (by simp [O])
    have w {j j' : J} (f : j ⟶ j') :
        colimit.ι ((Functor.curry.obj P).obj j') k'.obj
            (P.map (CategoryTheory.Prod.mkHom (𝟙 j') (g j').hom) (y j')) =
          colimit.ι ((Functor.curry.obj P).obj j') k'.obj
            (P.map (CategoryTheory.Prod.mkHom f (g j).hom) (y j)) := by
      calc
        colimit.ι ((Functor.curry.obj P).obj j') k'.obj
            (P.map (CategoryTheory.Prod.mkHom (𝟙 j') (g j').hom) (y j')) =
            colimit.ι ((Functor.curry.obj P).obj j') (k j') (y j') := by
          simpa using colimit.w_apply ((Functor.curry.obj P).obj j') (g j').hom (y j')
        _ = colimit.ι ((Functor.curry.obj P).obj j') (k j)
            (P.map (CategoryTheory.Prod.mkHom f (𝟙 (k j))) (y j)) := hcoh f
        _ = colimit.ι ((Functor.curry.obj P).obj j') k'.obj
            (((Functor.curry.obj P).obj j').map (g j).hom
              (P.map (CategoryTheory.Prod.mkHom f (𝟙 (k j))) (y j))) := by
          rw [colimit.w_apply]
        _ = colimit.ι ((Functor.curry.obj P).obj j') k'.obj
            (P.map (CategoryTheory.Prod.mkHom f (g j).hom) (y j)) := by
          congr 1
          change
            P.map (CategoryTheory.Prod.mkHom (𝟙 j') (g j).hom)
                (P.map (CategoryTheory.Prod.mkHom f (𝟙 (k j))) (y j)) =
              P.map (CategoryTheory.Prod.mkHom f (g j).hom) (y j)
          rw [← comp_apply, ← Functor.map_comp, CategoryTheory.prod_comp,
            Category.comp_id, Category.id_comp]
    have wrel {j j' : J} (f : j ⟶ j') :
        ∃ (l : I) (a : k'.obj ⟶ l) (b : k'.obj ⟶ l),
          ((Functor.curry.obj P).obj j').map a
              (P.map (CategoryTheory.Prod.mkHom (𝟙 j') (g j').hom) (y j')) =
            ((Functor.curry.obj P).obj j').map b
              (P.map (CategoryTheory.Prod.mkHom f (g j).hom) (y j)) := by
      exact (almost_directed_colimit_eventual_equality_iff hspan
        ((Functor.curry.obj P).obj j')).mp (w f)
    let kf {j j' : J} (f : j ⟶ j') : I := (wrel f).choose
    let gf {j j' : J} (f : j ⟶ j') : k'.obj ⟶ kf f :=
      (wrel f).choose_spec.choose
    let hf {j j' : J} (f : j ⟶ j') : k'.obj ⟶ kf f :=
      (wrel f).choose_spec.choose_spec.choose
    have wf {j j' : J} (f : j ⟶ j') :
        P.map (CategoryTheory.Prod.mkHom (𝟙 j')
          ((g j').hom ≫ gf f)) (y j') =
          P.map (CategoryTheory.Prod.mkHom f
            ((g j).hom ≫ hf f)) (y j) := by
      have q :
          ((Functor.curry.obj P).obj j').map (gf f)
              (P.map (CategoryTheory.Prod.mkHom (𝟙 j') (g j').hom) (y j')) =
            ((Functor.curry.obj P).obj j').map (hf f)
              (P.map (CategoryTheory.Prod.mkHom f (g j).hom) (y j)) :=
        (wrel f).choose_spec.choose_spec.choose_spec
      convert! q using 1
      · simp [← comp_apply, -types_comp_apply]
      · simp [← comp_apply, -types_comp_apply, ← P.map_comp]
    have hkf {j j' : J} (f : j ⟶ j') :
        Quotient.mk'' (kf f) = comp := by
      simpa [comp] using
        (Quotient.sound' (Zigzag.of_hom ((g j₀).hom ≫ gf f))).symm
    let kfObj {j j' : J} (f : j ⟶ j') : comp.Component :=
      ⟨kf f, hkf f⟩
    let gfObj {j j' : J} (f : j ⟶ j') : k' ⟶ kfObj f :=
      ObjectProperty.homMk (gf f)
    let hfObj {j j' : J} (f : j ⟶ j') : k' ⟶ kfObj f :=
      ObjectProperty.homMk (hf f)
    let O2 : Finset comp.Component :=
      (Finset.univ.biUnion fun j => Finset.univ.biUnion fun j' =>
        Finset.univ.image (@kfObj j j')) ∪ {k'}
    have kfO : ∀ {j j'} (f : j ⟶ j'), kfObj f ∈ O2 :=
        fun {j} {j'} f =>
      Finset.mem_union.mpr
        (Or.inl
          (Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ j,
            Finset.mem_biUnion.mpr ⟨j', Finset.mem_univ j',
              Finset.mem_image.mpr ⟨f, Finset.mem_univ _, rfl⟩⟩⟩))
    have k'O : k' ∈ O2 :=
      Finset.mem_union.mpr (Or.inr (Finset.mem_singleton.mpr rfl))
    let H2 : Finset
        (Σ' (X Y : comp.Component) (_ : X ∈ O2) (_ : Y ∈ O2), X ⟶ Y) :=
      Finset.univ.biUnion fun j : J =>
        Finset.univ.biUnion fun j' : J =>
          Finset.univ.biUnion fun f : j ⟶ j' =>
            {⟨k', kfObj f, k'O, kfO f, gfObj f⟩,
              ⟨k', kfObj f, k'O, kfO f, hfObj f⟩}
    obtain ⟨k'', i', s'⟩ := IsFiltered.sup_exists O2 H2
    let i {j j' : J} (f : j ⟶ j') : kfObj f ⟶ k'' :=
      i' (kfO f)
    have s : ∀ {j₁ j₂ j₃ j₄} (f : j₁ ⟶ j₂) (f' : j₃ ⟶ j₄),
        gfObj f ≫ i f = hfObj f' ≫ i f' := by
      intro j₁ j₂ j₃ j₄ f f'
      rw [s', s']
      · exact k'O
      · exact Finset.mem_biUnion.mpr ⟨j₃, Finset.mem_univ _,
          Finset.mem_biUnion.mpr ⟨j₄, Finset.mem_univ _,
            Finset.mem_biUnion.mpr ⟨f', Finset.mem_univ _, by
              rw [Finset.mem_insert, PSigma.mk.injEq, heq_eq_eq,
                PSigma.mk.injEq, heq_eq_eq, PSigma.mk.injEq, heq_eq_eq,
                PSigma.mk.injEq, heq_eq_eq, eq_self, true_and, eq_self,
                true_and, eq_self, true_and, eq_self, true_and,
                Finset.mem_singleton, eq_self, or_true]
              trivial⟩⟩⟩
      · exact Finset.mem_biUnion.mpr ⟨j₁, Finset.mem_univ _,
          Finset.mem_biUnion.mpr ⟨j₂, Finset.mem_univ _,
            Finset.mem_biUnion.mpr ⟨f, Finset.mem_univ _, by
              rw [Finset.mem_insert, PSigma.mk.injEq, heq_eq_eq,
                PSigma.mk.injEq, heq_eq_eq, PSigma.mk.injEq, heq_eq_eq,
                PSigma.mk.injEq, heq_eq_eq, eq_self, true_and, eq_self,
                true_and, eq_self, true_and, eq_self, true_and,
                Finset.mem_singleton, eq_self, true_or]
              trivial⟩⟩⟩
    fconstructor
    · apply colimit.ι
        (Functor.curry.obj (CategoryTheory.Prod.swap I J ⋙ P) ⋙ lim) k''.obj _
      refine Types.Limit.mk _ (fun j =>
          P.map (CategoryTheory.Prod.mkHom (𝟙 j) (i (𝟙 j)).hom)
            (P.map (CategoryTheory.Prod.mkHom (𝟙 j) (gf (𝟙 j)))
              (P.map (CategoryTheory.Prod.mkHom (𝟙 j) (g j).hom) (y j)))) ?_
      have hmerged {j j' : J} (f : j ⟶ j') :
          P.map (CategoryTheory.Prod.mkHom f
              ((g j).hom ≫ (gf (𝟙 j)) ≫ (i (𝟙 j)).hom)) (y j) =
            P.map (CategoryTheory.Prod.mkHom (𝟙 j')
              ((g j').hom ≫ (gf (𝟙 j') ≫ (i (𝟙 j')).hom))) (y j') := by
        calc
          P.map (CategoryTheory.Prod.mkHom f
              ((g j).hom ≫ (gf (𝟙 j)) ≫ (i (𝟙 j)).hom)) (y j) =
              P.map (CategoryTheory.Prod.mkHom f
              ((g j).hom ≫ (hf f) ≫ (i f).hom)) (y j) := by
            have hs : gf (𝟙 j) ≫ (i (𝟙 j)).hom =
                hf f ≫ (i f).hom := by
              simpa [gfObj, hfObj] using
                congrArg (fun q => q.hom) (s (𝟙 j) f)
            rw [hs]
          _ = P.map (CategoryTheory.Prod.mkHom (𝟙 j') (i f).hom)
              (P.map (CategoryTheory.Prod.mkHom f
                ((g j).hom ≫ hf f)) (y j)) := by
            rw [← comp_apply, ← Functor.map_comp, CategoryTheory.prod_comp,
              Category.comp_id, Category.assoc]
          _ = P.map (CategoryTheory.Prod.mkHom (𝟙 j') (i f).hom)
              (P.map (CategoryTheory.Prod.mkHom (𝟙 j')
                ((g j').hom ≫ gf f)) (y j')) := by
            rw [← wf f]
          _ = P.map (CategoryTheory.Prod.mkHom (𝟙 j')
              ((g j').hom ≫ gf f ≫ (i f).hom)) (y j') := by
            rw [← comp_apply, ← Functor.map_comp, CategoryTheory.prod_comp,
              Category.id_comp, Category.assoc]
          _ = P.map (CategoryTheory.Prod.mkHom (𝟙 j')
              ((g j').hom ≫ gf (𝟙 j') ≫ (i (𝟙 j')).hom)) (y j') := by
            have hs₁ : gf f ≫ (i f).hom =
                hf (𝟙 j') ≫ (i (𝟙 j')).hom := by
              simpa [gfObj, hfObj] using
                congrArg (fun q => q.hom) (s f (𝟙 j'))
            have hs₂ : gf (𝟙 j') ≫ (i (𝟙 j')).hom =
                hf (𝟙 j') ≫ (i (𝟙 j')).hom := by
              simpa [gfObj, hfObj] using
                congrArg (fun q => q.hom) (s (𝟙 j') (𝟙 j'))
            have hs := hs₁.trans hs₂.symm
            rw [hs]
      have hcoh {j j' : J} (f : j ⟶ j') :
          ((Functor.curry.obj (CategoryTheory.Prod.swap I J ⋙ P)).obj k''.obj).map f
              (P.map (CategoryTheory.Prod.mkHom (𝟙 j) (i (𝟙 j)).hom)
                (P.map (CategoryTheory.Prod.mkHom (𝟙 j) (gf (𝟙 j)))
                  (P.map (CategoryTheory.Prod.mkHom (𝟙 j) (g j).hom) (y j)))) =
            P.map (CategoryTheory.Prod.mkHom (𝟙 j') (i (𝟙 j')).hom)
              (P.map (CategoryTheory.Prod.mkHom (𝟙 j') (gf (𝟙 j')))
                (P.map (CategoryTheory.Prod.mkHom (𝟙 j') (g j').hom) (y j'))) := by
        change
          P.map (CategoryTheory.Prod.mkHom f (𝟙 k''.obj))
              (P.map (CategoryTheory.Prod.mkHom (𝟙 j) (i (𝟙 j)).hom)
                (P.map (CategoryTheory.Prod.mkHom (𝟙 j) (gf (𝟙 j)))
                  (P.map (CategoryTheory.Prod.mkHom (𝟙 j) (g j).hom) (y j)))) =
            P.map (CategoryTheory.Prod.mkHom (𝟙 j') (i (𝟙 j')).hom)
              (P.map (CategoryTheory.Prod.mkHom (𝟙 j') (gf (𝟙 j')))
                (P.map (CategoryTheory.Prod.mkHom (𝟙 j') (g j').hom) (y j')))
        have hmap (j : J) (a : k'.obj ⟶ kf (𝟙 j))
            (b : kf (𝟙 j) ⟶ k''.obj) :
            P.map (CategoryTheory.Prod.mkHom (𝟙 j) (g j).hom) ≫
                P.map (CategoryTheory.Prod.mkHom (𝟙 j) a) ≫
                P.map (CategoryTheory.Prod.mkHom (𝟙 j) b) =
              P.map (CategoryTheory.Prod.mkHom (𝟙 j)
                ((g j).hom ≫ a ≫ b)) := by
          rw [← P.map_comp, ← P.map_comp, CategoryTheory.prod_comp,
            CategoryTheory.prod_comp, Category.id_comp, Category.id_comp]
        have hx :
            P.map (CategoryTheory.Prod.mkHom (𝟙 j) (i (𝟙 j)).hom)
                (P.map (CategoryTheory.Prod.mkHom (𝟙 j) (gf (𝟙 j)))
                  (P.map (CategoryTheory.Prod.mkHom (𝟙 j) (g j).hom) (y j))) =
              P.map (CategoryTheory.Prod.mkHom (𝟙 j)
                ((g j).hom ≫ gf (𝟙 j) ≫ (i (𝟙 j)).hom)) (y j) := by
          rw [← comp_apply, ← comp_apply,
            (hmap j (gf (𝟙 j)) (i (𝟙 j)).hom)]
        have hy :
            P.map (CategoryTheory.Prod.mkHom (𝟙 j') (i (𝟙 j')).hom)
                (P.map (CategoryTheory.Prod.mkHom (𝟙 j') (gf (𝟙 j')))
                  (P.map (CategoryTheory.Prod.mkHom (𝟙 j') (g j').hom) (y j'))) =
              P.map (CategoryTheory.Prod.mkHom (𝟙 j')
                ((g j').hom ≫ gf (𝟙 j') ≫ (i (𝟙 j')).hom)) (y j') := by
          rw [← comp_apply, ← comp_apply,
            (hmap j' (gf (𝟙 j')) (i (𝟙 j')).hom)]
        calc
          P.map (CategoryTheory.Prod.mkHom f (𝟙 k''.obj))
              (P.map (CategoryTheory.Prod.mkHom (𝟙 j) (i (𝟙 j)).hom)
                (P.map (CategoryTheory.Prod.mkHom (𝟙 j) (gf (𝟙 j)))
                  (P.map (CategoryTheory.Prod.mkHom (𝟙 j) (g j).hom) (y j)))) =
              P.map (CategoryTheory.Prod.mkHom f
                ((g j).hom ≫ gf (𝟙 j) ≫ (i (𝟙 j)).hom)) (y j) := by
            rw [hx, ← comp_apply, ← P.map_comp, CategoryTheory.prod_comp,
              Category.id_comp, Category.comp_id]
          _ = P.map (CategoryTheory.Prod.mkHom (𝟙 j')
                ((g j').hom ≫ gf (𝟙 j') ≫ (i (𝟙 j')).hom)) (y j') :=
            hmerged f
          _ = P.map (CategoryTheory.Prod.mkHom (𝟙 j') (i (𝟙 j')).hom)
              (P.map (CategoryTheory.Prod.mkHom (𝟙 j') (gf (𝟙 j')))
                (P.map (CategoryTheory.Prod.mkHom (𝟙 j') (g j').hom) (y j'))) :=
            hy.symm
      exact fun j j' f => hcoh (j := j) (j' := j') f
    · apply Types.limit_ext
      intro j
      simp only [Functor.comp_obj,
        ← comp_apply, Category.assoc, ι_colimitLimitToLimitColimit_π,
        Functor.curry_obj_obj_obj, CategoryTheory.Prod.swap_obj]
      dsimp
      rw [← dsimp% e j]
      rw [Types.Limit.π_mk]
      dsimp only [Functor.comp_obj, ← Functor.curry_obj_obj_obj]
      rw [almost_directed_colimit_eventual_equality_iff hspan
        ((Functor.curry.obj P).obj j)]
      refine ⟨k''.obj, ((𝟙 k'' : k'' ⟶ k'').hom),
        (g j).hom ≫ (gf (𝟙 j)) ≫ (i (𝟙 j)).hom, ?_⟩
      simp
  let e := colimitLimitToLimitColimit P
  have hbij : Function.Bijective e := ⟨hq_inj, hq_surj⟩
  have hIso : IsIso e := (isIso_iff_bijective e).2 hbij
  exact ⟨Functor.mapIso colim (limitIsoSwapCompLim M) ≪≫
    (asIso e) ≪≫ HasLimit.isoOfNatIso
      ((Functor.isoWhiskerRight (Functor.currying.unitIso.app M) colim).symm ≪≫
        (colimitFlipIsoCompColim M).symm)⟩

/-- The coproduct pullback and coproduct equalizer identities displayed in the
source are the set-theoretic special cases of the preceding finite connected
limit statement, including the empty coproduct case. -/
def SetFiberProduct {X Y Z : Type u} (f : X → Y) (g : Z → Y) : Type u :=
  {p : X × Z // f p.1 = g p.2}

def SetEqualizer {X Y : Type u} (f g : X → Y) : Type u :=
  {x : X // f x = g x}

theorem coproduct_fibreProduct_equiv
    {J : Type v'} {A B C : J → Type u}
    (f : ∀ j, A j → B j) (g : ∀ j, C j → B j) :
    Nonempty
      (SetFiberProduct (Sigma.map id f) (Sigma.map id g) ≃
        (Σ j, SetFiberProduct (f j) (g j))) := by
  classical
  refine ⟨{
    toFun := fun p => by
      rcases p with ⟨⟨⟨j, a⟩, ⟨k, c⟩⟩, hp⟩
      have hp' : (⟨j, f j a⟩ : Σ j, B j) = ⟨k, g k c⟩ := by
        simpa [Sigma.map] using hp
      have hjk : j = k := congrArg Sigma.fst hp'
      subst k
      exact ⟨j, ⟨⟨a, c⟩, eq_of_heq (Sigma.mk.inj_iff.mp hp').2⟩⟩
    invFun := fun q => by
      rcases q with ⟨j, ⟨⟨a, c⟩, h⟩⟩
      exact ⟨⟨⟨j, a⟩, ⟨j, c⟩⟩, by
        simpa [Sigma.map] using congrArg (fun b => (⟨j, b⟩ : Σ j, B j)) h⟩
    left_inv := by
      intro p
      rcases p with ⟨⟨⟨j, a⟩, ⟨k, c⟩⟩, hp⟩
      have hp' : (⟨j, f j a⟩ : Σ j, B j) = ⟨k, g k c⟩ := by
        simpa [Sigma.map] using hp
      have hjk : j = k := congrArg Sigma.fst hp'
      subst k
      rfl
    right_inv := by
      rintro ⟨j, ⟨⟨a, c⟩, h⟩⟩
      simp }⟩

theorem coproduct_equalizer_equiv
    {J : Type v'} {A B : J → Type u}
    (f g : ∀ j, A j → B j) :
    Nonempty
      (SetEqualizer (Sigma.map id f) (Sigma.map id g) ≃
        (Σ j, SetEqualizer (f j) (g j))) := by
  refine ⟨{
    toFun := fun p => by
      rcases p with ⟨⟨j, a⟩, hp⟩
      have hp' : (⟨j, f j a⟩ : Σ j, B j) = ⟨j, g j a⟩ := by
        simpa [Sigma.map] using hp
      exact ⟨j, ⟨a, eq_of_heq (Sigma.mk.inj_iff.mp hp').2⟩⟩
    invFun := fun q => by
      rcases q with ⟨j, ⟨a, h⟩⟩
      exact ⟨⟨j, a⟩, by simpa [Sigma.map] using h⟩
    left_inv := by
      rintro ⟨⟨j, a⟩, hp⟩
      apply Subtype.ext
      rfl
    right_inv := by
      rintro ⟨j, ⟨a, h⟩⟩
      apply Sigma.ext rfl
      apply heq_of_eq
      apply Subtype.ext
      rfl }⟩

theorem almost_directed_colimit_commutes_fibre_products_and_equalizers
    {J : Type v'} :
    ∀ {A B C : J → Type u}
      (f : ∀ j, A j → B j) (g : ∀ j, C j → B j),
      Nonempty
        (SetFiberProduct (Sigma.map id f) (Sigma.map id g) ≃
          (Σ j, SetFiberProduct (f j) (g j))) ∧
      ∀ {A B : J → Type u} (f g : ∀ j, A j → B j),
        Nonempty
          (SetEqualizer (Sigma.map id f) (Sigma.map id g) ≃
            (Σ j, SetEqualizer (f j) (g j))) := by
  intro A B C f g
  exact ⟨coproduct_fibreProduct_equiv f g, by
    intro A B f g
    exact coproduct_equalizer_equiv f g⟩

end

end Formalization.Books.Categories.Unit19
