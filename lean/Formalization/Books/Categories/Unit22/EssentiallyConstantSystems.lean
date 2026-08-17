import Formalization.Books.Categories.Unit21.LimitsAndColimitsOverPreorderedSets
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.Algebra.Category.ModuleCat.Limits
import Mathlib.Algebra.DirectSum.Module
import Mathlib.CategoryTheory.Functor.OfSequence
import Mathlib.CategoryTheory.Limits.Constructions.EventuallyConstant
import Mathlib.CategoryTheory.Limits.Indization.Category

namespace Formalization.Books.Categories.Unit22

open CategoryTheory
open CategoryTheory.Limits
open Formalization.Books.Categories.Unit21

open scoped DirectSum
open scoped ZeroObject

universe u v u' v' w w'

noncomputable section

/-! # 22. Essentially constant systems

The source distinguishes a filtered cocone which is essentially constant from the
stronger condition that all sufficiently late transition maps are isomorphisms.
The definitions below retain the chosen cocone or cone, since that is the data
used by the factorization condition in the book.
-/

/-- A filtered diagram is ind-essentially constant with respect to a cocone. -/
def IsEssentiallyConstantInd
    {I : Type u} [Category.{v} I]
    {C : Type u'} [Category.{v'} C] [IsFiltered I]
    (M : I ⥤ C) (c : Cocone M) : Prop :=
  ∃ (i : I) (s : c.pt ⟶ M.obj i),
    s ≫ c.ι.app i = 𝟙 c.pt ∧
      ∀ j : I, ∃ (k : I) (f : i ⟶ k) (g : j ⟶ k),
        M.map g = c.ι.app j ≫ s ≫ M.map f

/-- A cofiltered diagram is pro-essentially constant with respect to a cone. -/
def IsEssentiallyConstantPro
    {I : Type u} [Category.{v} I]
    {C : Type u'} [Category.{v'} C] [IsCofiltered I]
    (M : I ⥤ C) (c : Cone M) : Prop :=
  ∃ (i : I) (r : M.obj i ⟶ c.pt),
    c.π.app i ≫ r = 𝟙 c.pt ∧
      ∀ j : I, ∃ (k : I) (f : k ⟶ i) (g : k ⟶ j),
        M.map g = M.map f ≫ r ≫ c.π.app j

/-- A filtered diagram is ind-essentially constant if it has such a cocone. -/
def IsEssentiallyConstantIndDiagram
    {I : Type u} [Category.{v} I]
    {C : Type u'} [Category.{v'} C] [IsFiltered I]
    (M : I ⥤ C) : Prop :=
  ∃ c : Cocone M, IsEssentiallyConstantInd M c

/-- A cofiltered diagram is pro-essentially constant if it has such a cone. -/
def IsEssentiallyConstantProDiagram
    {I : Type u} [Category.{v} I]
    {C : Type u'} [Category.{v'} C] [IsCofiltered I]
    (M : I ⥤ C) : Prop :=
  ∃ c : Cone M, IsEssentiallyConstantPro M c

/-- The source's notion for a system over a directed preorder. -/
def IsEssentiallyConstantSystem
    {I : Type u} [Preorder I]
    {C : Type v} [Category.{w} C]
    (M : System I C) : Prop :=
  ∃ hI : IsDirectedSet I,
    letI : Nonempty I := hI.1
    letI : IsDirectedOrder I := hI.2
    IsEssentiallyConstantIndDiagram M

/-- The source's dual notion for an inverse system over a directed preorder. -/
def IsEssentiallyConstantInverseSystem
    {I : Type u} [Preorder I]
    {C : Type v} [Category.{w} C]
    (M : InverseSystem I C) : Prop :=
  ∃ hI : IsDirectedSet I,
    letI : Nonempty I := hI.1
    letI : IsDirectedOrder I := hI.2
    IsEssentiallyConstantProDiagram M

/-- A system is eventually isomorphically constant from a threshold. -/
def EventuallyIsIso
    {I : Type u} [Preorder I]
    {C : Type v} [Category.{w} C]
    (M : System I C) : Prop :=
  ∃ i₀ : I, ∀ ⦃i i' : I⦄ (_ : i₀ ≤ i) (h : i ≤ i'),
    IsIso (M.map (homOfLE h))

/-- Essential constancy plus monomorphic transition maps forces eventual isomorphisms. -/
theorem eventuallyIsIso_of_essentiallyConstantSystem_of_mono
    {I : Type u} [Preorder I]
    {C : Type v} [Category.{w} C]
    {M : System I C} (hM : IsEssentiallyConstantSystem M)
    (hmono : ∀ ⦃i i' : I⦄ (h : i ≤ i'), Mono (M.map (homOfLE h))) :
    EventuallyIsIso M := by
  sorry

/-! ## The two source examples -/

/-- The transition map `(a,b) ↦ (a+b,0)` in the first example. -/
def zSquaredTransition :
    AddCommGrpCat.of (ℤ × ℤ) ⟶ AddCommGrpCat.of (ℤ × ℤ) :=
  AddCommGrpCat.ofHom
    (AddMonoidHom.mk' (fun p : ℤ × ℤ => (p.1 + p.2, 0)) (by
      intro x y
      ext <;> simp [add_comm, add_left_comm]))

/-- The projection to the claimed essentially constant value `ℤ`. -/
def zSquaredProjection :
    AddCommGrpCat.of (ℤ × ℤ) ⟶ AddCommGrpCat.of ℤ :=
  AddCommGrpCat.ofHom
    (AddMonoidHom.mk' (fun p : ℤ × ℤ => p.1 + p.2) (by
      intro x y
      simp [add_comm, add_left_comm]))

/-- The repeated transition system in the first example. -/
def zSquaredSystem : ℕ ⥤ AddCommGrpCat :=
  Functor.ofSequence (fun _ : ℕ => zSquaredTransition)

/-- The first example has an essentially constant value isomorphic to `ℤ`. -/
theorem zSquaredSystem_is_essentiallyConstant :
    ∃ c : Cocone zSquaredSystem,
      IsEssentiallyConstantInd zSquaredSystem c ∧
        Nonempty (c.pt ≅ AddCommGrpCat.of ℤ) := by
  sorry

/-- Each displayed transition in the first example has a nonzero kernel element. -/
theorem zSquaredSystem_transition_has_nontrivial_kernel (n : ℕ) :
    ∃ x : ℤ × ℤ, x ≠ 0 ∧
      (zSquaredSystem.map (homOfLE (Nat.le_add_right n 1))).hom x = 0 := by
  sorry

/-- The underlying module of the shift example. -/
abbrev ShiftModule := ⨁ _ : ℕ, ℤ

/-- The left shift on the direct sum of countably many copies of `ℤ`. -/
def shiftLinearMap : ShiftModule →ₗ[ℤ] ShiftModule :=
  DirectSum.toModule ℤ ℕ ShiftModule (fun n =>
    match n with
    | 0 => 0
    | n + 1 => DirectSum.lof ℤ ℕ (fun _ : ℕ => ℤ) n)

/-- The repeated shift system. -/
def shiftSystem : ℕ ⥤ ModuleCat ℤ :=
  Functor.ofSequence (fun _ : ℕ => ModuleCat.ofHom shiftLinearMap)

/-- The colimit of the shift system is zero. -/
theorem shiftSystem_colimit_is_zero :
    IsZero (colimit shiftSystem) := by
  sorry

/-- The zero object supplies the split section/retraction in the shift example. -/
theorem shiftSystem_zero_retraction (n : ℕ) :
    (0 : (0 : ModuleCat ℤ) ⟶ shiftSystem.obj n) ≫
        (0 : shiftSystem.obj n ⟶ (0 : ModuleCat ℤ)) =
      𝟙 (0 : ModuleCat ℤ) := by
  sorry

/-- The shift system is not essentially constant despite its zero colimit and split map. -/
theorem shiftSystem_not_essentiallyConstant :
    ¬ IsEssentiallyConstantIndDiagram shiftSystem := by
  sorry

/-! ## The sanity check and Ind/Pro viewpoints -/

/-- The chosen cocone in an ind-essentially constant diagram is a colimit cocone. -/
theorem essentiallyConstantInd_hasColimit
    {I : Type u} [Category.{v} I] [IsFiltered I]
    {C : Type u'} [Category.{v'} C]
    {M : I ⥤ C} (hM : IsEssentiallyConstantIndDiagram M) :
    ∃ c : Cocone M, Nonempty (IsColimit c) ∧ IsEssentiallyConstantInd M c := by
  sorry

/-- The chosen cone in a pro-essentially constant diagram is a limit cone. -/
theorem essentiallyConstantPro_hasLimit
    {I : Type u} [Category.{v} I] [IsCofiltered I]
    {C : Type u'} [Category.{v'} C]
    {M : I ⥤ C} (hM : IsEssentiallyConstantProDiagram M) :
    ∃ c : Cone M, Nonempty (IsLimit c) ∧ IsEssentiallyConstantPro M c := by
  sorry

/-- The canonical ind-category attached to a category. -/
abbrev IndCategory (C : Type u) [Category.{v} C] := CategoryTheory.Ind C

/-- The canonical fully faithful embedding into the ind-category. -/
noncomputable def indEmbedding {C : Type u} [Category.{v} C] :
    C ⥤ IndCategory C :=
  Ind.yoneda

noncomputable def indEmbedding_fullyFaithful {C : Type u} [Category.{v} C] :
    (indEmbedding (C := C)).FullyFaithful :=
  Ind.yoneda.fullyFaithful

/-- The pro-category is the opposite of the ind-category of the opposite. -/
abbrev ProCategory (C : Type u) [Category.{v} C] :=
  (CategoryTheory.Ind Cᵒᵖ)ᵒᵖ

/-- The canonical fully faithful embedding into the pro-category. -/
noncomputable def proEmbedding {C : Type u} [Category.{v} C] :
    C ⥤ ProCategory C :=
  opOp C ⋙ (Ind.yoneda (C := Cᵒᵖ)).op

noncomputable def proEmbedding_fullyFaithful {C : Type u} [Category.{v} C] :
    (proEmbedding (C := C)).FullyFaithful := by
  exact
    (Functor.FullyFaithful.ofFullyFaithful (opOp C)).comp
      (Ind.yoneda.fullyFaithful (C := Cᵒᵖ)).op

/-- The ind-object represented by a small filtered diagram. -/
noncomputable def indLim
    {C : Type u} [Category.{v} C]
    (I : Type v) [SmallCategory I] [IsFiltered I] :
    (I ⥤ C) ⥤ IndCategory C :=
  Ind.lim I

/-- The pro-object represented by a small cofiltered diagram. -/
noncomputable def proLim
    {C : Type u} [Category.{v} C]
    (I : Type v) [SmallCategory I] [IsCofiltered I] :
    (I ⥤ C) ⥤ ProCategory C where
  obj M := Opposite.op ((Ind.lim (C := Cᵒᵖ) Iᵒᵖ).obj M.op)
  map {M N} α := ((Ind.lim (C := Cᵒᵖ) Iᵒᵖ).map (NatTrans.op α)).op
  map_id := by
    intro M
    apply Quiver.Hom.op_inj
    simp
  map_comp := by
    intro M N P α β
    apply Quiver.Hom.op_inj
    simp

/-- The ind characterization in the ind-category. -/
theorem essentiallyConstantInd_iff_indLim_isomorphic_to_constant
    {C : Type u} [Category.{v} C]
    {I : Type v} [SmallCategory I] [IsFiltered I]
    (M : I ⥤ C) :
    IsEssentiallyConstantIndDiagram M ↔
      ∃ X : C, Nonempty ((indLim I).obj M ≅ (indEmbedding (C := C)).obj X) := by
  sorry

/-- The pro characterization in the pro-category. -/
theorem essentiallyConstantPro_iff_proLim_isomorphic_to_constant
    {C : Type u} [Category.{v} C]
    {I : Type v} [SmallCategory I] [IsCofiltered I]
    (M : I ⥤ C) :
    IsEssentiallyConstantProDiagram M ↔
      ∃ X : C, Nonempty ((proLim I).obj M ≅ (proEmbedding (C := C)).obj X) := by
  sorry

/-! The following structure records the standard representative of a pro
morphism between inverse sequences.  `refines` is the common-refinement
criterion from the source's example. -/

structure ProMorphismData
    {C : Type u} [Category.{v} C]
    (X Y : ℕᵒᵖ ⥤ C) where
  index : ℕ → ℕ
  monotone : Monotone index
  app : ∀ n : ℕ, X.obj (Opposite.op (index n)) ⟶ Y.obj (Opposite.op n)
  naturality : ∀ {n n' : ℕ} (h : n ≤ n'),
    X.map (homOfLE (monotone h)).op ≫ app n =
      app n' ≫ Y.map (homOfLE h).op

/-- The unreindexed data for a morphism of inverse sequences. -/
structure RawProMorphismData
    {C : Type u} [Category.{v} C]
    (X Y : ℕᵒᵖ ⥤ C) where
  index : ℕ → ℕ
  app : ∀ n : ℕ, X.obj (Opposite.op (index n)) ⟶ Y.obj (Opposite.op n)
  compatible : ∀ {n n' : ℕ} (h : n ≤ n'),
    ∃ (m : ℕ) (hn : index n ≤ m) (hn' : index n' ≤ m),
      X.map (homOfLE hn).op ≫ app n =
        X.map (homOfLE hn').op ≫ app n' ≫ Y.map (homOfLE h).op

namespace RawProMorphismData

/-- A monotone representative refines raw data when it is obtained by moving
each source index farther out and composing with the inverse-system map. -/
def Refines
    {C : Type u} [Category.{v} C]
    {X Y : ℕᵒᵖ ⥤ C}
    (p : RawProMorphismData X Y) (q : ProMorphismData X Y) : Prop :=
  (∀ n : ℕ, p.index n ≤ q.index n) ∧
    ∀ (n : ℕ) (h : p.index n ≤ q.index n),
      X.map (homOfLE h).op ≫ p.app n = q.app n

/-- Every compatible raw presentation admits a monotone refinement. -/
theorem exists_monotone_refinement
    {C : Type u} [Category.{v} C]
    {X Y : ℕᵒᵖ ⥤ C} (p : RawProMorphismData X Y) :
    ∃ q : ProMorphismData X Y, Refines p q := by
  sorry

end RawProMorphismData

namespace ProMorphismData

/-- One representative is obtained from another by increasing the source index. -/
def Refines
    {C : Type u} [Category.{v} C]
    {X Y : ℕᵒᵖ ⥤ C}
    (p q : ProMorphismData X Y) : Prop :=
  (∀ n : ℕ, p.index n ≤ q.index n) ∧
    ∀ (n : ℕ) (h : p.index n ≤ q.index n),
      X.map (homOfLE h).op ≫ p.app n = q.app n

/-- Two representatives have the same pro morphism when they admit a common
increasing refinement. -/
def HaveCommonRefinement
    {C : Type u} [Category.{v} C]
    {X Y : ℕᵒᵖ ⥤ C}
    (p q : ProMorphismData X Y) : Prop :=
  ∃ r : ProMorphismData X Y, Refines p r ∧ Refines q r

theorem commonRefinement_is_equivalence
    {C : Type u} [Category.{v} C]
    {X Y : ℕᵒᵖ ⥤ C} :
    Equivalence (HaveCommonRefinement (X := X) (Y := Y)) := by
  sorry

end ProMorphismData

/-- The copresheaf represented by a cofiltered diagram at an object. -/
noncomputable def proCopresheafAt
    {I : Type u} [Category.{v} I]
    {C : Type u'} [Category.{v'} C]
    (F : I ⥤ C) (X : C)
    [HasColimit (F.op ⋙ yoneda.obj X)] : Type v' :=
  colimit (F.op ⋙ yoneda.obj X)

/-- The copresheaf `X ↦ colim_i Hom(F(i),X)`. -/
noncomputable def proCopresheaf
    {I : Type u} [Category.{v} I]
    {C : Type u'} [Category.{v'} C]
    (F : I ⥤ C) [HasColimitsOfShape Iᵒᵖ (Type v')] :
    C ⥤ Type v' where
  obj X := colimit (F.op ⋙ yoneda.obj X)
  map {X Y} f := colim.map (Functor.whiskerLeft F.op (yoneda.map f))
  map_id := by
    intro X
    apply colimit.hom_ext
    intro i
    simp
  map_comp := by
    intro X Y Z f g
    apply colimit.hom_ext
    intro i
    simp [Functor.map_comp]

/-- The pro-morphism formula in terms of copresheaf transformations. -/
theorem proCategory_hom_as_copresheaf_natTrans
    {I J : Type v} [SmallCategory I] [SmallCategory J]
    [IsCofiltered I] [IsCofiltered J]
    {C : Type u} [Category.{v} C]
    [HasColimitsOfShape Iᵒᵖ (Type v)]
    [HasColimitsOfShape Jᵒᵖ (Type v)]
    (F : I ⥤ C) (G : J ⥤ C) :
    Nonempty
      (((proLim I).obj F ⟶ (proLim J).obj G) ≃
        (proCopresheaf G ⟶ proCopresheaf F)) := by
  sorry

/-- A functor carries ind-essentially constant diagrams to ind-essentially
constant diagrams. -/
theorem isEssentiallyConstantInd_comp
    {I : Type u} [Category.{v} I] [IsFiltered I]
    {C : Type u'} [Category.{v'} C]
    {D : Type w} [Category.{w'} D]
    (F : C ⥤ D) {M : I ⥤ C}
    (hM : IsEssentiallyConstantIndDiagram M) :
    IsEssentiallyConstantIndDiagram (M ⋙ F) := by
  sorry

/-- A functor carries pro-essentially constant diagrams to pro-essentially
constant diagrams. -/
theorem isEssentiallyConstantPro_comp
    {I : Type u} [Category.{v} I] [IsCofiltered I]
    {C : Type u'} [Category.{v'} C]
    {D : Type w} [Category.{w'} D]
    (F : C ⥤ D) {M : I ⥤ C}
    (hM : IsEssentiallyConstantProDiagram M) :
    IsEssentiallyConstantProDiagram (M ⋙ F) := by
  sorry

/-! ## Hom-set characterizations -/

/-- The covariant hom diagram `W ↦ Hom(W,M_i)`.  It is the typed form of
`M ⋙ coyoneda.obj (op W)`; writing the components explicitly avoids casts
between `op (unop W)` and `W` in the hom-set conditions. -/
abbrev homIntoDiagram
    {I : Type u} [Category.{v} I]
    {C : Type u'} [Category.{v'} C]
    (M : I ⥤ C) (W : C) : I ⥤ Type v' :=
  { obj := fun i => W ⟶ M.obj i
    map := fun {i j} (f : i ⟶ j) =>
      TypeCat.ofHom (fun g : W ⟶ M.obj i => g ≫ M.map f)
    map_id := by
      intro i
      ext g
      simp
    map_comp := by
      intro i j k f g
      ext h
      simp [Category.assoc] }

/-- The contravariant hom diagram `i ↦ Hom(M_i,W)`.  It is the typed form of
`M.op ⋙ yoneda.obj W`. -/
abbrev homFromDiagram
    {I : Type u} [Category.{v} I]
    {C : Type u'} [Category.{v'} C]
    (M : I ⥤ C) (W : C) : Iᵒᵖ ⥤ Type v' :=
  { obj := fun i => M.obj i.unop ⟶ W
    map := fun {i j} (f : i ⟶ j) =>
      TypeCat.ofHom (fun g : M.obj i.unop ⟶ W => M.map f.unop ≫ g)
    map_id := by
      intro i
      ext g
      simp
    map_comp := by
      intro i j k f g
      ext h
      simp [Category.assoc] }

/-- Precomposition on the covariant hom diagrams. -/
def precomposeHomInto
    {J : Type u} [Category.{v} J]
    {C : Type u'} [Category.{v'} C]
    {A B : C} (G : J ⥤ C) (f : A ⟶ B) :
    homIntoDiagram G B ⟶ homIntoDiagram G A where
  app := fun j =>
    TypeCat.ofHom (fun g : B ⟶ G.obj j => f ≫ g)
  naturality := by
    intro i j g
    ext h
    simp [Category.assoc]

/-- The diagram whose limit is the ind-category hom formula
`lim_i colim_j Hom(F(i),G(j))`. -/
def indHomFormulaDiagram
    {I J : Type v} [SmallCategory I] [SmallCategory J]
    {C : Type u} [Category.{v} C]
    [HasColimitsOfShape J (Type v)]
    (F : I ⥤ C) (G : J ⥤ C) : Iᵒᵖ ⥤ Type v where
  obj i := colimit (homIntoDiagram G (F.obj i.unop))
  map {i j} f :=
    colim.map (precomposeHomInto G (F.map f.unop))
  map_id := by
    intro i
    apply colimit.hom_ext
    intro j
    ext h
    simp [precomposeHomInto]
  map_comp := by
    intro i j k f g
    apply colimit.hom_ext
    intro l
    ext h
    simp [precomposeHomInto, Category.assoc]

/-- The ind-category hom-set formula from the source's ind-category remark. -/
theorem indCategory_hom_formula
    {I J : Type v} [SmallCategory I] [SmallCategory J]
    [IsFiltered I] [IsFiltered J]
    {C : Type u} [Category.{v} C]
    [HasColimitsOfShape J (Type v)]
    (F : I ⥤ C) (G : J ⥤ C)
    [HasLimit (indHomFormulaDiagram F G)] :
    Nonempty
      (((indLim I).obj F ⟶ (indLim J).obj G) ≃
        limit (indHomFormulaDiagram F G)) := by
  sorry

/-- The pro-category hom-set formula, expressed as the opposite ind formula. -/
theorem proCategory_hom_formula
    {I J : Type v} [SmallCategory I] [SmallCategory J]
    [IsCofiltered I] [IsCofiltered J]
    {C : Type u} [Category.{v} C]
    [HasColimitsOfShape Iᵒᵖ (Type v)]
    (F : I ⥤ C) (G : J ⥤ C)
    [HasLimit (indHomFormulaDiagram (F := G.op) (G := F.op))] :
    Nonempty
      (((proLim I).obj F ⟶ (proLim J).obj G) ≃
        limit (indHomFormulaDiagram (F := G.op) (G := F.op))) := by
  sorry

/-- The cocone induced on `Hom(W,-)` by a cocone on `M`. -/
def homIntoCocone
    {I : Type u} [Category.{v} I]
    {C : Type u'} [Category.{v'} C]
    {M : I ⥤ C} (c : Cocone M) (W : C) :
    Cocone (homIntoDiagram M W) where
  pt := W ⟶ c.pt
  ι :=
    { app := fun i =>
          TypeCat.ofHom (fun f : W ⟶ M.obj i =>
            f ≫ (c.ι.app i : M.obj i ⟶ c.pt))
      naturality := by
        intro i j f
        ext g
        simp [Category.assoc] }

/-- The cocone induced on `Hom(-,W)` by a cone on `M`. -/
def homFromCocone
    {I : Type u} [Category.{v} I]
    {C : Type u'} [Category.{v'} C]
    {M : I ⥤ C} (c : Cone M) (W : C) :
    Cocone (homFromDiagram M W) where
  pt := c.pt ⟶ W
  ι :=
    { app := fun i =>
          TypeCat.ofHom (fun f : M.obj i.unop ⟶ W =>
            (c.π.app i.unop : c.pt ⟶ M.obj i.unop) ≫ f)
      naturality := by
        intro i j f
        ext g
        simp }

/-- The map on hom sets induced by an ind cocone. -/
noncomputable def homIntoCoconeMap
    {I : Type u} [Category.{v} I]
    {C : Type u'} [Category.{v'} C]
    {M : I ⥤ C} (c : Cocone M) (W : C)
    [HasColimit (homIntoDiagram M W)] :
    colimit (homIntoDiagram M W) → (W ⟶ c.pt) :=
  colimit.desc (homIntoDiagram M W) (homIntoCocone c W)

/-- The map on hom sets induced by a pro cone. -/
noncomputable def homFromCoconeMap
    {I : Type u} [Category.{v} I]
    {C : Type u'} [Category.{v'} C]
    {M : I ⥤ C} (c : Cone M) (W : C)
    [HasColimit (homFromDiagram M W)] :
    colimit (homFromDiagram M W) → (c.pt ⟶ W) :=
  colimit.desc (homFromDiagram M W) (homFromCocone c W)

/-- The first three ind hom-set formulations, with the existence of the
set-valued colimits made explicit. -/
def IndHomColimitCondition
    {I : Type u} [Category.{v} I] [IsFiltered I]
    {C : Type u'} [Category.{v'} C]
    (M : I ⥤ C) : Prop :=
  ∃ c : Cocone M, ∀ W : C, ∃ hW : HasColimit (homIntoDiagram M W),
    letI : HasColimit (homIntoDiagram M W) := hW
    Function.Bijective (homIntoCoconeMap c W)

def IndHomColimitAndIsColimitCondition
    {I : Type u} [Category.{v} I] [IsFiltered I]
    {C : Type u'} [Category.{v'} C]
    (M : I ⥤ C) : Prop :=
  ∃ c : Cocone M, Nonempty (IsColimit c) ∧
    ∀ W : C, ∃ hW : HasColimit (homIntoDiagram M W),
      letI : HasColimit (homIntoDiagram M W) := hW
      Function.Bijective (homIntoCoconeMap c W)

/-- The fourth ind hom-set formulation, using a section at one stage. -/
def IndHomSectionCondition
    {I : Type u} [Category.{v} I] [IsFiltered I]
    {C : Type u'} [Category.{v'} C]
    (M : I ⥤ C) : Prop :=
  ∃ (X : C) (i : I) (s : X ⟶ M.obj i),
    ∀ W : C, ∃ hW : HasColimit (homIntoDiagram M W),
      letI : HasColimit (homIntoDiagram M W) := hW
      Function.Bijective
        (fun f : W ⟶ X =>
          colimit.ι (homIntoDiagram M W) i (f ≫ s))

def ProHomLimitCondition
    {I : Type u} [Category.{v} I] [IsCofiltered I]
    {C : Type u'} [Category.{v'} C]
    (M : I ⥤ C) : Prop :=
  ∃ c : Cone M, ∀ W : C, ∃ hW : HasColimit (homFromDiagram M W),
    letI : HasColimit (homFromDiagram M W) := hW
    Function.Bijective (homFromCoconeMap c W)

def ProHomLimitAndIsLimitCondition
    {I : Type u} [Category.{v} I] [IsCofiltered I]
    {C : Type u'} [Category.{v'} C]
    (M : I ⥤ C) : Prop :=
  ∃ c : Cone M, Nonempty (IsLimit c) ∧
    ∀ W : C, ∃ hW : HasColimit (homFromDiagram M W),
      letI : HasColimit (homFromDiagram M W) := hW
      Function.Bijective (homFromCoconeMap c W)

def ProHomSectionCondition
    {I : Type u} [Category.{v} I] [IsCofiltered I]
    {C : Type u'} [Category.{v'} C]
    (M : I ⥤ C) : Prop :=
  ∃ (X : C) (i : I) (r : M.obj i ⟶ X),
    ∀ W : C, ∃ hW : HasColimit (homFromDiagram M W),
      letI : HasColimit (homFromDiagram M W) := hW
      Function.Bijective
        (fun f : X ⟶ W =>
          colimit.ι (homFromDiagram M W) (Opposite.op i) (r ≫ f))

/-- The ind characterization by the three equivalent hom-set formulations. -/
theorem characterizeEssentiallyConstantInd
    {I : Type u} [Category.{v} I] [IsFiltered I]
    {C : Type u'} [Category.{v'} C]
    (M : I ⥤ C) :
    (IsEssentiallyConstantIndDiagram M ↔ IndHomColimitCondition M) ∧
      (IndHomColimitCondition M ↔ IndHomColimitAndIsColimitCondition M) ∧
      (IndHomColimitAndIsColimitCondition M ↔ IndHomSectionCondition M) := by
  sorry

/-- The pro dual characterization by the three equivalent hom-set formulations. -/
theorem characterizeEssentiallyConstantPro
    {I : Type u} [Category.{v} I] [IsCofiltered I]
    {C : Type u'} [Category.{v'} C]
    (M : I ⥤ C) :
    (IsEssentiallyConstantProDiagram M ↔ ProHomLimitCondition M) ∧
      (ProHomLimitCondition M ↔ ProHomLimitAndIsLimitCondition M) ∧
      (ProHomLimitAndIsLimitCondition M ↔ ProHomSectionCondition M) := by
  sorry

/-! ## Cofinality, products, and initial functors -/

/-- A product of filtered categories is filtered. -/
theorem isFiltered_product
    {I J : Type u} [Category.{v} I] [Category.{v} J]
    [IsFiltered I] [IsFiltered J] :
    IsFiltered (I × J) := by
  infer_instance

/-- The second projection from a product of filtered categories is final. -/
theorem product_snd_is_final
    {I J : Type u} [Category.{v} I] [Category.{v} J]
    [IsFiltered I] [IsFiltered J] :
    Functor.Final (CategoryTheory.Prod.snd I J) := by
  infer_instance

theorem isEssentiallyConstantInd_comp_final_iff
    {I : Type u} [Category.{v} I] [IsFiltered I]
    {J : Type u'} [Category.{v'} J] [IsFiltered J]
    {C : Type w} [Category.{w'} C]
    (H : I ⥤ J) [Functor.Final H] (M : J ⥤ C) :
    IsEssentiallyConstantIndDiagram M ↔
      IsEssentiallyConstantIndDiagram (H ⋙ M) := by
  sorry

theorem isEssentiallyConstantInd_comp_product_snd_iff
    {I : Type u} [Category.{v} I] [IsFiltered I]
    {J : Type u'} [Category.{v'} J] [IsFiltered J]
    {C : Type w} [Category.{w'} C]
    (M : J ⥤ C) :
    IsEssentiallyConstantIndDiagram M ↔
      IsEssentiallyConstantIndDiagram ((CategoryTheory.Prod.snd I J) ⋙ M) := by
  sorry

theorem isEssentiallyConstantPro_comp_initial_iff
    {I : Type u} [Category.{v} I] [IsCofiltered I]
    {J : Type u'} [Category.{v'} J] [IsCofiltered J]
    {C : Type w} [Category.{w'} C]
    (H : I ⥤ J) [Functor.Initial H] (M : J ⥤ C) :
    IsEssentiallyConstantProDiagram M ↔
      IsEssentiallyConstantProDiagram (H ⋙ M) := by
  sorry

end
