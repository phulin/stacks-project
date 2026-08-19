import Formalization.Books.Simplicial.Unit07.FibreProducts
import Formalization.Books.Simplicial.Unit13.ProductsWithSimplicialSets
import Mathlib.AlgebraicTopology.SimplicialSet.Dimension
import Mathlib.CategoryTheory.Limits.Shapes.Countable
import Mathlib.CategoryTheory.Yoneda
import Mathlib.Data.Countable.Basic

/-!
# Simplicial Methods, Chapter 17: Hom from simplicial sets into simplicial objects

The source's Hom object is a representing object for the contravariant
functor which sends `W` to maps from the degreewise coproduct
`W × U` into `V`.  We use Mathlib's `Functor.IsRepresentable` and
`Functor.RepresentableBy` for that universal property.  The degreewise
coproduct and the pullback in the final lemma are the constructions from
earlier chapters.
-/

namespace Formalization.Books.Simplicial.Unit17

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open scoped _root_.Simplicial

universe v u w

/-! ## Hypotheses on the simplicial set -/

/-- All simplices in sufficiently high degree are degenerate. -/
abbrev EventuallyDegenerate (U : SSet.{w}) : Prop :=
  ∃ d : ℕ, U.HasDimensionLT d

/-! ## The functor represented by `Hom(U, V)` -/

/-
The object `U` is regarded as an object of the full subcategory of finite,
nonempty simplicial sets.  The fixed-`U` functor supplied by Unit 13 has
object part `W ↦ W × U`; taking its opposite and composing with Yoneda gives
the source's functor of maps into `V`.
-/
noncomputable def productWithSimplicialSetBy
    {C : Type u} [Category.{v} C] [HasBinaryCoproducts C]
    (U : SSet.{w}) (hU : Unit13.FiniteNonemptySimplicialSet U) :
    SimplicialObject C ⥤ SimplicialObject C :=
  (Functor.prod'
      ((Functor.const (SimplicialObject C)).obj
        (⟨U, hU⟩ : Unit13.FSSets.{w}))
      (𝟭 (SimplicialObject C))) ⋙
    Unit13.productWithSimplicialSetBifunctor

noncomputable def homFunctor
    {C : Type u} [Category.{v} C] [HasBinaryCoproducts C]
    (U : SSet.{w}) (V : SimplicialObject C)
    (hU : Unit13.FiniteNonemptySimplicialSet U) :
    (SimplicialObject C)ᵒᵖ ⥤ Type v :=
  (productWithSimplicialSetBy U hU).op ⋙ yoneda.obj V

theorem homFunctor_obj
    {C : Type u} [Category.{v} C] [HasBinaryCoproducts C]
    (U : SSet.{w})
    (hU : Unit13.FiniteNonemptySimplicialSet U)
    (V : SimplicialObject C)
    (W : SimplicialObject C) :
    (homFunctor U V hU).obj (op W) =
    (Unit13.simplicialSetProduct U W hU ⟶ V) := by
  sorry

/-! ## Degree-zero representability -/

/-- The source's degree-zero functor on `Cᵒᵖ`. -/
noncomputable def homZeroFunctor
    {C : Type u} [Category.{v} C] [HasBinaryCoproducts C]
    (U : SSet.{w}) (V : SimplicialObject C)
    (hU : Unit13.FiniteNonemptySimplicialSet U) :
    Cᵒᵖ ⥤ Type v :=
  (SimplicialObject.const C).op ⋙ homFunctor U V hU

theorem homZeroFunctor_obj
    {C : Type u} [Category.{v} C] [HasBinaryCoproducts C]
    (U : SSet.{w}) (V : SimplicialObject C)
    (hU : Unit13.FiniteNonemptySimplicialSet U) (X : C) :
    (homZeroFunctor U V hU).obj (op X) =
      (Unit13.simplicialSetProduct U
        ((SimplicialObject.const C).obj X) hU ⟶ V) := by
  rfl

private noncomputable def simplicialSetElementsDiagram
    {C : Type u} [Category.{v} C]
    (U : SSet.{w}) (V : SimplicialObject C) : U.Elements ⥤ C where
  obj e := V.obj e.1
  map f := V.map f.1
  map_id := by
    intro e
    simp
  map_comp := by
    intro e₁ e₂ e₃ f g
    simp

private theorem hasLimit_simplicialSetElementsDiagram
    {C : Type u} [Category.{v} C] [HasCountableLimits C]
    (U : SSet.{w}) (V : SimplicialObject C)
    (hU : Unit13.FiniteNonemptySimplicialSet U) :
    HasLimit (simplicialSetElementsDiagram U V) := by
  letI : ∀ X : SimplexCategoryᵒᵖ, Finite (U.obj X) := by
    intro X
    simpa only [SimplexCategory.mk_len] using (hU X.unop.len).1
  letI : Countable SimplexCategory :=
    Function.Injective.countable (f := SimplexCategory.len) (by
      intro X Y h
      cases X
      cases Y
      cases h
      rfl)
  letI : Countable SimplexCategoryᵒᵖ :=
    Countable.of_equiv SimplexCategory Opposite.equivToOpposite
  letI : CountableCategory U.Elements := by
    constructor
    · change Countable (Σ X : SimplexCategoryᵒᵖ, U.obj X)
      infer_instance
    · intro e e'
      change Countable {f : e.1 ⟶ e'.1 // _}
      letI : Countable (e.1 ⟶ e'.1) :=
        Countable.of_equiv _ (opEquiv e.1 e'.1).symm
      infer_instance
  infer_instance

private theorem simplicialSetProduct_injection_map
    {C : Type u} [Category.{v} C] [HasBinaryCoproducts C]
    (U : SSet.{w}) (X : C) (hU : Unit13.FiniteNonemptySimplicialSet U)
    {Z Z' : SimplexCategoryᵒᵖ} (f : Z ⟶ Z') (u : U.obj Z) :
    (let h := Unit13.degreewiseCoproductInstance U
      ((SimplicialObject.const C).obj X) hU
     let _ := Unit13.degreewiseCoproductInstanceAt h Z
     let _ := Unit13.degreewiseCoproductInstanceAt h Z'
     Sigma.ι (fun _ : U.obj Z => ((SimplicialObject.const C).obj X).obj Z) u ≫
       (Unit13.simplicialSetProduct U ((SimplicialObject.const C).obj X) hU).map f) =
      (let h := Unit13.degreewiseCoproductInstance U
        ((SimplicialObject.const C).obj X) hU
       let _ := Unit13.degreewiseCoproductInstanceAt h Z'
       Sigma.ι (fun _ : U.obj Z' => ((SimplicialObject.const C).obj X).obj Z')
         (U.map f u)) := by
  sorry

private noncomputable def homToElementsCone
    {C : Type u} [Category.{v} C] [HasBinaryCoproducts C]
    (U : SSet.{w}) (V : SimplicialObject C)
    (hU : Unit13.FiniteNonemptySimplicialSet U) {X : C}
    (γ : Unit13.simplicialSetProduct U ((SimplicialObject.const C).obj X) hU ⟶ V) :
    ((Functor.const U.Elements).obj X ⟶ simplicialSetElementsDiagram U V) := by
  let h : Unit13.HasDegreewiseCoproducts U ((SimplicialObject.const C).obj X) :=
    Unit13.degreewiseCoproductInstance U ((SimplicialObject.const C).obj X) hU
  exact
    { app := fun e =>
        let _ := Unit13.degreewiseCoproductInstanceAt h e.1
        Sigma.ι (fun _ : U.obj e.1 => ((SimplicialObject.const C).obj X).obj e.1) e.2 ≫
          γ.app e.1
      naturality := by
        intro e e' f
        rcases e with ⟨Z, u⟩
        rcases e' with ⟨Z', u'⟩
        let fbase : Z ⟶ Z' := f.1
        have hf : U.map fbase u = u' := f.2
        let i :
            X ⟶ (Unit13.simplicialSetProduct U ((SimplicialObject.const C).obj X) hU).obj Z := by
          dsimp [Unit13.simplicialSetProduct, Unit13.simplicialSetProductOf]
          exact Sigma.ι (fun _ : U.obj Z => ((SimplicialObject.const C).obj X).obj Z) u
        let i' :
            X ⟶ (Unit13.simplicialSetProduct U ((SimplicialObject.const C).obj X) hU).obj Z' := by
          dsimp [Unit13.simplicialSetProduct, Unit13.simplicialSetProductOf]
          exact Sigma.ι (fun _ : U.obj Z' => ((SimplicialObject.const C).obj X).obj Z') u'
        change 𝟙 X ≫ (i' ≫ γ.app Z') = (i ≫ γ.app Z) ≫ V.map fbase
        simp only [Category.id_comp]
        have hi : i ≫
              (Unit13.simplicialSetProduct U ((SimplicialObject.const C).obj X) hU).map fbase = i' := by
          dsimp [i, i', Unit13.simplicialSetProduct, Unit13.simplicialSetProductOf]
          simp [Category.assoc, hf]
        calc
          i' ≫ γ.app Z' = (i ≫
              (Unit13.simplicialSetProduct U ((SimplicialObject.const C).obj X) hU).map fbase) ≫
              γ.app Z' := by rw [hi]
          _ = i ≫ ((Unit13.simplicialSetProduct U ((SimplicialObject.const C).obj X) hU).map fbase ≫
              γ.app Z') := by simp only [Category.assoc]
          _ = i ≫ (γ.app Z ≫ V.map fbase) := by rw [γ.naturality]
          _ = (i ≫ γ.app Z) ≫ V.map fbase := by simp only [Category.assoc] }

private noncomputable def elementsConeToHom
    {C : Type u} [Category.{v} C] [HasBinaryCoproducts C]
    (U : SSet.{w}) (V : SimplicialObject C)
    (hU : Unit13.FiniteNonemptySimplicialSet U) {X : C}
    (α : (Functor.const U.Elements).obj X ⟶ simplicialSetElementsDiagram U V) :
    Unit13.simplicialSetProduct U ((SimplicialObject.const C).obj X) hU ⟶ V := by
  let h : Unit13.HasDegreewiseCoproducts U ((SimplicialObject.const C).obj X) :=
    Unit13.degreewiseCoproductInstance U ((SimplicialObject.const C).obj X) hU
  exact
    { app := fun Z =>
        let _ := Unit13.degreewiseCoproductInstanceAt h Z
        let a : ∀ u : U.obj Z, X ⟶ V.obj Z := fun u =>
          show X ⟶ V.obj Z from α.app (Functor.elementsMk U Z u)
        Sigma.desc a
      naturality := by
        intro Z Z' f
        let _ := Unit13.degreewiseCoproductInstanceAt h Z
        let _ := Unit13.degreewiseCoproductInstanceAt h Z'
        apply Sigma.hom_ext
        intro u
        let fbase : Z ⟶ Z' := f
        let aZ : ∀ u : U.obj Z, X ⟶ V.obj Z := fun u => by
          change X ⟶ V.obj Z
          exact α.app (Functor.elementsMk U Z u)
        let aZ' : ∀ u : U.obj Z', X ⟶ V.obj Z' := fun u => by
          change X ⟶ V.obj Z'
          exact α.app (Functor.elementsMk U Z' u)
        let i :
            X ⟶ (Unit13.simplicialSetProduct U ((SimplicialObject.const C).obj X) hU).obj Z := by
          dsimp [Unit13.simplicialSetProduct, Unit13.simplicialSetProductOf]
          exact Sigma.ι (fun _ : U.obj Z => ((SimplicialObject.const C).obj X).obj Z) u
        change i ≫
            (Unit13.simplicialSetProduct U ((SimplicialObject.const C).obj X) hU).map fbase ≫
              Sigma.desc aZ' = i ≫ Sigma.desc aZ ≫ V.map fbase
        dsimp [i, Unit13.simplicialSetProduct, Unit13.simplicialSetProductOf]
        simp only [Sigma.ι_desc, Category.id_comp, Category.assoc]
        simpa [aZ, aZ', simplicialSetElementsDiagram, Category.assoc] using
            congrArg (fun k => (𝟙 X) ≫ k)
            (α.naturality (CategoryOfElements.homMk
              (Functor.elementsMk U Z u)
              (Functor.elementsMk U Z' (U.map fbase u)) fbase rfl))
          }

private noncomputable def elementsConeHomEquiv
    {C : Type u} [Category.{v} C] [HasBinaryCoproducts C]
    (U : SSet.{w}) (V : SimplicialObject C)
    (hU : Unit13.FiniteNonemptySimplicialSet U) {X : C} :
    ((Functor.const U.Elements).obj X ⟶ simplicialSetElementsDiagram U V) ≃
      (Unit13.simplicialSetProduct U ((SimplicialObject.const C).obj X) hU ⟶ V) :=
  { toFun := elementsConeToHom U V hU
    invFun := homToElementsCone U V hU
    left_inv := by
      intro α
      ext e
      change (Σ Z : SimplexCategoryᵒᵖ, U.obj Z) at e
      rcases e with ⟨Z, u⟩
      let h : Unit13.HasDegreewiseCoproducts U ((SimplicialObject.const C).obj X) :=
        Unit13.degreewiseCoproductInstance U ((SimplicialObject.const C).obj X) hU
      let _ := Unit13.degreewiseCoproductInstanceAt h Z
      dsimp only [elementsConeToHom, homToElementsCone]
      let a : ∀ u : U.obj Z, ((SimplicialObject.const C).obj X).obj Z ⟶ V.obj Z := fun u => by
        change ((SimplicialObject.const C).obj X).obj Z ⟶ V.obj Z
        exact α.app (Functor.elementsMk U Z u)
      change Sigma.ι (fun _ : U.obj Z => ((SimplicialObject.const C).obj X).obj Z) u ≫
        Sigma.desc a = a u
      exact Sigma.ι_desc a u
    right_inv := by
      intro γ
      ext Z
      let h : Unit13.HasDegreewiseCoproducts U ((SimplicialObject.const C).obj X) :=
        Unit13.degreewiseCoproductInstance U ((SimplicialObject.const C).obj X) hU
      let _ := Unit13.degreewiseCoproductInstanceAt h Z
      apply Sigma.hom_ext
      intro u
      dsimp only [elementsConeToHom, homToElementsCone]
      let b : ∀ u : U.obj Z, ((SimplicialObject.const C).obj X).obj Z ⟶ V.obj Z := fun u =>
        Sigma.ι (fun _ : U.obj Z => ((SimplicialObject.const C).obj X).obj Z) u ≫ γ.app Z
      change Sigma.ι (fun _ : U.obj Z => ((SimplicialObject.const C).obj X).obj Z) u ≫
        Sigma.desc b = b u
      exact Sigma.ι_desc b u }

private theorem homZero_map_apply
    {C : Type u} [Category.{v} C] [HasBinaryCoproducts C]
    (U : SSet.{w}) (V : SimplicialObject C)
    (hU : Unit13.FiniteNonemptySimplicialSet U)
    {X X' : C} (f : X ⟶ X')
    (γ : Unit13.simplicialSetProduct U ((SimplicialObject.const C).obj X') hU ⟶ V) :
    (homZeroFunctor U V hU).map f.op γ =
      (productWithSimplicialSetBy U hU).map
          ((SimplicialObject.const C).map f) ≫ γ := by
  rfl

private theorem productWithSimplicialSet_injection_map_second
    {C : Type u} [Category.{v} C] [HasBinaryCoproducts C]
    (U : SSet.{w})
    (hU : Unit13.FiniteNonemptySimplicialSet U)
    {X X' : C} (f : X ⟶ X') {Z : SimplexCategoryᵒᵖ} (u : U.obj Z) :
    (let hX := Unit13.degreewiseCoproductInstance U ((SimplicialObject.const C).obj X) hU
     let hX' := Unit13.degreewiseCoproductInstance U ((SimplicialObject.const C).obj X') hU
     let _ := Unit13.degreewiseCoproductInstanceAt hX Z
     let _ := Unit13.degreewiseCoproductInstanceAt hX' Z
     Sigma.ι (fun _ : U.obj Z => ((SimplicialObject.const C).obj X).obj Z) u ≫
       ((productWithSimplicialSetBy U hU).map ((SimplicialObject.const C).map f)).app Z) =
      (let hX' := Unit13.degreewiseCoproductInstance U ((SimplicialObject.const C).obj X') hU
       let _ := Unit13.degreewiseCoproductInstanceAt hX' Z
       f ≫ Sigma.ι (fun _ : U.obj Z => ((SimplicialObject.const C).obj X').obj Z) u) := by
  let hX : Unit13.HasDegreewiseCoproducts U ((SimplicialObject.const C).obj X) :=
    Unit13.degreewiseCoproductInstance U ((SimplicialObject.const C).obj X) hU
  let hX' : Unit13.HasDegreewiseCoproducts U ((SimplicialObject.const C).obj X') :=
    Unit13.degreewiseCoproductInstance U ((SimplicialObject.const C).obj X') hU
  let _ := Unit13.degreewiseCoproductInstanceAt hX Z
  let _ := Unit13.degreewiseCoproductInstanceAt hX' Z
  change
    Sigma.ι (fun _ : U.obj Z => ((SimplicialObject.const C).obj X).obj Z) u ≫
      Sigma.desc (fun u => f ≫
        Sigma.ι (fun _ : U.obj Z => ((SimplicialObject.const C).obj X').obj Z) u) =
    f ≫ Sigma.ι (fun _ : U.obj Z => ((SimplicialObject.const C).obj X').obj Z) u
  exact Sigma.ι_desc _ _

private theorem productWithSimplicialSet_injection_map_second_comp
    {C : Type u} [Category.{v} C] [HasBinaryCoproducts C]
    (U : SSet.{w}) (V : SimplicialObject C)
    (hU : Unit13.FiniteNonemptySimplicialSet U)
    {X X' : C} (f : X ⟶ X') {Z : SimplexCategoryᵒᵖ} (u : U.obj Z)
    (γ : Unit13.simplicialSetProduct U ((SimplicialObject.const C).obj X') hU ⟶ V) :
    (let hX := Unit13.degreewiseCoproductInstance U ((SimplicialObject.const C).obj X) hU
     let hX' := Unit13.degreewiseCoproductInstance U ((SimplicialObject.const C).obj X') hU
     let _ := Unit13.degreewiseCoproductInstanceAt hX Z
     let _ := Unit13.degreewiseCoproductInstanceAt hX' Z
     Sigma.ι (fun _ : U.obj Z => ((SimplicialObject.const C).obj X).obj Z) u ≫
       (((productWithSimplicialSetBy U hU).map ((SimplicialObject.const C).map f)).app Z ≫
         γ.app Z)) =
      (let hX' := Unit13.degreewiseCoproductInstance U ((SimplicialObject.const C).obj X') hU
       let _ := Unit13.degreewiseCoproductInstanceAt hX' Z
       f ≫ (Sigma.ι (fun _ : U.obj Z => ((SimplicialObject.const C).obj X').obj Z) u ≫
         γ.app Z)) := by
  let hX : Unit13.HasDegreewiseCoproducts U ((SimplicialObject.const C).obj X) :=
    Unit13.degreewiseCoproductInstance U ((SimplicialObject.const C).obj X) hU
  let hX' : Unit13.HasDegreewiseCoproducts U ((SimplicialObject.const C).obj X') :=
    Unit13.degreewiseCoproductInstance U ((SimplicialObject.const C).obj X') hU
  let _ := Unit13.degreewiseCoproductInstanceAt hX Z
  let _ := Unit13.degreewiseCoproductInstanceAt hX' Z
  change
    Sigma.ι (fun _ : U.obj Z => ((SimplicialObject.const C).obj X).obj Z) u ≫
        (((productWithSimplicialSetBy U hU).map ((SimplicialObject.const C).map f)).app Z ≫
          γ.app Z) =
      f ≫ (Sigma.ι (fun _ : U.obj Z => ((SimplicialObject.const C).obj X').obj Z) u ≫
        γ.app Z)
  calc
    _ = (Sigma.ι (fun _ : U.obj Z => ((SimplicialObject.const C).obj X).obj Z) u ≫
        ((productWithSimplicialSetBy U hU).map ((SimplicialObject.const C).map f)).app Z) ≫
        γ.app Z := (Category.assoc _ _ _).symm
    _ = (f ≫ Sigma.ι (fun _ : U.obj Z => ((SimplicialObject.const C).obj X').obj Z) u) ≫
        γ.app Z := by
      exact congrArg (fun k => k ≫ γ.app Z)
        (productWithSimplicialSet_injection_map_second U hU f u)
    _ = _ := Category.assoc _ _ _

private theorem homToElementsCone_map
    {C : Type u} [Category.{v} C] [HasBinaryCoproducts C]
    (U : SSet.{w}) (V : SimplicialObject C)
    (hU : Unit13.FiniteNonemptySimplicialSet U)
    {X X' : C} (f : X ⟶ X')
    (γ : Unit13.simplicialSetProduct U ((SimplicialObject.const C).obj X') hU ⟶ V) :
    homToElementsCone U V hU
        ((productWithSimplicialSetBy U hU).map ((SimplicialObject.const C).map f) ≫ γ) =
      (Functor.const U.Elements).map f ≫ homToElementsCone U V hU γ := by
  ext e
  change (Σ Z : SimplexCategoryᵒᵖ, U.obj Z) at e
  rcases e with ⟨Z, u⟩
  have he : Functor.elementsMk U Z u = ⟨Z, u⟩ := by rfl
  rw [← he]
  simp only [NatTrans.comp_app]
  let hX : Unit13.HasDegreewiseCoproducts U ((SimplicialObject.const C).obj X) :=
    Unit13.degreewiseCoproductInstance U ((SimplicialObject.const C).obj X) hU
  let hX' : Unit13.HasDegreewiseCoproducts U ((SimplicialObject.const C).obj X') :=
    Unit13.degreewiseCoproductInstance U ((SimplicialObject.const C).obj X') hU
  let _ := Unit13.degreewiseCoproductInstanceAt hX Z
  let _ := Unit13.degreewiseCoproductInstanceAt hX' Z
  change
    Sigma.ι (fun _ : U.obj Z => ((SimplicialObject.const C).obj X).obj Z) u ≫
        (((productWithSimplicialSetBy U hU).map ((SimplicialObject.const C).map f)).app Z ≫
          γ.app Z) =
      f ≫ (Sigma.ι (fun _ : U.obj Z => ((SimplicialObject.const C).obj X').obj Z) u ≫
        γ.app Z)
  calc
    _ = (Sigma.ι (fun _ : U.obj Z => ((SimplicialObject.const C).obj X).obj Z) u ≫
        ((productWithSimplicialSetBy U hU).map ((SimplicialObject.const C).map f)).app Z) ≫
        γ.app Z := (Category.assoc _ _ _).symm
    _ = (f ≫ Sigma.ι (fun _ : U.obj Z => ((SimplicialObject.const C).obj X').obj Z) u) ≫
        γ.app Z := by
      exact congrArg (fun k => k ≫ γ.app Z)
        (productWithSimplicialSet_injection_map_second U hU f u)
    _ = _ := Category.assoc _ _ _

/-
The first existence lemma in the source uses countable limits.  The finite
version is stated separately below because it is the one used to construct
the full simplicial Hom object.
-/
theorem homZero_isRepresentable_countable
    {C : Type u} [Category.{v} C] [HasBinaryCoproducts C]
    [HasCountableLimits C]
    (U : SSet.{w}) (V : SimplicialObject C)
    (hU : Unit13.FiniteNonemptySimplicialSet U) :
    (homZeroFunctor U V hU).IsRepresentable := by
  sorry

theorem homZero_isRepresentable_finite
    {C : Type u} [Category.{v} C] [HasBinaryCoproducts C]
    [HasFiniteLimits C]
    (U : SSet.{w}) (V : SimplicialObject C)
    (hU : Unit13.FiniteNonemptySimplicialSet U)
    (hUdeg : EventuallyDegenerate U) :
    (homZeroFunctor U V hU).IsRepresentable := by
  sorry

/-! ## The Hom object and its universal property -/

/-- A simplicial object `H` satisfies the source's definition of `Hom(U,V)`. -/
def IsHomObject
    {C : Type u} [Category.{v} C] [HasBinaryCoproducts C]
    (U : SSet.{w}) (V H : SimplicialObject C)
    (hU : Unit13.FiniteNonemptySimplicialSet U) : Prop :=
  Nonempty ((homFunctor U V hU).RepresentableBy H)

theorem hom_isRepresentable
    {C : Type u} [Category.{v} C] [HasBinaryCoproducts C]
    [HasFiniteLimits C]
    (U : SSet.{w}) (V : SimplicialObject C)
    (hU : Unit13.FiniteNonemptySimplicialSet U)
    (hUdeg : EventuallyDegenerate U) :
    (homFunctor U V hU).IsRepresentable := by
  sorry

/-- The chosen representing object for `Hom(U,V)`. -/
noncomputable def hom
    {C : Type u} [Category.{v} C] [HasBinaryCoproducts C]
    [HasFiniteLimits C]
    (U : SSet.{w}) (V : SimplicialObject C)
    (hU : Unit13.FiniteNonemptySimplicialSet U)
    (hUdeg : EventuallyDegenerate U) : SimplicialObject C := by
  letI : (homFunctor U V hU).IsRepresentable :=
    hom_isRepresentable U V hU hUdeg
  exact (homFunctor U V hU).reprX

theorem hom_isHomObject
    {C : Type u} [Category.{v} C] [HasBinaryCoproducts C]
    [HasFiniteLimits C]
    (U : SSet.{w}) (V : SimplicialObject C)
    (hU : Unit13.FiniteNonemptySimplicialSet U)
    (hUdeg : EventuallyDegenerate U) :
    IsHomObject U V (hom U V hU hUdeg) hU := by
  sorry

/-- The source's functorial universal-property bijection. -/
noncomputable def productWithSimplicialSetMapSecond
    {C : Type u} [Category.{v} C] [HasBinaryCoproducts C]
    (U : SSet.{w}) (hU : Unit13.FiniteNonemptySimplicialSet U)
    {W W' : SimplicialObject C} (f : W ⟶ W') :
    Unit13.simplicialSetProduct U W hU ⟶
      Unit13.simplicialSetProduct U W' hU := by
  let U₀ : Unit13.FSSets.{w} := ⟨U, hU⟩
  let f₀ : U₀ ⟶ U₀ := ObjectProperty.homMk (𝟙 U)
  exact Unit13.productWithSimplicialSetMap f₀ f

noncomputable def homRepresentableBy
    {C : Type u} [Category.{v} C] [HasBinaryCoproducts C]
    [HasFiniteLimits C]
    (U : SSet.{w}) (V : SimplicialObject C)
    (hU : Unit13.FiniteNonemptySimplicialSet U)
    (hUdeg : EventuallyDegenerate U) :
    (homFunctor U V hU).RepresentableBy (hom U V hU hUdeg) :=
  (hom_isHomObject U V hU hUdeg).some

noncomputable def homHomEquiv
    {C : Type u} [Category.{v} C] [HasBinaryCoproducts C]
    [HasFiniteLimits C]
    (U : SSet.{w}) (V : SimplicialObject C)
    (hU : Unit13.FiniteNonemptySimplicialSet U)
    (hUdeg : EventuallyDegenerate U) (W : SimplicialObject C) :
    (W ⟶ hom U V hU hUdeg) ≃
      (Unit13.simplicialSetProduct U W hU ⟶ V) := by
  letI : (homFunctor U V hU).IsRepresentable :=
    hom_isRepresentable U V hU hUdeg
  exact sorry

theorem homHomEquiv_comp
    {C : Type u} [Category.{v} C] [HasBinaryCoproducts C]
    [HasFiniteLimits C]
    (U : SSet.{w}) (V : SimplicialObject C)
    (hU : Unit13.FiniteNonemptySimplicialSet U)
    (hUdeg : EventuallyDegenerate U)
    {W W' : SimplicialObject C} (f : W ⟶ W')
    (g : W' ⟶ hom U V hU hUdeg) :
    homHomEquiv U V hU hUdeg W (f ≫ g) =
      productWithSimplicialSetMapSecond U hU f ≫
        homHomEquiv U V hU hUdeg W' g := by
  sorry

/-! ## The induced simplicial maps and the expected degree formula -/

/-- The map of `Hom(U,V)` associated to a morphism in `Δ`. -/
noncomputable def homMap
    {C : Type u} [Category.{v} C] [HasBinaryCoproducts C]
    [HasFiniteLimits C]
    (U : SSet.{w}) (V : SimplicialObject C)
    (hU : Unit13.FiniteNonemptySimplicialSet U)
    (hUdeg : EventuallyDegenerate U)
    {m n : ℕ} (φ : SimplexCategory.mk m ⟶ SimplexCategory.mk n) :
    (hom U V hU hUdeg).obj (op (SimplexCategory.mk n)) ⟶
      (hom U V hU hUdeg).obj (op (SimplexCategory.mk m)) :=
  (hom U V hU hUdeg).map φ.op

theorem finiteNonempty_product_standardSimplex
    (U : SSet.{w}) (hU : Unit13.FiniteNonemptySimplicialSet U)
    (n : ℕ) :
    Unit13.FiniteNonemptySimplicialSet
      (U ⊗ (Δ[n] : SSet.{w})) := by
  sorry

theorem eventuallyDegenerate_product_standardSimplex
    (U : SSet.{w}) (hUdeg : EventuallyDegenerate U) (n : ℕ) :
    EventuallyDegenerate (U ⊗ (Δ[n] : SSet.{w})) := by
  sorry

noncomputable def homZeroFinite
    {C : Type u} [Category.{v} C] [HasBinaryCoproducts C]
    [HasFiniteLimits C]
    (U : SSet.{w}) (V : SimplicialObject C)
    (hU : Unit13.FiniteNonemptySimplicialSet U)
    (hUdeg : EventuallyDegenerate U) : C := by
  letI : (homZeroFunctor U V hU).IsRepresentable :=
    homZero_isRepresentable_finite U V hU hUdeg
  exact (homZeroFunctor U V hU).reprX

noncomputable def homZeroFiniteRepresentableBy
    {C : Type u} [Category.{v} C] [HasBinaryCoproducts C]
    [HasFiniteLimits C]
    (U : SSet.{w}) (V : SimplicialObject C)
    (hU : Unit13.FiniteNonemptySimplicialSet U)
    (hUdeg : EventuallyDegenerate U) :
    (homZeroFunctor U V hU).RepresentableBy
      (homZeroFinite U V hU hUdeg) := by
  letI : (homZeroFunctor U V hU).IsRepresentable :=
    homZero_isRepresentable_finite U V hU hUdeg
  simpa [homZeroFinite] using
    (homZeroFunctor U V hU).representableBy

noncomputable def homZeroFiniteHomEquiv
    {C : Type u} [Category.{v} C] [HasBinaryCoproducts C]
    [HasFiniteLimits C]
    (U : SSet.{w}) (V : SimplicialObject C)
    (hU : Unit13.FiniteNonemptySimplicialSet U)
    (hUdeg : EventuallyDegenerate U) (X : C) :
    (X ⟶ homZeroFinite U V hU hUdeg) ≃
      (Unit13.simplicialSetProduct U
        ((SimplicialObject.const C).obj X) hU ⟶ V) := by
  letI : (homZeroFunctor U V hU).IsRepresentable :=
    homZero_isRepresentable_finite U V hU hUdeg
  simpa only [homZeroFunctor_obj] using
    (homZeroFiniteRepresentableBy U V hU hUdeg).homEquiv (X := X)

/-- The source's expected identification of the `n`th term with a degree-zero Hom object. -/
theorem hom_obj_iso_exists
    {C : Type u} [Category.{v} C] [HasBinaryCoproducts C]
    [HasFiniteLimits C]
    (U : SSet.{w}) (V : SimplicialObject C)
    (hU : Unit13.FiniteNonemptySimplicialSet U)
    (hUdeg : EventuallyDegenerate U) (n : ℕ) :
    Nonempty
      ((hom U V hU hUdeg).obj (op (SimplexCategory.mk n)) ≅
        homZeroFinite (U ⊗ (Δ[n] : SSet.{w})) V
          (finiteNonempty_product_standardSimplex U hU n)
          (eventuallyDegenerate_product_standardSimplex U hUdeg n)) := by
  sorry

noncomputable def hom_obj_iso
    {C : Type u} [Category.{v} C] [HasBinaryCoproducts C]
    [HasFiniteLimits C]
    (U : SSet.{w}) (V : SimplicialObject C)
    (hU : Unit13.FiniteNonemptySimplicialSet U)
    (hUdeg : EventuallyDegenerate U) (n : ℕ) :
    (hom U V hU hUdeg).obj (op (SimplexCategory.mk n)) ≅
      homZeroFinite (U ⊗ (Δ[n] : SSet.{w})) V
        (finiteNonempty_product_standardSimplex U hU n)
        (eventuallyDegenerate_product_standardSimplex U hUdeg n) :=
  (hom_obj_iso_exists U V hU hUdeg n).some

/-! ## Precomposition and the fibre-product lemma -/

/-
The universal property gives the map induced by a simplicial map
`a : U ⟶ V`: the universal map for `Hom(V,T)` is precomposed with
`id × a` and then transported back through the universal property for
`Hom(U,T)`.
-/
noncomputable def homPrecomp
    {C : Type u} [Category.{v} C] [HasBinaryCoproducts C]
    [HasFiniteLimits C]
    {U V : SSet.{w}} (a : U ⟶ V)
    (T : SimplicialObject C)
    (hU : Unit13.FiniteNonemptySimplicialSet U)
    (hV : Unit13.FiniteNonemptySimplicialSet V)
    (hUdeg : EventuallyDegenerate U)
    (hVdeg : EventuallyDegenerate V) :
    hom V T hV hVdeg ⟶ hom U T hU hUdeg := by
  let U₀ : Unit13.FSSets.{w} := ⟨U, hU⟩
  let V₀ : Unit13.FSSets.{w} := ⟨V, hV⟩
  let a₀ : U₀ ⟶ V₀ := ObjectProperty.homMk a
  let p : Unit13.simplicialSetProduct U
      (hom V T hV hVdeg) hU ⟶
      Unit13.simplicialSetProduct V
        (hom V T hV hVdeg) hV :=
    Unit13.productWithSimplicialSetMap a₀ (𝟙 _)
  exact (homHomEquiv U T hU hUdeg (hom V T hV hVdeg)).symm
    (p ≫ homHomEquiv V T hV hVdeg (hom V T hV hVdeg) (𝟙 _))

theorem homPrecomp_hasDegreewiseFibreProducts
    {C : Type u} [Category.{v} C] [HasBinaryCoproducts C]
    [HasFiniteLimits C]
    {U V W : SSet.{w}} (a : U ⟶ V) (b : U ⟶ W)
    (T : SimplicialObject C)
    (hU : Unit13.FiniteNonemptySimplicialSet U)
    (hV : Unit13.FiniteNonemptySimplicialSet V)
    (hW : Unit13.FiniteNonemptySimplicialSet W)
    (hUdeg : EventuallyDegenerate U)
    (hVdeg : EventuallyDegenerate V)
    (hWdeg : EventuallyDegenerate W) :
    Unit07.HasDegreewiseFibreProducts
      (homPrecomp a T hU hV hUdeg hVdeg)
      (homPrecomp b T hU hW hUdeg hWdeg) := by
  intro n
  infer_instance

noncomputable def homFibreProduct
    {C : Type u} [Category.{v} C] [HasBinaryCoproducts C]
    [HasFiniteLimits C]
    {U V W : SSet.{w}} (a : U ⟶ V) (b : U ⟶ W)
    (T : SimplicialObject C)
    (hU : Unit13.FiniteNonemptySimplicialSet U)
    (hV : Unit13.FiniteNonemptySimplicialSet V)
    (hW : Unit13.FiniteNonemptySimplicialSet W)
    (hUdeg : EventuallyDegenerate U)
    (hVdeg : EventuallyDegenerate V)
    (hWdeg : EventuallyDegenerate W) : SimplicialObject C :=
  Unit07.simplicialFibreProduct
    (homPrecomp a T hU hV hUdeg hVdeg)
    (homPrecomp b T hU hW hUdeg hWdeg)
    (homPrecomp_hasDegreewiseFibreProducts a b T hU hV hW
      hUdeg hVdeg hWdeg)

noncomputable def homFibreProductFst
    {C : Type u} [Category.{v} C] [HasBinaryCoproducts C]
    [HasFiniteLimits C]
    {U V W : SSet.{w}} (a : U ⟶ V) (b : U ⟶ W)
    (T : SimplicialObject C)
    (hU : Unit13.FiniteNonemptySimplicialSet U)
    (hV : Unit13.FiniteNonemptySimplicialSet V)
    (hW : Unit13.FiniteNonemptySimplicialSet W)
    (hUdeg : EventuallyDegenerate U)
    (hVdeg : EventuallyDegenerate V)
    (hWdeg : EventuallyDegenerate W) :
    homFibreProduct a b T hU hV hW hUdeg hVdeg hWdeg ⟶
      hom V T hV hVdeg :=
  Unit07.simplicialFibreProductFst
    (homPrecomp a T hU hV hUdeg hVdeg)
    (homPrecomp b T hU hW hUdeg hWdeg)
    (homPrecomp_hasDegreewiseFibreProducts a b T hU hV hW
      hUdeg hVdeg hWdeg)

noncomputable def homFibreProductSnd
    {C : Type u} [Category.{v} C] [HasBinaryCoproducts C]
    [HasFiniteLimits C]
    {U V W : SSet.{w}} (a : U ⟶ V) (b : U ⟶ W)
    (T : SimplicialObject C)
    (hU : Unit13.FiniteNonemptySimplicialSet U)
    (hV : Unit13.FiniteNonemptySimplicialSet V)
    (hW : Unit13.FiniteNonemptySimplicialSet W)
    (hUdeg : EventuallyDegenerate U)
    (hVdeg : EventuallyDegenerate V)
    (hWdeg : EventuallyDegenerate W) :
    homFibreProduct a b T hU hV hW hUdeg hVdeg hWdeg ⟶
      hom W T hW hWdeg :=
  Unit07.simplicialFibreProductSnd
    (homPrecomp a T hU hV hUdeg hVdeg)
    (homPrecomp b T hU hW hUdeg hWdeg)
    (homPrecomp_hasDegreewiseFibreProducts a b T hU hV hW
      hUdeg hVdeg hWdeg)

theorem homFibreProduct_isPullback
    {C : Type u} [Category.{v} C] [HasBinaryCoproducts C]
    [HasFiniteLimits C]
    {U V W : SSet.{w}} (a : U ⟶ V) (b : U ⟶ W)
    (T : SimplicialObject C)
    (hU : Unit13.FiniteNonemptySimplicialSet U)
    (hV : Unit13.FiniteNonemptySimplicialSet V)
    (hW : Unit13.FiniteNonemptySimplicialSet W)
    (hUdeg : EventuallyDegenerate U)
    (hVdeg : EventuallyDegenerate V)
    (hWdeg : EventuallyDegenerate W) :
    IsPullback
      (homFibreProductFst a b T hU hV hW hUdeg hVdeg hWdeg)
      (homFibreProductSnd a b T hU hV hW hUdeg hVdeg hWdeg)
      (homPrecomp a T hU hV hUdeg hVdeg)
      (homPrecomp b T hU hW hUdeg hWdeg) := by
  exact Unit07.simplicialFibreProductIsPullback
    (homPrecomp a T hU hV hUdeg hVdeg)
    (homPrecomp b T hU hW hUdeg hWdeg)
    (homPrecomp_hasDegreewiseFibreProducts a b T hU hV hW
      hUdeg hVdeg hWdeg)

theorem finiteNonempty_pushout
    {U V W : SSet.{w}} (a : U ⟶ V) (b : U ⟶ W)
    (hU : Unit13.FiniteNonemptySimplicialSet U)
    (hV : Unit13.FiniteNonemptySimplicialSet V)
    (hW : Unit13.FiniteNonemptySimplicialSet W) :
    Unit13.FiniteNonemptySimplicialSet (pushout a b) := by
  sorry

theorem eventuallyDegenerate_pushout
    {U V W : SSet.{w}} (a : U ⟶ V) (b : U ⟶ W)
    (hUdeg : EventuallyDegenerate U)
    (hVdeg : EventuallyDegenerate V)
    (hWdeg : EventuallyDegenerate W) :
    EventuallyDegenerate (pushout a b) := by
  sorry

/-- Existence of the source's canonical isomorphism of representing objects. -/
theorem hom_fibreProduct_iso_exists
    {C : Type u} [Category.{v} C] [HasBinaryCoproducts C]
    [HasFiniteLimits C]
    {U V W : SSet.{w}} (a : U ⟶ V) (b : U ⟶ W)
    (T : SimplicialObject C)
    (hU : Unit13.FiniteNonemptySimplicialSet U)
    (hV : Unit13.FiniteNonemptySimplicialSet V)
    (hW : Unit13.FiniteNonemptySimplicialSet W)
    (hUdeg : EventuallyDegenerate U)
    (hVdeg : EventuallyDegenerate V)
    (hWdeg : EventuallyDegenerate W) :
    Nonempty
      (homFibreProduct a b T hU hV hW hUdeg hVdeg hWdeg ≅
        hom (pushout a b) T
          (finiteNonempty_pushout a b hU hV hW)
          (eventuallyDegenerate_pushout a b hUdeg hVdeg hWdeg)) := by
  sorry

/-- The source's fibre-product identity, expressed by the canonical isomorphism of representing objects. -/
noncomputable def hom_fibreProduct_iso
    {C : Type u} [Category.{v} C] [HasBinaryCoproducts C]
    [HasFiniteLimits C]
    {U V W : SSet.{w}} (a : U ⟶ V) (b : U ⟶ W)
    (T : SimplicialObject C)
    (hU : Unit13.FiniteNonemptySimplicialSet U)
    (hV : Unit13.FiniteNonemptySimplicialSet V)
    (hW : Unit13.FiniteNonemptySimplicialSet W)
    (hUdeg : EventuallyDegenerate U)
    (hVdeg : EventuallyDegenerate V)
    (hWdeg : EventuallyDegenerate W) :
    homFibreProduct a b T hU hV hW hUdeg hVdeg hWdeg ≅
      hom (pushout a b) T
        (finiteNonempty_pushout a b hU hV hW)
        (eventuallyDegenerate_pushout a b hUdeg hVdeg hWdeg) :=
  (hom_fibreProduct_iso_exists a b T hU hV hW hUdeg hVdeg hWdeg).some

end Formalization.Books.Simplicial.Unit17
