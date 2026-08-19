import Formalization.Books.Simplicial.Unit07.FibreProducts
import Formalization.Books.Simplicial.Unit13.ProductsWithSimplicialSets
import Mathlib.AlgebraicTopology.SimplicialSet.Dimension
import Mathlib.AlgebraicTopology.SimplicialSet.FiniteColimits
import Mathlib.CategoryTheory.Functor.KanExtension.Pointwise
import Mathlib.CategoryTheory.Limits.Shapes.Countable
import Mathlib.CategoryTheory.Limits.Types.Pushouts
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
  rfl

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
  let : ∀ X : SimplexCategoryᵒᵖ, Finite (U.obj X) := by
    intro X
    simpa only [SimplexCategory.mk_len] using (hU X.unop.len).1
  let : Countable SimplexCategory :=
    Function.Injective.countable (f := SimplexCategory.len) (by
      intro X Y h
      cases X
      cases Y
      cases h
      rfl)
  let : Countable SimplexCategoryᵒᵖ :=
    Countable.of_equiv SimplexCategory Opposite.equivToOpposite
  let : CountableCategory U.Elements := by
    constructor
    · change Countable (Σ X : SimplexCategoryᵒᵖ, U.obj X)
      infer_instance
    · intro e e'
      change Countable {f : e.1 ⟶ e'.1 // _}
      let : Countable (e.1 ⟶ e'.1) :=
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
  simp [Unit13.simplicialSetProduct, Unit13.simplicialSetProductOf]

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
          simp [hf]
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
          exact α.app (Functor.elementsMk U Z u)
        let aZ' : ∀ u : U.obj Z', X ⟶ V.obj Z' := fun u => by
          exact α.app (Functor.elementsMk U Z' u)
        let i :
            X ⟶ (Unit13.simplicialSetProduct U ((SimplicialObject.const C).obj X) hU).obj Z := by
          dsimp [Unit13.simplicialSetProduct, Unit13.simplicialSetProductOf]
          exact Sigma.ι (fun _ : U.obj Z => ((SimplicialObject.const C).obj X).obj Z) u
        change i ≫
            (Unit13.simplicialSetProduct U ((SimplicialObject.const C).obj X) hU).map fbase ≫
              Sigma.desc aZ' = i ≫ Sigma.desc aZ ≫ V.map fbase
        dsimp [i, Unit13.simplicialSetProduct, Unit13.simplicialSetProductOf]
        simp only [Category.id_comp]
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

private def elementsNatCompatibleFamilyEquiv
    {C : Type u} [Category.{v} C]
    (U : SSet.{w}) (W V : SimplicialObject C) :
    (CategoryOfElements.π U ⋙ W ⟶ CategoryOfElements.π U ⋙ V) ≃
      Unit13.CompatibleFamily U W V where
  toFun α :=
    ⟨fun n u => α.app (Functor.elementsMk U (op (SimplexCategory.mk n)) u), by
      intro m n φ u
      exact α.naturality (CategoryOfElements.homMk
        (Functor.elementsMk U (op (SimplexCategory.mk n)) u)
        (Functor.elementsMk U (op (SimplexCategory.mk m)) (U.map φ.op u))
        φ.op rfl)⟩
  invFun f :=
    { app := fun e => f.1 e.1.unop.len e.2
      naturality := by
        rintro ⟨X, u⟩ ⟨Y, v⟩ g
        cases X with
        | op X =>
          cases X with
          | mk m =>
            cases Y with
            | op Y =>
              cases Y with
              | mk n =>
                change W.map g.val ≫ f.1 n v = f.1 m u ≫ V.map g.val
                simpa [g.property] using f.2 g.val.unop u }
  left_inv := by
    intro α
    ext e
    rcases e with ⟨X, u⟩
    cases X with
    | op X =>
      cases X with
      | mk n => rfl
  right_inv := by
    intro f
    apply Subtype.ext
    funext n u
    rfl

private noncomputable def elementsNatHomEquiv
    {C : Type u} [Category.{v} C] [HasBinaryCoproducts C]
    (U : SSet.{w}) (W V : SimplicialObject C)
    (hU : Unit13.FiniteNonemptySimplicialSet U) :
    (CategoryOfElements.π U ⋙ W ⟶ CategoryOfElements.π U ⋙ V) ≃
      (Unit13.simplicialSetProduct U W hU ⟶ V) :=
  (elementsNatCompatibleFamilyEquiv U W V).trans
    (Unit13.finiteSimplicialSetProduct_hom_equiv U W hU V).symm

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
private noncomputable def homZeroRepresentableByLimit
    {C : Type u} [Category.{v} C] [HasBinaryCoproducts C]
    (U : SSet.{w}) (V : SimplicialObject C)
    (hU : Unit13.FiniteNonemptySimplicialSet U)
    [HasLimit (simplicialSetElementsDiagram U V)] :
    (homZeroFunctor U V hU).RepresentableBy
      (limit (simplicialSetElementsDiagram U V)) := by
  let D := simplicialSetElementsDiagram U V
  let L := limit D
  let coneEquiv {X : C} :
      (X ⟶ L) ≃ ((Functor.const U.Elements).obj X ⟶ D) :=
    { toFun := fun f =>
        { app := fun e => f ≫ limit.π D e
          naturality := by
            intro e e' g
            simp }
      invFun := fun α => limit.lift D { pt := X, π := α }
      left_inv := by
        intro f
        apply limit.hom_ext
        intro e
        simp
      right_inv := by
        intro α
        ext e
        simp }
  let q {X : C} := elementsConeHomEquiv U V hU (X := X)
  let h {X : C} := (coneEquiv (X := X)).trans (q (X := X))
  let R : (homZeroFunctor U V hU).RepresentableBy L :=
    { homEquiv := fun {X} => h (X := X)
      homEquiv_comp := by
        intro X X' f g
        have hcomp :
            h (X := X) (f ≫ g) =
              (productWithSimplicialSetBy U hU).map ((SimplicialObject.const C).map f) ≫
                h (X := X') g := by
          apply (q (X := X)).symm.injective
          dsimp only [h]
          rw [Equiv.trans_apply, Equiv.trans_apply, Equiv.symm_apply_apply]
          change coneEquiv (X := X) (f ≫ g) =
            homToElementsCone U V hU
              ((productWithSimplicialSetBy U hU).map
                  ((SimplicialObject.const C).map f) ≫
                q (X := X') (coneEquiv (X := X') g))
          rw [homToElementsCone_map]
          have hq : homToElementsCone U V hU
                (q (X := X') (coneEquiv (X := X') g)) =
              coneEquiv (X := X') g := by
            exact (q (X := X')).symm_apply_apply _
          rw [hq]
          ext e
          simp [coneEquiv, Category.assoc]
        change h (X := X) (f ≫ g) =
          (homZeroFunctor U V hU).map f.op (h (X := X') g)
        rw [homZero_map_apply]
        exact hcomp }
  exact R

private theorem homZero_isRepresentable_of_hasLimit
    {C : Type u} [Category.{v} C] [HasBinaryCoproducts C]
    (U : SSet.{w}) (V : SimplicialObject C)
    (hU : Unit13.FiniteNonemptySimplicialSet U)
    [HasLimit (simplicialSetElementsDiagram U V)] :
    (homZeroFunctor U V hU).IsRepresentable :=
  (homZeroRepresentableByLimit U V hU).isRepresentable

theorem homZero_isRepresentable_countable
    {C : Type u} [Category.{v} C] [HasBinaryCoproducts C]
    [HasCountableLimits C]
    (U : SSet.{w}) (V : SimplicialObject C)
    (hU : Unit13.FiniteNonemptySimplicialSet U) :
    (homZeroFunctor U V hU).IsRepresentable := by
  let : HasLimit (simplicialSetElementsDiagram U V) :=
    hasLimit_simplicialSetElementsDiagram U V hU
  exact homZero_isRepresentable_of_hasLimit U V hU

private theorem hasLimit_simplicialSetElementsDiagram_finite
    {C : Type u} [Category.{v} C] [HasBinaryCoproducts C]
    [HasFiniteLimits C]
    (U : SSet.{w}) (V : SimplicialObject C)
    (hU : Unit13.FiniteNonemptySimplicialSet U)
    (hUdeg : EventuallyDegenerate U) :
    HasLimit (simplicialSetElementsDiagram U V) := by
  rcases hUdeg with ⟨d, hd⟩
  let : U.HasDimensionLT d := hd
  let : ∀ X : SimplexCategoryᵒᵖ, Finite (U.obj X) := fun X => by
    simpa only [SimplexCategory.mk_len] using (hU X.unop.len).1
  let : ∀ a b : U.Elements, Finite (a ⟶ b) := fun a b => by
    change Finite {f : a.1 ⟶ b.1 // _}
    let : Finite (a.1 ⟶ b.1) :=
      Finite.of_equiv _ (opEquiv a.1 b.1).symm
    apply Finite.of_injective Subtype.val
    exact Subtype.val_injective
  let : Finite (SimplexCategory.Truncated (d * d)) := by
    let f : SimplexCategory.Truncated (d * d) → Fin (d * d + 1) :=
      fun X => ⟨X.obj.len, Nat.lt_succ_of_le X.property⟩
    apply Finite.of_injective f
    intro X Y h
    cases X with
    | mk X hX =>
      cases Y with
      | mk Y hY =>
        apply ObjectProperty.FullSubcategory.ext
        exact SimplexCategory.ext (congrArg Fin.val h)
  let : Finite ((SimplexCategory.Truncated (d * d))ᵒᵖ) := by
    apply Finite.of_injective (fun X => X.unop)
    intro X Y h
    exact congrArg op h
  let : Finite (Unit11.boundedElements U d) := by
    let f : Unit11.boundedElements U d →
        Σ X : (SimplexCategory.Truncated (d * d))ᵒᵖ,
          U.obj (op X.unop.obj) :=
      fun e => ⟨op ⟨e.obj.1.unop, Nat.le_of_lt_succ e.property⟩, e.obj.2⟩
    apply Finite.of_injective f
    intro X Y h
    apply ObjectProperty.FullSubcategory.ext
    exact congrArg
      (fun z => (⟨op z.1.unop.obj, z.2⟩ : U.Elements)) h
  let : ∀ a b : Unit11.boundedElements U d, Finite (a ⟶ b) := fun a b => by
    apply Finite.of_injective (fun f => f.hom)
    intro f g h
    apply ObjectProperty.hom_ext
    exact h
  let : Finite (ULiftHom.{w} (Unit11.boundedElements U d)) :=
    Finite.of_equiv _ ULiftHom.objEquiv
  let : ∀ a b : ULiftHom.{w} (Unit11.boundedElements U d),
      Finite (a ⟶ b) := fun a b => by
    change Finite (ULift.{w} (a.objDown ⟶ b.objDown))
    infer_instance
  let : FinCategory (ULiftHom.{w} (Unit11.boundedElements U d)) :=
    { fintypeObj := Fintype.ofFinite _
      fintypeHom := fun a b => Fintype.ofFinite _ }
  let e := (ULiftHom.equiv (C := Unit11.boundedElements U d)).symm
  let : HasLimit
      (e.functor ⋙ Unit11.boundedElementsInclusion U d ⋙
        simplicialSetElementsDiagram U V) := by
    infer_instance
  let : HasLimit
      (Unit11.boundedElementsInclusion U d ⋙
        simplicialSetElementsDiagram U V) :=
    hasLimit_of_equivalence_comp e
  let : (Unit11.boundedElementsInclusion U d).Initial :=
    Unit11.boundedElementsInclusion_initial U d
  let : HasLimit (simplicialSetElementsDiagram U V) :=
    Functor.Initial.hasLimit_of_comp (Unit11.boundedElementsInclusion U d)
  infer_instance

theorem homZero_isRepresentable_finite
    {C : Type u} [Category.{v} C] [HasBinaryCoproducts C]
    [HasFiniteLimits C]
    (U : SSet.{w}) (V : SimplicialObject C)
    (hU : Unit13.FiniteNonemptySimplicialSet U)
    (hUdeg : EventuallyDegenerate U) :
    (homZeroFunctor U V hU).IsRepresentable := by
  let : HasLimit (simplicialSetElementsDiagram U V) :=
    hasLimit_simplicialSetElementsDiagram_finite U V hU hUdeg
  exact homZero_isRepresentable_of_hasLimit U V hU

/-! ## The Hom object and its universal property -/

/-- A simplicial object `H` satisfies the source's definition of `Hom(U,V)`. -/
def IsHomObject
    {C : Type u} [Category.{v} C] [HasBinaryCoproducts C]
    (U : SSet.{w}) (V H : SimplicialObject C)
    (hU : Unit13.FiniteNonemptySimplicialSet U) : Prop :=
  Nonempty ((homFunctor U V hU).RepresentableBy H)

private def productElementsToStructuredArrow
    (U : SSet.{w}) (n : ℕ) :
    (U ⊗ (Δ[n] : SSet.{w})).Elements ⥤
      StructuredArrow (op (SimplexCategory.mk n)) (CategoryOfElements.π U) where
  obj e := StructuredArrow.mk (Y := Functor.elementsMk U e.1 e.2.1)
    (SSet.stdSimplex.objEquiv.{w} e.2.2).op
  map {e e'} g := StructuredArrow.homMk
    (CategoryOfElements.homMk _ _ g.val (by
      have hg := g.property
      change (U.map g.val e.2.1,
        (Δ[n] : SSet.{w}).map g.val e.2.2) = e'.2 at hg
      exact congrArg Prod.fst hg)) (by
        apply Quiver.Hom.unop_inj
        have hg := g.property
        change (U.map g.val e.2.1,
          (Δ[n] : SSet.{w}).map g.val e.2.2) = e'.2 at hg
        have hs := congrArg Prod.snd hg
        change g.val.unop ≫ SSet.stdSimplex.objEquiv.{w} e.2.2 =
          SSet.stdSimplex.objEquiv.{w} e'.2.2
        simpa [SSet.stdSimplex.map_apply] using
          congrArg SSet.stdSimplex.objEquiv.{w} hs)

private def structuredArrowToProductElements
    (U : SSet.{w}) (n : ℕ) :
    StructuredArrow (op (SimplexCategory.mk n)) (CategoryOfElements.π U) ⥤
      (U ⊗ (Δ[n] : SSet.{w})).Elements where
  obj e := Functor.elementsMk (U ⊗ (Δ[n] : SSet.{w})) e.right.1
    (e.right.2, SSet.stdSimplex.objEquiv.{w}.symm e.hom.unop)
  map {e e'} g := CategoryOfElements.homMk _ _ g.right.val (by
    change (U.map g.right.val e.right.2,
      (Δ[n] : SSet.{w}).map g.right.val
        (SSet.stdSimplex.objEquiv.{w}.symm e.hom.unop)) =
      (e'.right.2, SSet.stdSimplex.objEquiv.{w}.symm e'.hom.unop)
    apply Prod.ext
    · exact g.right.property
    · change (Δ[n] : SSet.{w}).map g.right.val
          (SSet.stdSimplex.objEquiv.{w}.symm e.hom.unop) =
        SSet.stdSimplex.objEquiv.{w}.symm e'.hom.unop
      apply SSet.stdSimplex.objEquiv.{w}.injective
      change g.right.val.unop ≫ e.hom.unop = e'.hom.unop
      exact congrArg Quiver.Hom.unop g.w)

private def productElementsStructuredArrowEquivalence
    (U : SSet.{w}) (n : ℕ) :
    (U ⊗ (Δ[n] : SSet.{w})).Elements ≌
      StructuredArrow (op (SimplexCategory.mk n)) (CategoryOfElements.π U) where
  functor := productElementsToStructuredArrow U n
  inverse := structuredArrowToProductElements U n
  unitIso := NatIso.ofComponents (fun e =>
    CategoryOfElements.isoMk _ _ (Iso.refl _) (by
      change (U.map (𝟙 e.1) e.2.1,
        (Δ[n] : SSet.{w}).map (𝟙 e.1) e.2.2) =
          (e.2.1, SSet.stdSimplex.objEquiv.{w}.symm
            (SSet.stdSimplex.objEquiv.{w} e.2.2))
      simp)) (by
      intro e e' f
      apply CategoryOfElements.ext
      rfl)
  counitIso := NatIso.ofComponents (fun e =>
    StructuredArrow.isoMk
      (CategoryOfElements.isoMk _ _ (Iso.refl _) (by
        change U.map (𝟙 e.right.1) e.right.2 = e.right.2
        simp)) (by
          change (SSet.stdSimplex.objEquiv.{w}
              (SSet.stdSimplex.objEquiv.{w}.symm e.hom.unop)).op ≫
            𝟙 e.right.1 = e.hom
          exact Category.comp_id _)) (by
        intro e e' f
        apply StructuredArrow.hom_ext
        apply CategoryOfElements.ext
        rfl)

private theorem finiteNonempty_product_standardSimplex_aux
    (U : SSet.{w}) (hU : Unit13.FiniteNonemptySimplicialSet U)
    (n : ℕ) :
    Unit13.FiniteNonemptySimplicialSet
      (U ⊗ (Δ[n] : SSet.{w})) := by
  intro k
  let hΔ : Unit13.FiniteNonemptySimplicialSet (Δ[n] : SSet.{w}) :=
    Unit13.standardSimplex_finite_nonempty n
  let : Finite (U.obj (op (SimplexCategory.mk k))) := (hU k).1
  let : Nonempty (U.obj (op (SimplexCategory.mk k))) := (hU k).2
  let : Finite ((Δ[n] : SSet.{w}).obj (op (SimplexCategory.mk k))) :=
    (hΔ k).1
  let : Nonempty ((Δ[n] : SSet.{w}).obj (op (SimplexCategory.mk k))) :=
    (hΔ k).2
  change Finite
      (U.obj (op (SimplexCategory.mk k)) ×
        (Δ[n] : SSet.{w}).obj (op (SimplexCategory.mk k))) ∧
    Nonempty
      (U.obj (op (SimplexCategory.mk k)) ×
        (Δ[n] : SSet.{w}).obj (op (SimplexCategory.mk k)))
  constructor <;> infer_instance

private theorem eventuallyDegenerate_product_standardSimplex_aux
    (U : SSet.{w}) (hUdeg : EventuallyDegenerate U) (n : ℕ) :
    EventuallyDegenerate (U ⊗ (Δ[n] : SSet.{w})) := by
  rcases hUdeg with ⟨d, hd⟩
  let : U.HasDimensionLT d := hd
  let : U.HasDimensionLE d := inferInstance
  refine ⟨d + n + 1, ?_⟩
  exact Unit11.product_hasDimensionLE U (Δ[n] : SSet.{w}) d n

private theorem hasPointwiseRightKanExtension_elements
    {C : Type u} [Category.{v} C] [HasBinaryCoproducts C]
    [HasFiniteLimits C]
    (U : SSet.{w}) (V : SimplicialObject C)
    (hU : Unit13.FiniteNonemptySimplicialSet U)
    (hUdeg : EventuallyDegenerate U) :
    (CategoryOfElements.π U).HasPointwiseRightKanExtension
      (CategoryOfElements.π U ⋙ V) := by
  rintro ⟨Y⟩
  rcases Y with ⟨n⟩
  let : HasLimit
      (simplicialSetElementsDiagram (U ⊗ (Δ[n] : SSet.{w})) V) :=
    hasLimit_simplicialSetElementsDiagram_finite
      (U ⊗ (Δ[n] : SSet.{w})) V
      (finiteNonempty_product_standardSimplex_aux U hU n)
      (eventuallyDegenerate_product_standardSimplex_aux U hUdeg n)
  let e := productElementsStructuredArrowEquivalence U n
  have : HasLimit
      (e.functor ⋙
        StructuredArrow.proj (op (SimplexCategory.mk n))
          (CategoryOfElements.π U) ⋙
        CategoryOfElements.π U ⋙ V) := by
    change HasLimit
      (simplicialSetElementsDiagram (U ⊗ (Δ[n] : SSet.{w})) V)
    infer_instance
  exact hasLimit_of_equivalence_comp e

private def elementsWhiskerLeft
    {C : Type u} [Category.{v} C]
    (U : SSet.{w}) {W W' : SimplicialObject C} (f : W ⟶ W') :
    CategoryOfElements.π U ⋙ W ⟶ CategoryOfElements.π U ⋙ W' where
  app e := f.app e.1
  naturality _ _ g := f.naturality g.val

private theorem elementsNatHomEquiv_whiskerLeft
    {C : Type u} [Category.{v} C] [HasBinaryCoproducts C]
    (U : SSet.{w}) (V : SimplicialObject C)
    (hU : Unit13.FiniteNonemptySimplicialSet U)
    {W W' : SimplicialObject C} (f : W ⟶ W')
    (α : CategoryOfElements.π U ⋙ W' ⟶
      CategoryOfElements.π U ⋙ V) :
    elementsNatHomEquiv U W V hU
        (elementsWhiskerLeft U f ≫ α) =
      (productWithSimplicialSetBy U hU).map f ≫
        elementsNatHomEquiv U W' V hU α := by
  let qW := Unit13.finiteSimplicialSetProduct_hom_equiv U W hU V
  let qW' := Unit13.finiteSimplicialSetProduct_hom_equiv U W' hU V
  let p := elementsNatCompatibleFamilyEquiv U W' V
  let γ := elementsNatHomEquiv U W' V hU α
  have hγ : qW' γ = p α := by
    exact qW'.apply_symm_apply (p α)
  apply qW.injective
  change qW (qW.symm ((elementsNatCompatibleFamilyEquiv U W V)
      (elementsWhiskerLeft U f ≫ α))) =
    qW ((productWithSimplicialSetBy U hU).map f ≫ γ)
  rw [qW.apply_symm_apply]
  apply Subtype.ext
  funext n z
  let hW := Unit13.degreewiseCoproductInstance U W hU
  let hW' := Unit13.degreewiseCoproductInstance U W' hU
  let _ := Unit13.degreewiseCoproductInstanceAt hW (op (SimplexCategory.mk n))
  let _ := Unit13.degreewiseCoproductInstanceAt hW' (op (SimplexCategory.mk n))
  have hγz := congrArg (fun k : Unit13.CompatibleFamily U W' V => k.1 n z) hγ
  change
    f.app (op (SimplexCategory.mk n)) ≫
        α.app (Functor.elementsMk U (op (SimplexCategory.mk n)) z) =
      Sigma.ι (fun _ : U _⦋n⦌ => W.obj (op (SimplexCategory.mk n))) z ≫
        (((productWithSimplicialSetBy U hU).map f).app
          (op (SimplexCategory.mk n)) ≫ γ.app (op (SimplexCategory.mk n)))
  dsimp [qW', p, Unit13.finiteSimplicialSetProduct_hom_equiv,
    Unit13.simplicialSetProduct_hom_equiv,
    elementsNatCompatibleFamilyEquiv] at hγz
  change Sigma.ι (fun _ : U _⦋n⦌ => W'.obj (op (SimplexCategory.mk n))) z ≫
      γ.app (op (SimplexCategory.mk n)) =
    α.app (Functor.elementsMk U (op (SimplexCategory.mk n)) z) at hγz
  calc
    _ = f.app (op (SimplexCategory.mk n)) ≫
        (Sigma.ι (fun _ : U _⦋n⦌ => W'.obj (op (SimplexCategory.mk n))) z ≫
          γ.app (op (SimplexCategory.mk n))) := by
      exact congrArg (fun k => f.app (op (SimplexCategory.mk n)) ≫ k) hγz.symm
    _ = (f.app (op (SimplexCategory.mk n)) ≫
        Sigma.ι (fun _ : U _⦋n⦌ => W'.obj (op (SimplexCategory.mk n))) z) ≫
          γ.app (op (SimplexCategory.mk n)) := (Category.assoc _ _ _).symm
    _ = (Sigma.ι (fun _ : U _⦋n⦌ => W.obj (op (SimplexCategory.mk n))) z ≫
        ((productWithSimplicialSetBy U hU).map f).app
          (op (SimplexCategory.mk n))) ≫ γ.app (op (SimplexCategory.mk n)) := by
      congr 1
      change f.app (op (SimplexCategory.mk n)) ≫
          Sigma.ι (fun _ : U _⦋n⦌ => W'.obj (op (SimplexCategory.mk n))) z =
        Sigma.ι (fun _ : U _⦋n⦌ => W.obj (op (SimplexCategory.mk n))) z ≫
          Sigma.desc (fun z => f.app (op (SimplexCategory.mk n)) ≫
            Sigma.ι (fun _ : U _⦋n⦌ => W'.obj (op (SimplexCategory.mk n))) z)
      rw [Sigma.ι_desc]
    _ = _ := Category.assoc _ _ _

private noncomputable def homPointwise
    {C : Type u} [Category.{v} C] [HasBinaryCoproducts C]
    [HasFiniteLimits C]
    (U : SSet.{w}) (V : SimplicialObject C)
    (hU : Unit13.FiniteNonemptySimplicialSet U)
    (hUdeg : EventuallyDegenerate U) : SimplicialObject C := by
  let π := CategoryOfElements.π U
  let F := π ⋙ V
  let : π.HasPointwiseRightKanExtension F :=
    hasPointwiseRightKanExtension_elements U V hU hUdeg
  exact π.pointwiseRightKanExtension F

private noncomputable def homPointwiseRepresentableBy
    {C : Type u} [Category.{v} C] [HasBinaryCoproducts C]
    [HasFiniteLimits C]
    (U : SSet.{w}) (V : SimplicialObject C)
    (hU : Unit13.FiniteNonemptySimplicialSet U)
    (hUdeg : EventuallyDegenerate U) :
    (homFunctor U V hU).RepresentableBy
      (homPointwise U V hU hUdeg) := by
  let π := CategoryOfElements.π U
  let F := π ⋙ V
  let : π.HasPointwiseRightKanExtension F :=
    hasPointwiseRightKanExtension_elements U V hU hUdeg
  let H := π.pointwiseRightKanExtension F
  let ε := π.pointwiseRightKanExtensionCounit F
  let k {W : SimplicialObject C} :=
    H.homEquivOfIsRightKanExtension ε W
  let q {W : SimplicialObject C} := elementsNatHomEquiv U W V hU
  let h {W : SimplicialObject C} := (k (W := W)).trans (q (W := W))
  let R : (homFunctor U V hU).RepresentableBy H :=
    { homEquiv := fun {W} => h (W := W)
      homEquiv_comp := by
        intro W W' f g
        change h (W := W) (f ≫ g) =
          (productWithSimplicialSetBy U hU).map f ≫ h (W := W') g
        have hk : k (W := W) (f ≫ g) =
            elementsWhiskerLeft U f ≫ k (W := W') g := by
          ext e
          dsimp [k, Functor.homEquivOfIsRightKanExtension, elementsWhiskerLeft]
          exact Category.assoc _ _ _
        dsimp only [h, Equiv.trans_apply]
        rw [hk, elementsNatHomEquiv_whiskerLeft U V hU f] }
  exact R

theorem hom_isRepresentable
    {C : Type u} [Category.{v} C] [HasBinaryCoproducts C]
    [HasFiniteLimits C]
    (U : SSet.{w}) (V : SimplicialObject C)
    (hU : Unit13.FiniteNonemptySimplicialSet U)
    (hUdeg : EventuallyDegenerate U) :
    (homFunctor U V hU).IsRepresentable :=
  (homPointwiseRepresentableBy U V hU hUdeg).isRepresentable

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
  let : (homFunctor U V hU).IsRepresentable :=
    hom_isRepresentable U V hU hUdeg
  exact ⟨(homFunctor U V hU).representableBy⟩

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
  exact (homRepresentableBy U V hU hUdeg).homEquiv

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
  change (homRepresentableBy U V hU hUdeg).homEquiv (f ≫ g) =
    productWithSimplicialSetMapSecond U hU f ≫
      (homRepresentableBy U V hU hUdeg).homEquiv g
  rw [(homRepresentableBy U V hU hUdeg).homEquiv_comp]
  rfl

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
  exact finiteNonempty_product_standardSimplex_aux U hU n

theorem eventuallyDegenerate_product_standardSimplex
    (U : SSet.{w}) (hUdeg : EventuallyDegenerate U) (n : ℕ) :
    EventuallyDegenerate (U ⊗ (Δ[n] : SSet.{w})) := by
  exact eventuallyDegenerate_product_standardSimplex_aux U hUdeg n

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
  let P := U ⊗ (Δ[n] : SSet.{w})
  let hP := finiteNonempty_product_standardSimplex U hU n
  let hPdeg := eventuallyDegenerate_product_standardSimplex U hUdeg n
  let : HasLimit (simplicialSetElementsDiagram P V) :=
    hasLimit_simplicialSetElementsDiagram_finite P V hP hPdeg
  let π := CategoryOfElements.π U
  let F := π ⋙ V
  let : π.HasPointwiseRightKanExtension F :=
    hasPointwiseRightKanExtension_elements U V hU hUdeg
  let : (homFunctor U V hU).IsRepresentable :=
    hom_isRepresentable U V hU hUdeg
  let eH : homPointwise U V hU hUdeg ≅ hom U V hU hUdeg :=
    (homPointwiseRepresentableBy U V hU hUdeg).isoReprX
  let : (homZeroFunctor P V hP).IsRepresentable :=
    homZero_isRepresentable_finite P V hP hPdeg
  let e0 : limit (simplicialSetElementsDiagram P V) ≅
      homZeroFinite P V hP hPdeg :=
    (homZeroRepresentableByLimit P V hP).isoReprX
  let e := productElementsStructuredArrowEquivalence U n
  let eLim : limit (simplicialSetElementsDiagram P V) ≅
      limit (StructuredArrow.proj (op (SimplexCategory.mk n)) π ⋙ F) :=
    HasLimit.isoOfEquivalence e (Iso.refl _)
  refine ⟨eH.symm.app (op (SimplexCategory.mk n)) ≪≫ ?_ ≪≫ e0⟩
  change limit (StructuredArrow.proj (op (SimplexCategory.mk n)) π ⋙ F) ≅
    limit (simplicialSetElementsDiagram P V)
  exact eLim.symm

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
  intro n
  let X : SimplexCategoryᵒᵖ := op (SimplexCategory.mk n)
  let e := pushoutObjIso a b X
  letI : Finite (V.obj X) := by simpa [X] using (hV n).1
  letI : Finite (W.obj X) := by simpa [X] using (hW n).1
  letI : Fintype (V.obj X) := Fintype.ofFinite _
  letI : Fintype (W.obj X) := Fintype.ofFinite _
  letI : Nonempty (V.obj X) := by simpa [X] using (hV n).2
  letI : Nonempty (W.obj X) := by simpa [X] using (hW n).2
  have hfin : Finite (pushout (a.app X) (b.app X)) := by
    let f : V.obj X ⊕ W.obj X → pushout (a.app X) (b.app X) :=
      Sum.elim (pushout.inl (a.app X) (b.app X))
        (pushout.inr (a.app X) (b.app X))
    apply Finite.of_surjective f
    intro x
    obtain ⟨j, y, hy⟩ :=
      Types.jointly_surjective_of_isColimit
        (pushout.isColimit (a.app X) (b.app X)) x
    obtain (_ | _ | _) := j
    · refine ⟨Sum.inl ((a.app X) y), ?_⟩
      change (pushout.inl (a.app X) (b.app X)) ((a.app X) y) = x
      have hz := congrArg (fun k => k y)
        (PushoutCocone.condition_zero (pushout.cocone (a.app X) (b.app X)))
      exact hz.symm.trans hy
    · exact ⟨Sum.inl y, hy⟩
    · exact ⟨Sum.inr y, hy⟩
  letI : Finite (pushout (a.app X) (b.app X)) := hfin
  have hne : Nonempty (pushout (a.app X) (b.app X)) :=
    Nonempty.map (pushout.inl (a.app X) (b.app X)) inferInstance
  constructor
  · exact Finite.of_injective (f := e.hom) (by
      intro x y h
      have h' := congrArg (fun z => e.inv z) h
      simpa using h')
  · exact Nonempty.map e.inv hne

theorem eventuallyDegenerate_pushout
    {U V W : SSet.{w}} (a : U ⟶ V) (b : U ⟶ W)
    (hUdeg : EventuallyDegenerate U)
    (hVdeg : EventuallyDegenerate V)
    (hWdeg : EventuallyDegenerate W) :
    EventuallyDegenerate (pushout a b) := by
  rcases hUdeg with ⟨dU, hdU⟩
  rcases hVdeg with ⟨dV, hdV⟩
  rcases hWdeg with ⟨dW, hdW⟩
  let d := max dU (max dV dW)
  letI : U.HasDimensionLT dU := hdU
  letI : V.HasDimensionLT dV := hdV
  letI : W.HasDimensionLT dW := hdW
  have hU' : U.HasDimensionLT d :=
    SSet.hasDimensionLT_of_le U dU d (Nat.le_max_left _ _)
  have hV' : V.HasDimensionLT d :=
    SSet.hasDimensionLT_of_le V dV d
      (le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _))
  have hW' : W.HasDimensionLT d :=
    SSet.hasDimensionLT_of_le W dW d
      (le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _))
  exact ⟨d, SSet.hasDimensionLT_of_isColimit (pushout.isColimit a b) (by
    rintro (_ | _ | _)
    · exact hU'
    · exact hV'
    · exact hW')⟩

private theorem homPrecomp_homHomEquiv
    {C : Type u} [Category.{v} C] [HasBinaryCoproducts C]
    [HasFiniteLimits C]
    {U V : SSet.{w}} (a : U ⟶ V)
    (T : SimplicialObject C)
    (hU : Unit13.FiniteNonemptySimplicialSet U)
    (hV : Unit13.FiniteNonemptySimplicialSet V)
    (hUdeg : EventuallyDegenerate U)
    (hVdeg : EventuallyDegenerate V)
    (Z : SimplicialObject C)
    (f : Z ⟶ hom V T hV hVdeg) :
    homHomEquiv U T hU hUdeg Z
        (f ≫ homPrecomp a T hU hV hUdeg hVdeg) =
      Unit13.productWithSimplicialSetMap
          (ObjectProperty.homMk a :
            (⟨U, hU⟩ : Unit13.FSSets.{w}) ⟶
              (⟨V, hV⟩ : Unit13.FSSets.{w})) (𝟙 Z) ≫
        homHomEquiv V T hV hVdeg Z f := by
  let U₀ : Unit13.FSSets.{w} := ⟨U, hU⟩
  let V₀ : Unit13.FSSets.{w} := ⟨V, hV⟩
  let a₀ : U₀ ⟶ V₀ := ObjectProperty.homMk a
  change homHomEquiv U T hU hUdeg Z
      (f ≫ homPrecomp a T hU hV hUdeg hVdeg) =
    Unit13.productWithSimplicialSetMap a₀ (𝟙 Z) ≫
      homHomEquiv V T hV hVdeg Z f
  rw [homHomEquiv_comp]
  dsimp [homPrecomp, productWithSimplicialSetMapSecond]
  rw [Equiv.apply_symm_apply]
  have hprod :
      Unit13.productWithSimplicialSetMap
          (ObjectProperty.homMk (𝟙 U) : U₀ ⟶ U₀) f ≫
        Unit13.productWithSimplicialSetMap
          (ObjectProperty.homMk a : U₀ ⟶ V₀) (𝟙 _) =
      Unit13.productWithSimplicialSetMap (ObjectProperty.homMk a : U₀ ⟶ V₀) f := by
    ext X
    let hUZ : Unit13.HasDegreewiseCoproducts U Z :=
      Unit13.degreewiseCoproductInstance U Z hU
    let hUH : Unit13.HasDegreewiseCoproducts U (hom V T hV hVdeg) :=
      Unit13.degreewiseCoproductInstance U (hom V T hV hVdeg) hU
    let hVH : Unit13.HasDegreewiseCoproducts V (hom V T hV hVdeg) :=
      Unit13.degreewiseCoproductInstance V (hom V T hV hVdeg) hV
    let _ : HasCoproduct (fun _ : U.obj X => Z.obj X) :=
      Unit13.degreewiseCoproductInstanceAt hUZ X
    let _ : HasCoproduct (fun _ : U.obj X => (hom V T hV hVdeg).obj X) :=
      Unit13.degreewiseCoproductInstanceAt hUH X
    let _ : HasCoproduct (fun _ : V.obj X => (hom V T hV hVdeg).obj X) :=
      Unit13.degreewiseCoproductInstanceAt hVH X
    simp [Unit13.productWithSimplicialSetMap, ObjectProperty.homMk]
    apply Sigma.hom_ext
    intro u
    change
      Sigma.ι (fun _ : U.obj X => Z.obj X) u ≫
        (Sigma.desc (fun u => f.app X ≫ Sigma.ι
          (fun _ : U.obj X => (hom V T hV hVdeg).obj X)
          ((ConcreteCategory.hom (𝟙 (U.obj X))) u)) ≫
          Sigma.desc (fun u => 𝟙 _ ≫ Sigma.ι
            (fun _ : V.obj X => (hom V T hV hVdeg).obj X)
            ((ConcreteCategory.hom (a.app X)) u))) =
      Sigma.ι (fun _ : U.obj X => Z.obj X) u ≫
        Sigma.desc (fun u => f.app X ≫ Sigma.ι
          (fun _ : V.obj X => (hom V T hV hVdeg).obj X)
          ((ConcreteCategory.hom (a.app X)) u))
    rw [← Category.assoc, Sigma.ι_desc]
    simp [Category.assoc, Sigma.ι_desc]
  have hprod' :
      Unit13.productWithSimplicialSetMap (ObjectProperty.homMk a : U₀ ⟶ V₀) (𝟙 Z) ≫
          Unit13.productWithSimplicialSetMap
            (ObjectProperty.homMk (𝟙 V) : V₀ ⟶ V₀) f =
        Unit13.productWithSimplicialSetMap (ObjectProperty.homMk a : U₀ ⟶ V₀) f := by
    ext X
    let hUZ : Unit13.HasDegreewiseCoproducts U Z :=
      Unit13.degreewiseCoproductInstance U Z hU
    let hVZ : Unit13.HasDegreewiseCoproducts V Z :=
      Unit13.degreewiseCoproductInstance V Z hV
    let hVH : Unit13.HasDegreewiseCoproducts V (hom V T hV hVdeg) :=
      Unit13.degreewiseCoproductInstance V (hom V T hV hVdeg) hV
    let _ : HasCoproduct (fun _ : U.obj X => Z.obj X) :=
      Unit13.degreewiseCoproductInstanceAt hUZ X
    let _ : HasCoproduct (fun _ : V.obj X => Z.obj X) :=
      Unit13.degreewiseCoproductInstanceAt hVZ X
    let _ : HasCoproduct (fun _ : V.obj X => (hom V T hV hVdeg).obj X) :=
      Unit13.degreewiseCoproductInstanceAt hVH X
    simp [Unit13.productWithSimplicialSetMap, ObjectProperty.homMk]
    apply Sigma.hom_ext
    intro u
    change
      Sigma.ι (fun _ : U.obj X => Z.obj X) u ≫
        (Sigma.desc (fun u => 𝟙 _ ≫ Sigma.ι
          (fun _ : V.obj X => Z.obj X) ((ConcreteCategory.hom (a.app X)) u)) ≫
          Sigma.desc (fun u => f.app X ≫ Sigma.ι
            (fun _ : V.obj X => (hom V T hV hVdeg).obj X)
            ((ConcreteCategory.hom (𝟙 (V.obj X))) u))) =
      Sigma.ι (fun _ : U.obj X => Z.obj X) u ≫
        Sigma.desc (fun u => f.app X ≫ Sigma.ι
          (fun _ : V.obj X => (hom V T hV hVdeg).obj X)
          ((ConcreteCategory.hom (a.app X)) u))
    rw [← Category.assoc, Sigma.ι_desc]
    simp [Category.assoc, Sigma.ι_desc]
  have hhom0 :
      homHomEquiv V T hV hVdeg Z f =
        productWithSimplicialSetMapSecond V hV f ≫
          homHomEquiv V T hV hVdeg (hom V T hV hVdeg) (𝟙 _) := by
    rw [← homHomEquiv_comp]
    simp
  have hhom :
      homHomEquiv V T hV hVdeg Z f =
        Unit13.productWithSimplicialSetMap
            (ObjectProperty.homMk (𝟙 V) : V₀ ⟶ V₀) f ≫
          homHomEquiv V T hV hVdeg (hom V T hV hVdeg) (𝟙 _) := by
    simpa [productWithSimplicialSetMapSecond] using hhom0
  have hprod'_a₀ :
      Unit13.productWithSimplicialSetMap a₀ (𝟙 Z) ≫
          Unit13.productWithSimplicialSetMap
            (ObjectProperty.homMk (𝟙 V) : V₀ ⟶ V₀) f =
        Unit13.productWithSimplicialSetMap a₀ f := by
    simpa [a₀] using hprod'
  rw [← Category.assoc, hprod, hhom]
  rw [← Category.assoc, hprod'_a₀]

private theorem productWithSimplicialSetMap_comp
    {C : Type u} [Category.{v} C] [HasBinaryCoproducts C]
    {A B D : Unit13.FSSets.{w}}
    {Z Z' Z'' : SimplicialObject C}
    (f : A ⟶ B) (g : B ⟶ D)
    (r : Z ⟶ Z') (s : Z' ⟶ Z'') :
    Unit13.productWithSimplicialSetMap f r ≫
        Unit13.productWithSimplicialSetMap g s =
      Unit13.productWithSimplicialSetMap (f ≫ g) (r ≫ s) := by
  ext X
  let hA : Unit13.HasDegreewiseCoproducts A.obj Z :=
    Unit13.degreewiseCoproductInstance A.obj Z A.property
  let hB : Unit13.HasDegreewiseCoproducts B.obj Z' :=
    Unit13.degreewiseCoproductInstance B.obj Z' B.property
  let hD : Unit13.HasDegreewiseCoproducts D.obj Z'' :=
    Unit13.degreewiseCoproductInstance D.obj Z'' D.property
  let _ : HasCoproduct (fun _ : A.obj.obj X => Z.obj X) :=
    Unit13.degreewiseCoproductInstanceAt hA X
  let _ : HasCoproduct (fun _ : B.obj.obj X => Z'.obj X) :=
    Unit13.degreewiseCoproductInstanceAt hB X
  let _ : HasCoproduct (fun _ : D.obj.obj X => Z''.obj X) :=
    Unit13.degreewiseCoproductInstanceAt hD X
  simp [Unit13.productWithSimplicialSetMap]
  apply Sigma.hom_ext
  intro u
  have hdesc :
      Sigma.desc (fun u => r.app X ≫ Sigma.ι
          (fun _ : B.1.obj X => Z'.obj X)
          ((ConcreteCategory.hom (f.hom.app X)) u)) ≫
        Sigma.desc (fun u => s.app X ≫ Sigma.ι
          (fun _ : D.1.obj X => Z''.obj X)
          ((ConcreteCategory.hom (g.hom.app X)) u)) =
      Sigma.desc (fun u => (r.app X ≫ s.app X) ≫ Sigma.ι
          (fun _ : D.1.obj X => Z''.obj X)
          ((ConcreteCategory.hom (g.hom.app X))
            ((ConcreteCategory.hom (f.hom.app X)) u))) := by
    apply Sigma.hom_ext
    intro u
    simp [Category.assoc]
  convert congrArg
      (fun k => Sigma.ι (fun _ : A.obj.obj X => Z.obj X) u ≫ k) hdesc using 1 <;>
    rfl

private theorem productWithSimplicialSetMap_pushout_condition
    {C : Type u} [Category.{v} C] [HasBinaryCoproducts C]
    {U V W : SSet.{w}} (a : U ⟶ V) (b : U ⟶ W)
    (Z : SimplicialObject C)
    (hU : Unit13.FiniteNonemptySimplicialSet U)
    (hV : Unit13.FiniteNonemptySimplicialSet V)
    (hW : Unit13.FiniteNonemptySimplicialSet W)
    (hP : Unit13.FiniteNonemptySimplicialSet (pushout a b)) :
    let U₀ : Unit13.FSSets.{w} := ⟨U, hU⟩
    let V₀ : Unit13.FSSets.{w} := ⟨V, hV⟩
    let W₀ : Unit13.FSSets.{w} := ⟨W, hW⟩
    let P₀ : Unit13.FSSets.{w} := ⟨pushout a b, hP⟩
    let a₀ : U₀ ⟶ V₀ := ObjectProperty.homMk a
    let b₀ : U₀ ⟶ W₀ := ObjectProperty.homMk b
    let inl₀ : V₀ ⟶ P₀ := ObjectProperty.homMk (pushout.inl a b)
    let inr₀ : W₀ ⟶ P₀ := ObjectProperty.homMk (pushout.inr a b)
    Unit13.productWithSimplicialSetMap a₀ (𝟙 Z) ≫
          Unit13.productWithSimplicialSetMap inl₀ (𝟙 Z) =
      Unit13.productWithSimplicialSetMap b₀ (𝟙 Z) ≫
          Unit13.productWithSimplicialSetMap inr₀ (𝟙 Z) := by
  dsimp
  have hleft := productWithSimplicialSetMap_comp
    (A := (⟨U, hU⟩ : Unit13.FSSets.{w}))
    (B := (⟨V, hV⟩ : Unit13.FSSets.{w}))
    (D := (⟨pushout a b, hP⟩ : Unit13.FSSets.{w}))
    (ObjectProperty.homMk a) (ObjectProperty.homMk (pushout.inl a b))
    (𝟙 Z) (𝟙 Z)
  have hright := productWithSimplicialSetMap_comp
    (A := (⟨U, hU⟩ : Unit13.FSSets.{w}))
    (B := (⟨W, hW⟩ : Unit13.FSSets.{w}))
    (D := (⟨pushout a b, hP⟩ : Unit13.FSSets.{w}))
    (ObjectProperty.homMk b) (ObjectProperty.homMk (pushout.inr a b))
    (𝟙 Z) (𝟙 Z)
  rw [hleft, hright]
  congr 1
  have h := congrArg
    (fun k : U ⟶ pushout a b =>
      (ObjectProperty.homMk k :
        (⟨U, hU⟩ : Unit13.FSSets.{w}) ⟶
          (⟨pushout a b, hP⟩ : Unit13.FSSets.{w})))
    (pushout.condition (f := a) (g := b))
  exact h

private noncomputable def pushoutFunctionDescData
    {S X Y : Type w}
    (f : S ⟶ X) (g : S ⟶ Y) (c : (span f g).CoconeTypes) :
    {q : pushout f g → c.pt // ∀ k : WalkingSpan,
      q ∘ ((Functor.coconeTypesEquiv (span f g)).symm (pushout.cocone f g)).ι k =
        c.ι k} := by
  let F := span f g
  let c₀ : F.CoconeTypes :=
    (Functor.coconeTypesEquiv F).symm (pushout.cocone f g)
  have hc₀ : c₀.IsColimit := by
    apply (Functor.CoconeTypes.isColimit_iff c₀).2
    exact ⟨pushout.isColimit f g⟩
  exact ⟨Classical.choose (hc₀.exists_desc c),
    Classical.choose_spec (hc₀.exists_desc c)⟩

private noncomputable def pushoutFunctionDesc
    {S X Y : Type w}
    (f : S ⟶ X) (g : S ⟶ Y) (c : (span f g).CoconeTypes) :
    pushout f g → c.pt :=
  (pushoutFunctionDescData f g c).1

private theorem pushoutFunctionDesc_inl
    {S X Y : Type w}
    (f : S ⟶ X) (g : S ⟶ Y) (c : (span f g).CoconeTypes) (x : X) :
    pushoutFunctionDesc f g c (pushout.inl f g x) = c.ι WalkingSpan.left x := by
  exact congr_fun ((pushoutFunctionDescData f g c).2 WalkingSpan.left) x

private theorem pushoutFunctionDesc_inr
    {S X Y : Type w}
    (f : S ⟶ X) (g : S ⟶ Y) (c : (span f g).CoconeTypes) (y : Y) :
    pushoutFunctionDesc f g c (pushout.inr f g y) = c.ι WalkingSpan.right y := by
  exact congr_fun ((pushoutFunctionDescData f g c).2 WalkingSpan.right) y

private noncomputable def compatibleFamily_pushout
    {C : Type u} [Category.{v} C] [HasBinaryCoproducts C]
    {U V W : SSet.{w}} (a : U ⟶ V) (b : U ⟶ W)
    {Z Q : SimplicialObject C}
    (f : Unit13.CompatibleFamily V Z Q)
    (g : Unit13.CompatibleFamily W Z Q)
    (h : ∀ n : ℕ, ∀ u : U _⦋n⦌,
      f.1 n ((a.app (op (SimplexCategory.mk n))) u) =
        g.1 n ((b.app (op (SimplexCategory.mk n))) u)) :
    Unit13.CompatibleFamily (pushout a b) Z Q := by
  refine ⟨fun n p => ?_, ?_⟩
  · let X : SimplexCategoryᵒᵖ := op (SimplexCategory.mk n)
    let e := pushoutObjIso a b X
    let cX : (span (a.app X) (b.app X)).CoconeTypes :=
      { pt := Z.obj X ⟶ Q.obj X
        ι := fun k => match k with
          | none => fun u => f.1 n ((a.app X) u)
          | some WalkingPair.left => f.1 n
          | some WalkingPair.right => g.1 n
        ι_naturality := by
          intro j j' φ
          rcases j with _ | (_ | _)
          · rcases j' with _ | (_ | _)
            · have hφ : φ = 𝟙 _ := Subsingleton.elim _ _
              subst φ
              rfl
            · have hφ : φ = WalkingSpan.Hom.fst := Subsingleton.elim _ _
              subst φ
              rfl
            · have hφ : φ = WalkingSpan.Hom.snd := Subsingleton.elim _ _
              subst φ
              funext u
              exact (h n u).symm
          · rcases j' with _ | (_ | _)
            · exact nomatch φ
            · have hφ : φ = 𝟙 _ := Subsingleton.elim _ _
              subst φ
              rfl
            · exact nomatch φ
          · rcases j' with _ | (_ | _)
            · exact nomatch φ
            · exact nomatch φ
            · have hφ : φ = 𝟙 _ := Subsingleton.elim _ _
              subst φ
              rfl }
    exact pushoutFunctionDesc (a.app X) (b.app X) cX (e.hom p)
  · intro m n φ p
    let X : SimplexCategoryᵒᵖ := op (SimplexCategory.mk n)
    let Y : SimplexCategoryᵒᵖ := op (SimplexCategory.mk m)
    let eX := pushoutObjIso a b X
    let eY := pushoutObjIso a b Y
    letI : HasPushout (a.app X) (b.app X) := inferInstance
    letI : HasPushout (a.app Y) (b.app Y) := inferInstance
    have hq : a.app X ≫ V.map φ.op = U.map φ.op ≫ a.app Y :=
      (a.naturality φ.op).symm
    have hq' : b.app X ≫ W.map φ.op = U.map φ.op ≫ b.app Y :=
      (b.naturality φ.op).symm
    let q : pushout (a.app X) (b.app X) ⟶ pushout (a.app Y) (b.app Y) :=
      pushout.map (a.app X) (b.app X) (a.app Y) (b.app Y)
        (V.map φ.op) (W.map φ.op) (U.map φ.op) hq hq'
    let cX : (span (a.app X) (b.app X)).CoconeTypes :=
      { pt := Z.obj X ⟶ Q.obj X
        ι := fun k => match k with
          | none => fun u => f.1 n ((a.app X) u)
          | some WalkingPair.left => f.1 n
          | some WalkingPair.right => g.1 n
        ι_naturality := by
          intro j j' ψ
          rcases j with _ | (_ | _)
          · rcases j' with _ | (_ | _)
            · have hψ : ψ = 𝟙 _ := Subsingleton.elim _ _
              subst ψ
              rfl
            · have hψ : ψ = WalkingSpan.Hom.fst := Subsingleton.elim _ _
              subst ψ
              rfl
            · have hψ : ψ = WalkingSpan.Hom.snd := Subsingleton.elim _ _
              subst ψ
              funext u
              exact (h n u).symm
          · rcases j' with _ | (_ | _)
            · exact nomatch ψ
            · have hψ : ψ = 𝟙 _ := Subsingleton.elim _ _
              subst ψ
              rfl
            · exact nomatch ψ
          · rcases j' with _ | (_ | _)
            · exact nomatch ψ
            · exact nomatch ψ
            · have hψ : ψ = 𝟙 _ := Subsingleton.elim _ _
              subst ψ
              rfl }
    let cY : (span (a.app Y) (b.app Y)).CoconeTypes :=
      { pt := Z.obj Y ⟶ Q.obj Y
        ι := fun k => match k with
          | none => fun u => f.1 m ((a.app Y) u)
          | some WalkingPair.left => f.1 m
          | some WalkingPair.right => g.1 m
        ι_naturality := by
          intro j j' ψ
          rcases j with _ | (_ | _)
          · rcases j' with _ | (_ | _)
            · have hψ : ψ = 𝟙 _ := Subsingleton.elim _ _
              subst ψ
              rfl
            · have hψ : ψ = WalkingSpan.Hom.fst := Subsingleton.elim _ _
              subst ψ
              rfl
            · have hψ : ψ = WalkingSpan.Hom.snd := Subsingleton.elim _ _
              subst ψ
              funext u
              exact (h m u).symm
          · rcases j' with _ | (_ | _)
            · exact nomatch ψ
            · have hψ : ψ = 𝟙 _ := Subsingleton.elim _ _
              subst ψ
              rfl
            · exact nomatch ψ
          · rcases j' with _ | (_ | _)
            · exact nomatch ψ
            · exact nomatch ψ
            · have hψ : ψ = 𝟙 _ := Subsingleton.elim _ _
              subst ψ
              rfl }
    let kX := pushoutFunctionDesc (a.app X) (b.app X) cX
    let kY := pushoutFunctionDesc (a.app Y) (b.app Y) cY
    have hkX_inl (v : V.obj X) :
        kX (pushout.inl (a.app X) (b.app X) v) = f.1 n v := by
      simpa [kX, cX] using pushoutFunctionDesc_inl (a.app X) (b.app X) cX v
    have hkX_inr (v : W.obj X) :
        kX (pushout.inr (a.app X) (b.app X) v) = g.1 n v := by
      simpa [kX, cX] using pushoutFunctionDesc_inr (a.app X) (b.app X) cX v
    have hkY_inl (v : V.obj Y) :
        kY (pushout.inl (a.app Y) (b.app Y) v) = f.1 m v := by
      simpa [kY, cY] using pushoutFunctionDesc_inl (a.app Y) (b.app Y) cY v
    have hkY_inr (v : W.obj Y) :
        kY (pushout.inr (a.app Y) (b.app Y) v) = g.1 m v := by
      simpa [kY, cY] using pushoutFunctionDesc_inr (a.app Y) (b.app Y) cY v
    have hq_inl (v : V.obj X) :
        q (pushout.inl (a.app X) (b.app X) v) =
          pushout.inl (a.app Y) (b.app Y) (V.map φ.op v) := by
      have hq_inl' :
          pushout.inl (a.app X) (b.app X) ≫ q =
            V.map φ.op ≫ pushout.inl (a.app Y) (b.app Y) := by
        have hdesc :
            a.app X ≫ (V.map φ.op ≫ pushout.inl (a.app Y) (b.app Y)) =
              b.app X ≫ (W.map φ.op ≫ pushout.inr (a.app Y) (b.app Y)) := by
          calc
            a.app X ≫ (V.map φ.op ≫ pushout.inl (a.app Y) (b.app Y)) =
                (a.app X ≫ V.map φ.op) ≫ pushout.inl (a.app Y) (b.app Y) := by simp only [Category.assoc]
            _ = (U.map φ.op ≫ a.app Y) ≫ pushout.inl (a.app Y) (b.app Y) := by rw [hq]
            _ = U.map φ.op ≫ (a.app Y ≫ pushout.inl (a.app Y) (b.app Y)) := by simp only [Category.assoc]
            _ = U.map φ.op ≫ (b.app Y ≫ pushout.inr (a.app Y) (b.app Y)) := by rw [pushout.condition]
            _ = (U.map φ.op ≫ b.app Y) ≫ pushout.inr (a.app Y) (b.app Y) := by simp only [Category.assoc]
            _ = (b.app X ≫ W.map φ.op) ≫ pushout.inr (a.app Y) (b.app Y) := by rw [hq']
            _ = b.app X ≫ (W.map φ.op ≫ pushout.inr (a.app Y) (b.app Y)) := by simp only [Category.assoc]
        change pushout.inl (a.app X) (b.app X) ≫
            pushout.desc (V.map φ.op ≫ pushout.inl (a.app Y) (b.app Y))
              (W.map φ.op ≫ pushout.inr (a.app Y) (b.app Y)) _ = _
        exact pushout.inl_desc _ _ hdesc
      simpa only [CategoryTheory.comp_apply] using congrArg (fun k => k v) hq_inl'
    have hq_inr (v : W.obj X) :
        q (pushout.inr (a.app X) (b.app X) v) =
          pushout.inr (a.app Y) (b.app Y) (W.map φ.op v) := by
      have hq_inr' :
          pushout.inr (a.app X) (b.app X) ≫ q =
            W.map φ.op ≫ pushout.inr (a.app Y) (b.app Y) := by
        have hdesc :
            a.app X ≫ (V.map φ.op ≫ pushout.inl (a.app Y) (b.app Y)) =
              b.app X ≫ (W.map φ.op ≫ pushout.inr (a.app Y) (b.app Y)) := by
          calc
            a.app X ≫ (V.map φ.op ≫ pushout.inl (a.app Y) (b.app Y)) =
                (a.app X ≫ V.map φ.op) ≫ pushout.inl (a.app Y) (b.app Y) := by simp only [Category.assoc]
            _ = (U.map φ.op ≫ a.app Y) ≫ pushout.inl (a.app Y) (b.app Y) := by rw [hq]
            _ = U.map φ.op ≫ (a.app Y ≫ pushout.inl (a.app Y) (b.app Y)) := by simp only [Category.assoc]
            _ = U.map φ.op ≫ (b.app Y ≫ pushout.inr (a.app Y) (b.app Y)) := by rw [pushout.condition]
            _ = (U.map φ.op ≫ b.app Y) ≫ pushout.inr (a.app Y) (b.app Y) := by simp only [Category.assoc]
            _ = (b.app X ≫ W.map φ.op) ≫ pushout.inr (a.app Y) (b.app Y) := by rw [hq']
            _ = b.app X ≫ (W.map φ.op ≫ pushout.inr (a.app Y) (b.app Y)) := by simp only [Category.assoc]
        change pushout.inr (a.app X) (b.app X) ≫
            pushout.desc (V.map φ.op ≫ pushout.inl (a.app Y) (b.app Y))
              (W.map φ.op ≫ pushout.inr (a.app Y) (b.app Y)) _ = _
        exact pushout.inr_desc _ _ hdesc
      simpa only [CategoryTheory.comp_apply] using congrArg (fun k => k v) hq_inr'
    have hfamily : ∀ z : pushout (a.app X) (b.app X),
        Z.map φ.op ≫ kY (q z) = kX z ≫ Q.map φ.op := by
      intro z
      obtain ⟨j, y, hy⟩ :=
        Types.jointly_surjective_of_isColimit (pushout.isColimit (a.app X) (b.app X)) z
      obtain (_ | _ | _) := j
      · rw [← hy]
        rw [PushoutCocone.condition_zero]
        change U.obj X at y
        change Z.map φ.op ≫ kY (q (pushout.inl (a.app X) (b.app X) ((a.app X) y))) =
          kX (pushout.inl (a.app X) (b.app X) ((a.app X) y)) ≫ Q.map φ.op
        rw [hkX_inl, hq_inl, hkY_inl]
        exact f.property φ ((a.app X) y)
      · rw [← hy]
        change V.obj X at y
        change Z.map φ.op ≫ kY (q (pushout.inl (a.app X) (b.app X) y)) =
          kX (pushout.inl (a.app X) (b.app X) y) ≫ Q.map φ.op
        rw [hkX_inl, hq_inl, hkY_inl]
        exact f.property φ y
      · rw [← hy]
        change W.obj X at y
        change Z.map φ.op ≫ kY (q (pushout.inr (a.app X) (b.app X) y)) =
          kX (pushout.inr (a.app X) (b.app X) y) ≫ Q.map φ.op
        rw [hkX_inr, hq_inr, hkY_inr]
        exact g.property φ y
    have hqcat_inl :
        pushout.inl (a.app X) (b.app X) ≫ q =
          V.map φ.op ≫ pushout.inl (a.app Y) (b.app Y) := by
      apply ConcreteCategory.hom_ext
      intro v
      exact hq_inl v
    have hqcat_inr :
        pushout.inr (a.app X) (b.app X) ≫ q =
          W.map φ.op ≫ pushout.inr (a.app Y) (b.app Y) := by
      apply ConcreteCategory.hom_ext
      intro v
      exact hq_inr v
    have hecat :
        eX.inv ≫ (pushout a b).map φ.op ≫ eY.hom = q := by
      apply pushout.hom_ext
      · dsimp [X, Y]
        rw [← Category.assoc, inl_comp_pushoutObjIso_inv]
        rw [← (pushout.inl a b).naturality_assoc φ.op]
        rw [inl_comp_pushoutObjIso_hom]
        exact hqcat_inl.symm
      · dsimp [X, Y]
        rw [← Category.assoc, inr_comp_pushoutObjIso_inv]
        rw [← (pushout.inr a b).naturality_assoc φ.op]
        rw [inr_comp_pushoutObjIso_hom]
        exact hqcat_inr.symm
    have he := ConcreteCategory.congr_hom hecat (eX.hom p)
    change eY.hom ((pushout a b).map φ.op (eX.inv (eX.hom p))) = q (eX.hom p) at he
    rw [eX.hom_inv_id_apply] at he
    change Z.map φ.op ≫ kY (eY.hom ((pushout a b).map φ.op p)) =
      kX (eX.hom p) ≫ Q.map φ.op
    rw [he]
    exact hfamily (eX.hom p)

private theorem finiteProductMap_family_apply
    {C : Type u} [Category.{v} C] [HasBinaryCoproducts C]
    {U V : SSet.{w}} (a : U ⟶ V)
    (Z T : SimplicialObject C)
    (hU : Unit13.FiniteNonemptySimplicialSet U)
    (hV : Unit13.FiniteNonemptySimplicialSet V)
    {n : ℕ} (u : U _⦋n⦌)
    (γ : Unit13.simplicialSetProduct V Z hV ⟶ T) :
    ((Unit13.finiteSimplicialSetProduct_hom_equiv U Z hU T).1
      (Unit13.productWithSimplicialSetMap
        (ObjectProperty.homMk a :
          (⟨U, hU⟩ : Unit13.FSSets.{w}) ⟶
            (⟨V, hV⟩ : Unit13.FSSets.{w})) (𝟙 Z) ≫ γ)).1 n u =
      ((Unit13.finiteSimplicialSetProduct_hom_equiv V Z hV T).1 γ).1 n
        ((a.app (op (SimplexCategory.mk n))) u) := by
  dsimp [Unit13.finiteSimplicialSetProduct_hom_equiv,
    Unit13.simplicialSetProduct_hom_equiv]
  simp [Unit13.productWithSimplicialSetMap,
    Unit13.simplicialSetProduct, Unit13.simplicialSetProductOf]

private theorem finiteProductMap_second_family_apply
    {C : Type u} [Category.{v} C] [HasBinaryCoproducts C]
    {U : SSet.{w}} (Z Z' T : SimplicialObject C)
    (hU : Unit13.FiniteNonemptySimplicialSet U)
    (r : Z ⟶ Z') (n : ℕ) (u : U _⦋n⦌)
    (γ : Unit13.simplicialSetProduct U Z' hU ⟶ T) :
    ((Unit13.finiteSimplicialSetProduct_hom_equiv U Z hU T).1
      (Unit13.productWithSimplicialSetMap
        (ObjectProperty.homMk (𝟙 U) :
          (⟨U, hU⟩ : Unit13.FSSets.{w}) ⟶ (⟨U, hU⟩ : Unit13.FSSets.{w})) r ≫ γ)).1 n u =
      r.app (op (SimplexCategory.mk n)) ≫
        ((Unit13.finiteSimplicialSetProduct_hom_equiv U Z' hU T).1 γ).1 n u := by
  dsimp [Unit13.finiteSimplicialSetProduct_hom_equiv,
    Unit13.simplicialSetProduct_hom_equiv]
  simp [Unit13.productWithSimplicialSetMap,
    Unit13.simplicialSetProduct, Unit13.simplicialSetProductOf, Category.assoc]

private theorem compatibleFamily_pushout_inl
    {C : Type u} [Category.{v} C] [HasBinaryCoproducts C]
    {U V W : SSet.{w}} (a : U ⟶ V) (b : U ⟶ W)
    {Z Q : SimplicialObject C}
    (f : Unit13.CompatibleFamily V Z Q)
    (g : Unit13.CompatibleFamily W Z Q)
    (h : ∀ n : ℕ, ∀ u : U _⦋n⦌,
      f.1 n ((a.app (op (SimplexCategory.mk n))) u) =
        g.1 n ((b.app (op (SimplexCategory.mk n))) u))
    {n : ℕ} (v : V _⦋n⦌) :
    (compatibleFamily_pushout a b f g h).1 n
        ((pushout.inl a b).app (op (SimplexCategory.mk n)) v) = f.1 n v := by
  dsimp [compatibleFamily_pushout]
  have hi :
      (pushoutObjIso a b (op (SimplexCategory.mk n))).hom
          ((pushout.inl a b).app (op (SimplexCategory.mk n)) v) =
        pushout.inl (a.app (op (SimplexCategory.mk n)))
          (b.app (op (SimplexCategory.mk n))) v := by
    simpa only [CategoryTheory.comp_apply] using
      congrArg (fun k => k v)
        (inl_comp_pushoutObjIso_hom a b (op (SimplexCategory.mk n)))
  rw [hi, pushoutFunctionDesc_inl]

private theorem compatibleFamily_pushout_inr
    {C : Type u} [Category.{v} C] [HasBinaryCoproducts C]
    {U V W : SSet.{w}} (a : U ⟶ V) (b : U ⟶ W)
    {Z Q : SimplicialObject C}
    (f : Unit13.CompatibleFamily V Z Q)
    (g : Unit13.CompatibleFamily W Z Q)
    (h : ∀ n : ℕ, ∀ u : U _⦋n⦌,
      f.1 n ((a.app (op (SimplexCategory.mk n))) u) =
        g.1 n ((b.app (op (SimplexCategory.mk n))) u))
    {n : ℕ} (v : W _⦋n⦌) :
    (compatibleFamily_pushout a b f g h).1 n
        ((pushout.inr a b).app (op (SimplexCategory.mk n)) v) = g.1 n v := by
  dsimp [compatibleFamily_pushout]
  have hi :
      (pushoutObjIso a b (op (SimplexCategory.mk n))).hom
          ((pushout.inr a b).app (op (SimplexCategory.mk n)) v) =
        pushout.inr (a.app (op (SimplexCategory.mk n)))
          (b.app (op (SimplexCategory.mk n))) v := by
    simpa only [CategoryTheory.comp_apply] using
      congrArg (fun k => k v)
        (inr_comp_pushoutObjIso_hom a b (op (SimplexCategory.mk n)))
  rw [hi, pushoutFunctionDesc_inr]

private noncomputable def homFibreProduct_to_pushout_data
    {C : Type u} [Category.{v} C] [HasBinaryCoproducts C]
    [HasFiniteLimits C]
    {U V W : SSet.{w}} (a : U ⟶ V) (b : U ⟶ W)
    (T : SimplicialObject C)
    (hU : Unit13.FiniteNonemptySimplicialSet U)
    (hV : Unit13.FiniteNonemptySimplicialSet V)
    (hW : Unit13.FiniteNonemptySimplicialSet W)
    (hUdeg : EventuallyDegenerate U)
    (hVdeg : EventuallyDegenerate V)
    (hWdeg : EventuallyDegenerate W)
    (Z : SimplicialObject C)
    (s : Z ⟶ homFibreProduct a b T hU hV hW hUdeg hVdeg hWdeg) :
    {γ : Unit13.simplicialSetProduct (pushout a b) Z
          (finiteNonempty_pushout a b hU hV hW) ⟶ T //
      Unit13.productWithSimplicialSetMap
            (ObjectProperty.homMk (pushout.inl a b) :
              (⟨V, hV⟩ : Unit13.FSSets.{w}) ⟶
                (⟨pushout a b, finiteNonempty_pushout a b hU hV hW⟩ : Unit13.FSSets.{w}))
            (𝟙 Z) ≫ γ =
          homHomEquiv V T hV hVdeg Z
            (s ≫ homFibreProductFst a b T hU hV hW hUdeg hVdeg hWdeg) ∧
      Unit13.productWithSimplicialSetMap
            (ObjectProperty.homMk (pushout.inr a b) :
              (⟨W, hW⟩ : Unit13.FSSets.{w}) ⟶
                (⟨pushout a b, finiteNonempty_pushout a b hU hV hW⟩ : Unit13.FSSets.{w}))
            (𝟙 Z) ≫ γ =
          homHomEquiv W T hW hWdeg Z
            (s ≫ homFibreProductSnd a b T hU hV hW hUdeg hVdeg hWdeg)} := by
  let fV : Unit13.CompatibleFamily V Z T :=
    (Unit13.finiteSimplicialSetProduct_hom_equiv V Z hV T).1
      (homHomEquiv V T hV hVdeg Z
        (s ≫ homFibreProductFst a b T hU hV hW hUdeg hVdeg hWdeg))
  let gW : Unit13.CompatibleFamily W Z T :=
    (Unit13.finiteSimplicialSetProduct_hom_equiv W Z hW T).1
      (homHomEquiv W T hW hWdeg Z
        (s ≫ homFibreProductSnd a b T hU hV hW hUdeg hVdeg hWdeg))
  have hcompat : ∀ n : ℕ, ∀ u : U _⦋n⦌,
      fV.1 n ((a.app (op (SimplexCategory.mk n))) u) =
        gW.1 n ((b.app (op (SimplexCategory.mk n))) u) := by
    intro n u
    have hcond := (homFibreProduct_isPullback a b T hU hV hW hUdeg hVdeg hWdeg).w
    have hs :
        s ≫ homFibreProductFst a b T hU hV hW hUdeg hVdeg hWdeg ≫
            homPrecomp a T hU hV hUdeg hVdeg =
          s ≫ homFibreProductSnd a b T hU hV hW hUdeg hVdeg hWdeg ≫
            homPrecomp b T hU hW hUdeg hWdeg := by
      calc
        _ = s ≫ (homFibreProductFst a b T hU hV hW hUdeg hVdeg hWdeg ≫
              homPrecomp a T hU hV hUdeg hVdeg) := by rfl
        _ = s ≫ (homFibreProductSnd a b T hU hV hW hUdeg hVdeg hWdeg ≫
              homPrecomp b T hU hW hUdeg hWdeg) := congrArg (fun k => s ≫ k) hcond
        _ = _ := by rfl
    have hfamily := congrArg (fun k => homHomEquiv U T hU hUdeg Z k) hs
    have hmap :
        Unit13.productWithSimplicialSetMap
            (ObjectProperty.homMk a :
              (⟨U, hU⟩ : Unit13.FSSets.{w}) ⟶
                (⟨V, hV⟩ : Unit13.FSSets.{w})) (𝟙 Z) ≫
            homHomEquiv V T hV hVdeg Z
              (s ≫ homFibreProductFst a b T hU hV hW hUdeg hVdeg hWdeg) =
          Unit13.productWithSimplicialSetMap
              (ObjectProperty.homMk b :
                (⟨U, hU⟩ : Unit13.FSSets.{w}) ⟶
                  (⟨W, hW⟩ : Unit13.FSSets.{w})) (𝟙 Z) ≫
            homHomEquiv W T hW hWdeg Z
              (s ≫ homFibreProductSnd a b T hU hV hW hUdeg hVdeg hWdeg) := by
      rw [← homPrecomp_homHomEquiv a T hU hV hUdeg hVdeg Z
        (s ≫ homFibreProductFst a b T hU hV hW hUdeg hVdeg hWdeg)]
      rw [← homPrecomp_homHomEquiv b T hU hW hUdeg hWdeg Z
        (s ≫ homFibreProductSnd a b T hU hV hW hUdeg hVdeg hWdeg)]
      simpa only [Category.assoc] using hfamily
    have hpoint := congrArg
      (fun k => ((Unit13.finiteSimplicialSetProduct_hom_equiv U Z hU T).1 k).1 n u) hmap
    calc
      fV.1 n ((a.app (op (SimplexCategory.mk n))) u) =
          ((Unit13.finiteSimplicialSetProduct_hom_equiv U Z hU T).1
            (Unit13.productWithSimplicialSetMap
              (ObjectProperty.homMk a :
                (⟨U, hU⟩ : Unit13.FSSets.{w}) ⟶ (⟨V, hV⟩ : Unit13.FSSets.{w}))
              (𝟙 Z) ≫ homHomEquiv V T hV hVdeg Z
                (s ≫ homFibreProductFst a b T hU hV hW hUdeg hVdeg hWdeg))).1 n u := by
        symm
        exact finiteProductMap_family_apply a Z T hU hV u
          (homHomEquiv V T hV hVdeg Z
            (s ≫ homFibreProductFst a b T hU hV hW hUdeg hVdeg hWdeg))
      _ = ((Unit13.finiteSimplicialSetProduct_hom_equiv U Z hU T).1
            (Unit13.productWithSimplicialSetMap
              (ObjectProperty.homMk b :
                (⟨U, hU⟩ : Unit13.FSSets.{w}) ⟶ (⟨W, hW⟩ : Unit13.FSSets.{w}))
              (𝟙 Z) ≫ homHomEquiv W T hW hWdeg Z
                (s ≫ homFibreProductSnd a b T hU hV hW hUdeg hVdeg hWdeg))).1 n u := hpoint
      _ = gW.1 n ((b.app (op (SimplexCategory.mk n))) u) := by
        exact finiteProductMap_family_apply b Z T hU hW u
          (homHomEquiv W T hW hWdeg Z
            (s ≫ homFibreProductSnd a b T hU hV hW hUdeg hVdeg hWdeg))
  let K := compatibleFamily_pushout a b fV gW hcompat
  let γ := (Unit13.finiteSimplicialSetProduct_hom_equiv
    (pushout a b) Z (finiteNonempty_pushout a b hU hV hW) T).symm K
  refine ⟨γ, ?_, ?_⟩
  · apply (Unit13.finiteSimplicialSetProduct_hom_equiv V Z hV T).injective
    apply Subtype.ext
    funext n v
    have hmap := finiteProductMap_family_apply (pushout.inl a b) Z T hV
      (finiteNonempty_pushout a b hU hV hW) v γ
    have hK : (Unit13.finiteSimplicialSetProduct_hom_equiv
          (pushout a b) Z (finiteNonempty_pushout a b hU hV hW) T).1 γ = K := by
      dsimp [γ]
      exact Equiv.apply_symm_apply _ _
    calc
      _ = ((Unit13.finiteSimplicialSetProduct_hom_equiv
            (pushout a b) Z (finiteNonempty_pushout a b hU hV hW) T).1 γ).1 n
            ((pushout.inl a b).app (op (SimplexCategory.mk n)) v) := hmap
      _ = K.1 n ((pushout.inl a b).app (op (SimplexCategory.mk n)) v) := by rw [hK]
      _ = fV.1 n v := compatibleFamily_pushout_inl a b fV gW hcompat v
      _ = _ := by rfl
  · apply (Unit13.finiteSimplicialSetProduct_hom_equiv W Z hW T).injective
    apply Subtype.ext
    funext n v
    have hmap := finiteProductMap_family_apply (pushout.inr a b) Z T hW
      (finiteNonempty_pushout a b hU hV hW) v γ
    have hK : (Unit13.finiteSimplicialSetProduct_hom_equiv
          (pushout a b) Z (finiteNonempty_pushout a b hU hV hW) T).1 γ = K := by
      dsimp [γ]
      exact Equiv.apply_symm_apply _ _
    calc
      _ = ((Unit13.finiteSimplicialSetProduct_hom_equiv
            (pushout a b) Z (finiteNonempty_pushout a b hU hV hW) T).1 γ).1 n
            ((pushout.inr a b).app (op (SimplexCategory.mk n)) v) := hmap
      _ = K.1 n ((pushout.inr a b).app (op (SimplexCategory.mk n)) v) := by rw [hK]
      _ = gW.1 n v := compatibleFamily_pushout_inr a b fV gW hcompat v
      _ = _ := by rfl

private noncomputable def pushout_to_homFibreProduct_data
    {C : Type u} [Category.{v} C] [HasBinaryCoproducts C]
    [HasFiniteLimits C]
    {U V W : SSet.{w}} (a : U ⟶ V) (b : U ⟶ W)
    (T : SimplicialObject C)
    (hU : Unit13.FiniteNonemptySimplicialSet U)
    (hV : Unit13.FiniteNonemptySimplicialSet V)
    (hW : Unit13.FiniteNonemptySimplicialSet W)
    (hUdeg : EventuallyDegenerate U)
    (hVdeg : EventuallyDegenerate V)
    (hWdeg : EventuallyDegenerate W)
    (Z : SimplicialObject C)
    (γ : Unit13.simplicialSetProduct (pushout a b) Z
      (finiteNonempty_pushout a b hU hV hW) ⟶ T) :
    {lift : Z ⟶ homFibreProduct a b T hU hV hW hUdeg hVdeg hWdeg //
      lift ≫ homFibreProductFst a b T hU hV hW hUdeg hVdeg hWdeg =
          (homHomEquiv V T hV hVdeg Z).symm
            (Unit13.productWithSimplicialSetMap
              (ObjectProperty.homMk (pushout.inl a b) :
                (⟨V, hV⟩ : Unit13.FSSets.{w}) ⟶
                  (⟨pushout a b, finiteNonempty_pushout a b hU hV hW⟩ : Unit13.FSSets.{w}))
              (𝟙 Z) ≫ γ) ∧
      lift ≫ homFibreProductSnd a b T hU hV hW hUdeg hVdeg hWdeg =
          (homHomEquiv W T hW hWdeg Z).symm
            (Unit13.productWithSimplicialSetMap
              (ObjectProperty.homMk (pushout.inr a b) :
                (⟨W, hW⟩ : Unit13.FSSets.{w}) ⟶
                  (⟨pushout a b, finiteNonempty_pushout a b hU hV hW⟩ : Unit13.FSSets.{w}))
              (𝟙 Z) ≫ γ)} := by
  let fVmap : Unit13.simplicialSetProduct V Z hV ⟶ T :=
    Unit13.productWithSimplicialSetMap
      (ObjectProperty.homMk (pushout.inl a b) :
        (⟨V, hV⟩ : Unit13.FSSets.{w}) ⟶
          (⟨pushout a b, finiteNonempty_pushout a b hU hV hW⟩ : Unit13.FSSets.{w}))
      (𝟙 Z) ≫ γ
  let gWmap : Unit13.simplicialSetProduct W Z hW ⟶ T :=
    Unit13.productWithSimplicialSetMap
      (ObjectProperty.homMk (pushout.inr a b) :
        (⟨W, hW⟩ : Unit13.FSSets.{w}) ⟶
          (⟨pushout a b, finiteNonempty_pushout a b hU hV hW⟩ : Unit13.FSSets.{w}))
      (𝟙 Z) ≫ γ
  let sV : Z ⟶ hom V T hV hVdeg := (homHomEquiv V T hV hVdeg Z).symm fVmap
  let sW : Z ⟶ hom W T hW hWdeg := (homHomEquiv W T hW hWdeg Z).symm gWmap
  have hcompat :
      sV ≫ homPrecomp a T hU hV hUdeg hVdeg =
        sW ≫ homPrecomp b T hU hW hUdeg hWdeg := by
    apply (homHomEquiv U T hU hUdeg Z).injective
    rw [homPrecomp_homHomEquiv a T hU hV hUdeg hVdeg Z sV]
    rw [homPrecomp_homHomEquiv b T hU hW hUdeg hWdeg Z sW]
    have hsV : homHomEquiv V T hV hVdeg Z sV = fVmap := by
      dsimp [sV]
      exact Equiv.apply_symm_apply _ _
    have hsW : homHomEquiv W T hW hWdeg Z sW = gWmap := by
      dsimp [sW]
      exact Equiv.apply_symm_apply _ _
    rw [hsV, hsW]
    change
      Unit13.productWithSimplicialSetMap
          (ObjectProperty.homMk a :
            (⟨U, hU⟩ : Unit13.FSSets.{w}) ⟶ (⟨V, hV⟩ : Unit13.FSSets.{w})) (𝟙 Z) ≫ fVmap =
        Unit13.productWithSimplicialSetMap
          (ObjectProperty.homMk b :
            (⟨U, hU⟩ : Unit13.FSSets.{w}) ⟶ (⟨W, hW⟩ : Unit13.FSSets.{w})) (𝟙 Z) ≫ gWmap
    have hpush := productWithSimplicialSetMap_pushout_condition
      a b Z hU hV hW (finiteNonempty_pushout a b hU hV hW)
    dsimp at hpush
    rw [show fVmap =
      Unit13.productWithSimplicialSetMap
          (ObjectProperty.homMk (pushout.inl a b) :
            (⟨V, hV⟩ : Unit13.FSSets.{w}) ⟶
              (⟨pushout a b, finiteNonempty_pushout a b hU hV hW⟩ : Unit13.FSSets.{w}))
          (𝟙 Z) ≫ γ by rfl]
    rw [show gWmap =
      Unit13.productWithSimplicialSetMap
          (ObjectProperty.homMk (pushout.inr a b) :
            (⟨W, hW⟩ : Unit13.FSSets.{w}) ⟶
              (⟨pushout a b, finiteNonempty_pushout a b hU hV hW⟩ : Unit13.FSSets.{w}))
          (𝟙 Z) ≫ γ by rfl]
    rw [← Category.assoc, ← Category.assoc, hpush]
  let hex : ∃! lift : Z ⟶ homFibreProduct a b T hU hV hW hUdeg hVdeg hWdeg,
      lift ≫ homFibreProductFst a b T hU hV hW hUdeg hVdeg hWdeg = sV ∧
        lift ≫ homFibreProductSnd a b T hU hV hW hUdeg hVdeg hWdeg = sW :=
    Unit07.simplicialFibreProduct_universal_property
      (homPrecomp a T hU hV hUdeg hVdeg)
      (homPrecomp b T hU hW hUdeg hWdeg)
      (homPrecomp_hasDegreewiseFibreProducts a b T hU hV hW
        hUdeg hVdeg hWdeg)
      Z sV sW hcompat
  exact ⟨Classical.choose hex, (Classical.choose_spec hex).1⟩

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
  let hP := finiteNonempty_pushout a b hU hV hW
  let hPdeg := eventuallyDegenerate_pushout a b hUdeg hVdeg hWdeg
  let HP := homFibreProduct a b T hU hV hW hUdeg hVdeg hWdeg
  let H := hom (pushout a b) T hP hPdeg
  let F0 := homFibreProduct_to_pushout_data a b T hU hV hW hUdeg hVdeg hWdeg
    HP (𝟙 HP)
  let γ0 := homHomEquiv (pushout a b) T hP hPdeg H (𝟙 H)
  let G0 := pushout_to_homFibreProduct_data a b T hU hV hW hUdeg hVdeg hWdeg H γ0
  let i : HP ⟶ H :=
    (homHomEquiv (pushout a b) T hP hPdeg HP).symm F0.1
  let j : H ⟶ HP := G0.1
  have hi_repr :
      homHomEquiv (pushout a b) T hP hPdeg HP i = F0.1 := by
    dsimp [i]
    exact Equiv.apply_symm_apply _ _
  have hF : F0.1 =
      productWithSimplicialSetMapSecond (pushout a b) hP i ≫ γ0 := by
    calc
      F0.1 = homHomEquiv (pushout a b) T hP hPdeg HP i := hi_repr.symm
      _ = homHomEquiv (pushout a b) T hP hPdeg HP (i ≫ 𝟙 H) := by simp
      _ = productWithSimplicialSetMapSecond (pushout a b) hP i ≫ γ0 := by
        rw [homHomEquiv_comp]
  have hprod_inl :
      Unit13.productWithSimplicialSetMap
          (ObjectProperty.homMk (pushout.inl a b) :
            (⟨V, hV⟩ : Unit13.FSSets.{w}) ⟶
              (⟨pushout a b, hP⟩ : Unit13.FSSets.{w})) (𝟙 HP) ≫
        productWithSimplicialSetMapSecond (pushout a b) hP i =
      productWithSimplicialSetMapSecond V hV i ≫
        Unit13.productWithSimplicialSetMap
          (ObjectProperty.homMk (pushout.inl a b) :
            (⟨V, hV⟩ : Unit13.FSSets.{w}) ⟶
              (⟨pushout a b, hP⟩ : Unit13.FSSets.{w})) (𝟙 H) := by
    have hl := productWithSimplicialSetMap_comp
      (A := (⟨V, hV⟩ : Unit13.FSSets.{w}))
      (B := (⟨pushout a b, hP⟩ : Unit13.FSSets.{w}))
      (D := (⟨pushout a b, hP⟩ : Unit13.FSSets.{w}))
      (ObjectProperty.homMk (pushout.inl a b))
      (ObjectProperty.homMk (𝟙 (pushout a b))) (𝟙 HP) i
    have hr := productWithSimplicialSetMap_comp
      (A := (⟨V, hV⟩ : Unit13.FSSets.{w}))
      (B := (⟨V, hV⟩ : Unit13.FSSets.{w}))
      (D := (⟨pushout a b, hP⟩ : Unit13.FSSets.{w}))
      (ObjectProperty.homMk (𝟙 V)) (ObjectProperty.homMk (pushout.inl a b)) i (𝟙 H)
    dsimp [productWithSimplicialSetMapSecond]
    rw [hl, hr]
    have hleft :
        (ObjectProperty.homMk (pushout.inl a b) :
            (⟨V, hV⟩ : Unit13.FSSets.{w}) ⟶
              (⟨pushout a b, hP⟩ : Unit13.FSSets.{w})) ≫
          ObjectProperty.homMk (𝟙 (pushout a b)) =
        (ObjectProperty.homMk (pushout.inl a b) :
          (⟨V, hV⟩ : Unit13.FSSets.{w}) ⟶
            (⟨pushout a b, hP⟩ : Unit13.FSSets.{w})) := by
      ext X
      simp
    have hright :
        (ObjectProperty.homMk (𝟙 V) :
            (⟨V, hV⟩ : Unit13.FSSets.{w}) ⟶ (⟨V, hV⟩ : Unit13.FSSets.{w})) ≫
          (ObjectProperty.homMk (pushout.inl a b) :
            (⟨V, hV⟩ : Unit13.FSSets.{w}) ⟶
              (⟨pushout a b, hP⟩ : Unit13.FSSets.{w})) =
        (ObjectProperty.homMk (pushout.inl a b) :
          (⟨V, hV⟩ : Unit13.FSSets.{w}) ⟶
            (⟨pushout a b, hP⟩ : Unit13.FSSets.{w})) := by
      ext X
      simp
    have hf :
        (ObjectProperty.homMk (pushout.inl a b) :
            (⟨V, hV⟩ : Unit13.FSSets.{w}) ⟶
              (⟨pushout a b, hP⟩ : Unit13.FSSets.{w})) ≫
          ObjectProperty.homMk (𝟙 (pushout a b)) =
        (ObjectProperty.homMk (𝟙 V) :
            (⟨V, hV⟩ : Unit13.FSSets.{w}) ⟶ (⟨V, hV⟩ : Unit13.FSSets.{w})) ≫
          (ObjectProperty.homMk (pushout.inl a b) :
            (⟨V, hV⟩ : Unit13.FSSets.{w}) ⟶
              (⟨pushout a b, hP⟩ : Unit13.FSSets.{w})) :=
      hleft.trans hright.symm
    have hz : (𝟙 HP ≫ i) = (i ≫ 𝟙 H) := by simp
    exact congrArg₂ (fun f r => Unit13.productWithSimplicialSetMap f r) hf hz
  have hprod_inr :
      Unit13.productWithSimplicialSetMap
          (ObjectProperty.homMk (pushout.inr a b) :
            (⟨W, hW⟩ : Unit13.FSSets.{w}) ⟶
              (⟨pushout a b, hP⟩ : Unit13.FSSets.{w})) (𝟙 HP) ≫
        productWithSimplicialSetMapSecond (pushout a b) hP i =
      productWithSimplicialSetMapSecond W hW i ≫
        Unit13.productWithSimplicialSetMap
          (ObjectProperty.homMk (pushout.inr a b) :
            (⟨W, hW⟩ : Unit13.FSSets.{w}) ⟶
              (⟨pushout a b, hP⟩ : Unit13.FSSets.{w})) (𝟙 H) := by
    have hl := productWithSimplicialSetMap_comp
      (A := (⟨W, hW⟩ : Unit13.FSSets.{w}))
      (B := (⟨pushout a b, hP⟩ : Unit13.FSSets.{w}))
      (D := (⟨pushout a b, hP⟩ : Unit13.FSSets.{w}))
      (ObjectProperty.homMk (pushout.inr a b))
      (ObjectProperty.homMk (𝟙 (pushout a b))) (𝟙 HP) i
    have hr := productWithSimplicialSetMap_comp
      (A := (⟨W, hW⟩ : Unit13.FSSets.{w}))
      (B := (⟨W, hW⟩ : Unit13.FSSets.{w}))
      (D := (⟨pushout a b, hP⟩ : Unit13.FSSets.{w}))
      (ObjectProperty.homMk (𝟙 W)) (ObjectProperty.homMk (pushout.inr a b)) i (𝟙 H)
    dsimp [productWithSimplicialSetMapSecond]
    rw [hl, hr]
    have hleft :
        (ObjectProperty.homMk (pushout.inr a b) :
            (⟨W, hW⟩ : Unit13.FSSets.{w}) ⟶
              (⟨pushout a b, hP⟩ : Unit13.FSSets.{w})) ≫
          ObjectProperty.homMk (𝟙 (pushout a b)) =
        (ObjectProperty.homMk (pushout.inr a b) :
          (⟨W, hW⟩ : Unit13.FSSets.{w}) ⟶
            (⟨pushout a b, hP⟩ : Unit13.FSSets.{w})) := by
      ext X
      simp
    have hright :
        (ObjectProperty.homMk (𝟙 W) :
            (⟨W, hW⟩ : Unit13.FSSets.{w}) ⟶ (⟨W, hW⟩ : Unit13.FSSets.{w})) ≫
          (ObjectProperty.homMk (pushout.inr a b) :
            (⟨W, hW⟩ : Unit13.FSSets.{w}) ⟶
              (⟨pushout a b, hP⟩ : Unit13.FSSets.{w})) =
        (ObjectProperty.homMk (pushout.inr a b) :
          (⟨W, hW⟩ : Unit13.FSSets.{w}) ⟶
            (⟨pushout a b, hP⟩ : Unit13.FSSets.{w})) := by
      ext X
      simp
    have hf :
        (ObjectProperty.homMk (pushout.inr a b) :
            (⟨W, hW⟩ : Unit13.FSSets.{w}) ⟶
              (⟨pushout a b, hP⟩ : Unit13.FSSets.{w})) ≫
          ObjectProperty.homMk (𝟙 (pushout a b)) =
        (ObjectProperty.homMk (𝟙 W) :
            (⟨W, hW⟩ : Unit13.FSSets.{w}) ⟶ (⟨W, hW⟩ : Unit13.FSSets.{w})) ≫
          (ObjectProperty.homMk (pushout.inr a b) :
            (⟨W, hW⟩ : Unit13.FSSets.{w}) ⟶
              (⟨pushout a b, hP⟩ : Unit13.FSSets.{w})) :=
      hleft.trans hright.symm
    have hz : (𝟙 HP ≫ i) = (i ≫ 𝟙 H) := by simp
    exact congrArg₂ (fun f r => Unit13.productWithSimplicialSetMap f r) hf hz
  refine ⟨{ hom := i, inv := j, hom_inv_id := ?_, inv_hom_id := ?_ }⟩
  · apply (homFibreProduct_isPullback a b T hU hV hW hUdeg hVdeg hWdeg).hom_ext
    · rw [Category.assoc, G0.2.1]
      apply (homHomEquiv V T hV hVdeg HP).injective
      rw [homHomEquiv_comp, Equiv.apply_symm_apply]
      calc
        productWithSimplicialSetMapSecond V hV i ≫
              Unit13.productWithSimplicialSetMap
                (ObjectProperty.homMk (pushout.inl a b) :
                  (⟨V, hV⟩ : Unit13.FSSets.{w}) ⟶
                    (⟨pushout a b, hP⟩ : Unit13.FSSets.{w})) (𝟙 H) ≫ γ0 =
            Unit13.productWithSimplicialSetMap
                (ObjectProperty.homMk (pushout.inl a b) :
                  (⟨V, hV⟩ : Unit13.FSSets.{w}) ⟶
                    (⟨pushout a b, hP⟩ : Unit13.FSSets.{w})) (𝟙 HP) ≫
              productWithSimplicialSetMapSecond (pushout a b) hP i ≫ γ0 := by
          simpa only [Category.assoc] using
            congrArg (fun k => k ≫ γ0) hprod_inl.symm
        _ = Unit13.productWithSimplicialSetMap
                (ObjectProperty.homMk (pushout.inl a b) :
                  (⟨V, hV⟩ : Unit13.FSSets.{w}) ⟶
                    (⟨pushout a b, hP⟩ : Unit13.FSSets.{w})) (𝟙 HP) ≫ F0.1 := by
          rw [hF]
        _ = homHomEquiv V T hV hVdeg HP
              (𝟙 (homFibreProduct a b T hU hV hW hUdeg hVdeg hWdeg) ≫
                homFibreProductFst a b T hU hV hW hUdeg hVdeg hWdeg) := by
          simpa [HP] using F0.2.1
    · rw [Category.assoc, G0.2.2]
      apply (homHomEquiv W T hW hWdeg HP).injective
      rw [homHomEquiv_comp, Equiv.apply_symm_apply]
      calc
        productWithSimplicialSetMapSecond W hW i ≫
              Unit13.productWithSimplicialSetMap
                (ObjectProperty.homMk (pushout.inr a b) :
                  (⟨W, hW⟩ : Unit13.FSSets.{w}) ⟶
                    (⟨pushout a b, hP⟩ : Unit13.FSSets.{w})) (𝟙 H) ≫ γ0 =
            Unit13.productWithSimplicialSetMap
                (ObjectProperty.homMk (pushout.inr a b) :
                  (⟨W, hW⟩ : Unit13.FSSets.{w}) ⟶
                    (⟨pushout a b, hP⟩ : Unit13.FSSets.{w})) (𝟙 HP) ≫
              productWithSimplicialSetMapSecond (pushout a b) hP i ≫ γ0 := by
          simpa only [Category.assoc] using
            congrArg (fun k => k ≫ γ0) hprod_inr.symm
        _ = Unit13.productWithSimplicialSetMap
                (ObjectProperty.homMk (pushout.inr a b) :
                  (⟨W, hW⟩ : Unit13.FSSets.{w}) ⟶
                    (⟨pushout a b, hP⟩ : Unit13.FSSets.{w})) (𝟙 HP) ≫ F0.1 := by
          rw [hF]
        _ = homHomEquiv W T hW hWdeg HP
              (𝟙 (homFibreProduct a b T hU hV hW hUdeg hVdeg hWdeg) ≫
                homFibreProductSnd a b T hU hV hW hUdeg hVdeg hWdeg) := by
          simpa [HP] using F0.2.2
  · apply (homHomEquiv (pushout a b) T hP hPdeg H).injective
    rw [homHomEquiv_comp, hi_repr]
    apply (Unit13.finiteSimplicialSetProduct_hom_equiv
      (pushout a b) H hP T).injective
    apply Subtype.ext
    funext n p
    have hsecondP := finiteProductMap_second_family_apply H HP T hP j n p F0.1
    apply Eq.trans hsecondP
    have hF0V :
        Unit13.productWithSimplicialSetMap
            (ObjectProperty.homMk (pushout.inl a b) :
              (⟨V, hV⟩ : Unit13.FSSets.{w}) ⟶
                (⟨pushout a b, hP⟩ : Unit13.FSSets.{w})) (𝟙 HP) ≫ F0.1 =
          homHomEquiv V T hV hVdeg HP
            (homFibreProductFst a b T hU hV hW hUdeg hVdeg hWdeg) := by
      simpa [HP, Category.id_comp] using F0.2.1
    have hF0W :
        Unit13.productWithSimplicialSetMap
            (ObjectProperty.homMk (pushout.inr a b) :
              (⟨W, hW⟩ : Unit13.FSSets.{w}) ⟶
                (⟨pushout a b, hP⟩ : Unit13.FSSets.{w})) (𝟙 HP) ≫ F0.1 =
          homHomEquiv W T hW hWdeg HP
            (homFibreProductSnd a b T hU hV hW hUdeg hVdeg hWdeg) := by
      simpa [HP, Category.id_comp] using F0.2.2
    have hG0V :
        homHomEquiv V T hV hVdeg H
            (j ≫ homFibreProductFst a b T hU hV hW hUdeg hVdeg hWdeg) =
          Unit13.productWithSimplicialSetMap
            (ObjectProperty.homMk (pushout.inl a b) :
              (⟨V, hV⟩ : Unit13.FSSets.{w}) ⟶
                (⟨pushout a b, hP⟩ : Unit13.FSSets.{w})) (𝟙 H) ≫ γ0 := by
      rw [G0.2.1]
      exact Equiv.apply_symm_apply _ _
    have hG0W :
        homHomEquiv W T hW hWdeg H
            (j ≫ homFibreProductSnd a b T hU hV hW hUdeg hVdeg hWdeg) =
          Unit13.productWithSimplicialSetMap
            (ObjectProperty.homMk (pushout.inr a b) :
              (⟨W, hW⟩ : Unit13.FSSets.{w}) ⟶
                (⟨pushout a b, hP⟩ : Unit13.FSSets.{w})) (𝟙 H) ≫ γ0 := by
      rw [G0.2.2]
      exact Equiv.apply_symm_apply _ _
    have hcompV :
        productWithSimplicialSetMapSecond V hV j ≫
            homHomEquiv V T hV hVdeg HP
              (homFibreProductFst a b T hU hV hW hUdeg hVdeg hWdeg) =
          Unit13.productWithSimplicialSetMap
            (ObjectProperty.homMk (pushout.inl a b) :
              (⟨V, hV⟩ : Unit13.FSSets.{w}) ⟶
                (⟨pushout a b, hP⟩ : Unit13.FSSets.{w})) (𝟙 H) ≫ γ0 := by
      rw [← homHomEquiv_comp]
      exact hG0V
    have hcompW :
        productWithSimplicialSetMapSecond W hW j ≫
            homHomEquiv W T hW hWdeg HP
              (homFibreProductSnd a b T hU hV hW hUdeg hVdeg hWdeg) =
          Unit13.productWithSimplicialSetMap
            (ObjectProperty.homMk (pushout.inr a b) :
              (⟨W, hW⟩ : Unit13.FSSets.{w}) ⟶
                (⟨pushout a b, hP⟩ : Unit13.FSSets.{w})) (𝟙 H) ≫ γ0 := by
      rw [← homHomEquiv_comp]
      exact hG0W
    have hinl : ∀ v : V _⦋n⦌,
        j.app (op (SimplexCategory.mk n)) ≫
              ((Unit13.finiteSimplicialSetProduct_hom_equiv
                (pushout a b) HP hP T).1 F0.1).1 n
                ((pushout.inl a b).app (op (SimplexCategory.mk n)) v) =
          ((Unit13.finiteSimplicialSetProduct_hom_equiv
            (pushout a b) H hP T).1 γ0).1 n
              ((pushout.inl a b).app (op (SimplexCategory.mk n)) v) := by
      intro v
      have hmapF := finiteProductMap_family_apply (pushout.inl a b) HP T hV hP v F0.1
      have hsecondV := finiteProductMap_second_family_apply H HP T hV j n v
        (homHomEquiv V T hV hVdeg HP
          (homFibreProductFst a b T hU hV hW hUdeg hVdeg hWdeg))
      have hpoint := congrArg
        (fun k =>
          ((Unit13.finiteSimplicialSetProduct_hom_equiv V H hV T).1 k).1 n v)
        hcompV
      calc
        j.app (op (SimplexCategory.mk n)) ≫
              ((Unit13.finiteSimplicialSetProduct_hom_equiv
                (pushout a b) HP hP T).1 F0.1).1 n
                ((pushout.inl a b).app (op (SimplexCategory.mk n)) v) =
            j.app (op (SimplexCategory.mk n)) ≫
              ((Unit13.finiteSimplicialSetProduct_hom_equiv V HP hV T).1
                (Unit13.productWithSimplicialSetMap
                  (ObjectProperty.homMk (pushout.inl a b) :
                    (⟨V, hV⟩ : Unit13.FSSets.{w}) ⟶
                      (⟨pushout a b, hP⟩ : Unit13.FSSets.{w})) (𝟙 HP) ≫ F0.1)).1 n v := by
          rw [hmapF]
        _ = j.app (op (SimplexCategory.mk n)) ≫
              ((Unit13.finiteSimplicialSetProduct_hom_equiv V HP hV T).1
                (homHomEquiv V T hV hVdeg HP
                  (homFibreProductFst a b T hU hV hW hUdeg hVdeg hWdeg))).1 n v := by
          rw [hF0V]
        _ = ((Unit13.finiteSimplicialSetProduct_hom_equiv V H hV T).1
              (productWithSimplicialSetMapSecond V hV j ≫
                homHomEquiv V T hV hVdeg HP
                  (homFibreProductFst a b T hU hV hW hUdeg hVdeg hWdeg))).1 n v := by
          exact hsecondV.symm
        _ = ((Unit13.finiteSimplicialSetProduct_hom_equiv V H hV T).1
              (Unit13.productWithSimplicialSetMap
                (ObjectProperty.homMk (pushout.inl a b) :
                  (⟨V, hV⟩ : Unit13.FSSets.{w}) ⟶
                    (⟨pushout a b, hP⟩ : Unit13.FSSets.{w})) (𝟙 H) ≫ γ0)).1 n v := hpoint
        _ = ((Unit13.finiteSimplicialSetProduct_hom_equiv
            (pushout a b) H hP T).1 γ0).1 n
              ((pushout.inl a b).app (op (SimplexCategory.mk n)) v) := by
          exact finiteProductMap_family_apply (pushout.inl a b) H T hV hP v γ0
    have hinr : ∀ v : W _⦋n⦌,
        j.app (op (SimplexCategory.mk n)) ≫
              ((Unit13.finiteSimplicialSetProduct_hom_equiv
                (pushout a b) HP hP T).1 F0.1).1 n
                ((pushout.inr a b).app (op (SimplexCategory.mk n)) v) =
          ((Unit13.finiteSimplicialSetProduct_hom_equiv
            (pushout a b) H hP T).1 γ0).1 n
              ((pushout.inr a b).app (op (SimplexCategory.mk n)) v) := by
      intro v
      have hmapF := finiteProductMap_family_apply (pushout.inr a b) HP T hW hP v F0.1
      have hsecondW := finiteProductMap_second_family_apply H HP T hW j n v
        (homHomEquiv W T hW hWdeg HP
          (homFibreProductSnd a b T hU hV hW hUdeg hVdeg hWdeg))
      have hpoint := congrArg
        (fun k =>
          ((Unit13.finiteSimplicialSetProduct_hom_equiv W H hW T).1 k).1 n v)
        hcompW
      calc
        j.app (op (SimplexCategory.mk n)) ≫
              ((Unit13.finiteSimplicialSetProduct_hom_equiv
                (pushout a b) HP hP T).1 F0.1).1 n
                ((pushout.inr a b).app (op (SimplexCategory.mk n)) v) =
            j.app (op (SimplexCategory.mk n)) ≫
              ((Unit13.finiteSimplicialSetProduct_hom_equiv W HP hW T).1
                (Unit13.productWithSimplicialSetMap
                  (ObjectProperty.homMk (pushout.inr a b) :
                    (⟨W, hW⟩ : Unit13.FSSets.{w}) ⟶
                      (⟨pushout a b, hP⟩ : Unit13.FSSets.{w})) (𝟙 HP) ≫ F0.1)).1 n v := by
          rw [hmapF]
        _ = j.app (op (SimplexCategory.mk n)) ≫
              ((Unit13.finiteSimplicialSetProduct_hom_equiv W HP hW T).1
                (homHomEquiv W T hW hWdeg HP
                  (homFibreProductSnd a b T hU hV hW hUdeg hVdeg hWdeg))).1 n v := by
          rw [hF0W]
        _ = ((Unit13.finiteSimplicialSetProduct_hom_equiv W H hW T).1
              (productWithSimplicialSetMapSecond W hW j ≫
                homHomEquiv W T hW hWdeg HP
                  (homFibreProductSnd a b T hU hV hW hUdeg hVdeg hWdeg))).1 n v := by
          exact hsecondW.symm
        _ = ((Unit13.finiteSimplicialSetProduct_hom_equiv W H hW T).1
              (Unit13.productWithSimplicialSetMap
                (ObjectProperty.homMk (pushout.inr a b) :
                  (⟨W, hW⟩ : Unit13.FSSets.{w}) ⟶
                    (⟨pushout a b, hP⟩ : Unit13.FSSets.{w})) (𝟙 H) ≫ γ0)).1 n v := hpoint
        _ = ((Unit13.finiteSimplicialSetProduct_hom_equiv
            (pushout a b) H hP T).1 γ0).1 n
              ((pushout.inr a b).app (op (SimplexCategory.mk n)) v) := by
          exact finiteProductMap_family_apply (pushout.inr a b) H T hW hP v γ0
    let X : SimplexCategoryᵒᵖ := op (SimplexCategory.mk n)
    let e := pushoutObjIso a b X
    let q : pushout (a.app X) (b.app X) := e.hom p
    obtain ⟨k, y, hy⟩ :=
      Types.jointly_surjective_of_isColimit
        (pushout.isColimit (a.app X) (b.app X)) q
    obtain (_ | _ | _) := k
    ·
      change U.obj X at y
      have hz := congrArg (fun k => k y)
        (PushoutCocone.condition_zero (pushout.cocone (a.app X) (b.app X)))
      have hp : (pushout.inl a b).app X ((a.app X) y) = p := by
        let e' := pushoutObjIso a b X
        have hhy : ((pushout.cocone (a.app X) (b.app X)).ι.app WalkingSpan.left)
              ((a.app X) y) = q := by
          exact hz.symm.trans hy
        have hhom : (pushoutObjIso a b X).hom
              ((pushout.inl a b).app X ((a.app X) y)) =
            pushout.inl (a.app X) (b.app X) ((a.app X) y) := by
          simpa only [CategoryTheory.comp_apply] using
            congrArg (fun k => k ((a.app X) y)) (inl_comp_pushoutObjIso_hom a b X)
        have hh : e'.hom ((pushout.inl a b).app X ((a.app X) y)) = e'.hom p := by
          simpa [e', q] using hhom.trans hhy
        have hh' := congrArg (fun z => e'.inv z) hh
        simpa [e'] using hh'
      rw [← hp]
      exact hinl _
    ·
      change V.obj X at y
      have hp : (pushout.inl a b).app X y = p := by
        let e' := pushoutObjIso a b X
        have hhy : pushout.inl (a.app X) (b.app X) y = q := by
          change pushout.inl (a.app X) (b.app X) y = q at hy
          exact hy
        have hhom : (pushoutObjIso a b X).hom ((pushout.inl a b).app X y) =
            pushout.inl (a.app X) (b.app X) y := by
          simpa only [CategoryTheory.comp_apply] using
            congrArg (fun k => k y) (inl_comp_pushoutObjIso_hom a b X)
        have hh : e'.hom ((pushout.inl a b).app X y) = e'.hom p := by
          simpa [e', q] using hhom.trans hhy
        have hh' := congrArg (fun z => e'.inv z) hh
        simpa [e'] using hh'
      rw [← hp]
      exact hinl y
    ·
      change W.obj X at y
      have hp : (pushout.inr a b).app X y = p := by
        let e' := pushoutObjIso a b X
        have hhy : pushout.inr (a.app X) (b.app X) y = q := by
          change pushout.inr (a.app X) (b.app X) y = q at hy
          exact hy
        have hhom : (pushoutObjIso a b X).hom ((pushout.inr a b).app X y) =
            pushout.inr (a.app X) (b.app X) y := by
          simpa only [CategoryTheory.comp_apply] using
            congrArg (fun k => k y) (inr_comp_pushoutObjIso_hom a b X)
        have hh : e'.hom ((pushout.inr a b).app X y) = e'.hom p := by
          simpa [e', q] using hhom.trans hhy
        have hh' := congrArg (fun z => e'.inv z) hh
        simpa [e'] using hh'
      rw [← hp]
      exact hinr y

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
