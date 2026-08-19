import Formalization.Books.Simplicial.Unit07.FibreProducts
import Formalization.Books.Simplicial.Unit13.ProductsWithSimplicialSets
import Mathlib.AlgebraicTopology.SimplicialSet.Dimension
import Mathlib.CategoryTheory.Functor.KanExtension.Pointwise
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
