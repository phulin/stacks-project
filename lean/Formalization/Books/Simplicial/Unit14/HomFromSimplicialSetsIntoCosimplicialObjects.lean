import Formalization.Books.Simplicial.Unit11.SimplicialSets
import Formalization.Books.Simplicial.Unit13.ProductsWithSimplicialSets
import Mathlib.CategoryTheory.Limits.Shapes.FiniteProducts

/-!
# Simplicial Methods, Chapter 14: Hom from simplicial sets into cosimplicial objects

The source's degreewise products are Mathlib's categorical products indexed by
the finite types of simplices.  The maps between those products are the
canonical reindexing maps `Limits.Pi.map'`, followed by the maps of the
cosimplicial object.
-/

namespace Formalization.Books.Simplicial.Unit14

open CategoryTheory
open CategoryTheory.Limits
open Opposite
open scoped _root_.Simplicial

universe v u w

/-! ## The motivating set-valued construction -/

/--
The source's preliminary construction.  A simplicial object `U` and a
cosimplicial object `V` determine a cosimplicial set whose degree `n` consists
of morphisms `U_n ⟶ V_n`.
-/
def cosimplicialHomSet
    {C : Type w} [Category.{v} C]
    (U : SimplicialObject C) (V : CosimplicialObject C) :
    CosimplicialObject (Type v) where
  obj X := U.obj (op X) ⟶ V.obj X
  map f := ↾fun g => U.map f.op ≫ g ≫ V.map f
  map_id := by
    intro X
    ext f
    change U.map (𝟙 X).op ≫ f ≫ V.map (𝟙 X) = f
    simp
    rw [V.map_id]
    simp
  map_comp := by
    intro X Y Z f g
    ext h
    change
      U.map (f ≫ g).op ≫ h ≫ V.map (f ≫ g) =
        U.map g.op ≫ (U.map f.op ≫ h ≫ V.map f) ≫ V.map g
    simp only [op_comp, U.map_comp, V.map_comp, Category.assoc]

theorem cosimplicialHomSet_obj
    {C : Type w} [Category.{v} C]
    (U : SimplicialObject C) (V : CosimplicialObject C) (n : ℕ) :
    (cosimplicialHomSet U V).obj (SimplexCategory.mk n) =
      (U _⦋n⦌ ⟶ V ^⦋n⦌) := rfl

theorem cosimplicialHomSet_map
    {C : Type w} [Category.{v} C]
    (U : SimplicialObject C) (V : CosimplicialObject C)
    {m n : ℕ} (φ : SimplexCategory.mk m ⟶ SimplexCategory.mk n)
    (f : U _⦋m⦌ ⟶ V ^⦋m⦌) :
    (cosimplicialHomSet U V).map φ f =
      U.map φ.op ≫ f ≫ V.map φ := by
  change U.map φ.op ≫ f ≫ V.map φ = U.map φ.op ≫ f ≫ V.map φ
  rfl

/-! ## The finite-product Hom construction -/

/-- The chosen product defining the Hom object at an arbitrary object of `Δ`. -/
noncomputable def homObjectAt
    {C : Type w} [Category.{v} C] [HasFiniteProducts C]
    (U : SSet.{u}) (V : CosimplicialObject C)
    (hU : Unit13.FiniteNonemptySimplicialSet U) (X : SimplexCategory) : C :=
  letI : Finite (U.obj (op X)) := by
    simpa only [SimplexCategory.mk_len] using (hU X.len).1
  ∏ᶜ fun _ : U.obj (op X) => V.obj X

/-- The source's product in degree `n`. -/
noncomputable def homObject
    {C : Type w} [Category.{v} C] [HasFiniteProducts C]
    (U : SSet.{u}) (V : CosimplicialObject C)
    (hU : Unit13.FiniteNonemptySimplicialSet U) (n : ℕ) : C :=
  homObjectAt U V hU (SimplexCategory.mk n)

/-- The map between the chosen products associated to a map in `Δ`. -/
noncomputable def homMapAt
    {C : Type w} [Category.{v} C] [HasFiniteProducts C]
    (U : SSet.{u}) (V : CosimplicialObject C)
    (hU : Unit13.FiniteNonemptySimplicialSet U) {X Y : SimplexCategory}
    (φ : X ⟶ Y) : homObjectAt U V hU X ⟶ homObjectAt U V hU Y := by
  letI : Finite (U.obj (op X)) := by
    simpa only [SimplexCategory.mk_len] using (hU X.len).1
  letI : Finite (U.obj (op Y)) := by
    simpa only [SimplexCategory.mk_len] using (hU Y.len).1
  change
    (∏ᶜ fun _ : U.obj (op X) => V.obj X) ⟶
      (∏ᶜ fun _ : U.obj (op Y) => V.obj Y)
  exact Pi.map' (U.map φ.op) (fun _ => V.map φ)

/-- The cosimplicial object `Hom(U,V)`, formed degree by degree. -/
noncomputable def hom
    {C : Type w} [Category.{v} C] [HasFiniteProducts C]
    (U : SSet.{u}) (V : CosimplicialObject C)
    (hU : Unit13.FiniteNonemptySimplicialSet U) : CosimplicialObject C where
  obj := homObjectAt U V hU
  map := fun {X Y} φ => homMapAt U V hU φ
  map_id := by
    intro X
    dsimp [homMapAt, homObjectAt]
    let _ : Finite (U.obj (op X)) := by
      simpa only [SimplexCategory.mk_len] using (hU X.len).1
    ext u
    simp [Pi.map'_comp_π]
    rw [V.map_id]
    simp
  map_comp := by
    intro X Y Z f g
    dsimp [homMapAt, homObjectAt]
    let _ : Finite (U.obj (op X)) := by
      simpa only [SimplexCategory.mk_len] using (hU X.len).1
    let _ : Finite (U.obj (op Y)) := by
      simpa only [SimplexCategory.mk_len] using (hU Y.len).1
    let _ : Finite (U.obj (op Z)) := by
      simpa only [SimplexCategory.mk_len] using (hU Z.len).1
    ext u
    simp [Pi.map'_comp_π, Category.assoc]
    rw [V.map_comp]

theorem hom_obj
    {C : Type w} [Category.{v} C] [HasFiniteProducts C]
    (U : SSet.{u}) (V : CosimplicialObject C)
    (hU : Unit13.FiniteNonemptySimplicialSet U) (n : ℕ) :
    (hom U V hU).obj (SimplexCategory.mk n) = homObject U V hU n := rfl

theorem hom_map
    {C : Type w} [Category.{v} C] [HasFiniteProducts C]
    (U : SSet.{u}) (V : CosimplicialObject C)
    (hU : Unit13.FiniteNonemptySimplicialSet U) {m n : ℕ}
    (φ : SimplexCategory.mk m ⟶ SimplexCategory.mk n) :
    (hom U V hU).map φ = homMapAt U V hU φ := rfl

/-! ## The displayed `X`-valued-points formula -/

/--
The source's equality of hom-sets is the canonical product equivalence: a map
into the product is sent to its family of composites with the projections.
-/
noncomputable def homObjectHomEquiv
    {C : Type w} [Category.{v} C] [HasFiniteProducts C]
    (U : SSet.{u}) (V : CosimplicialObject C)
    (hU : Unit13.FiniteNonemptySimplicialSet U) (X : C) (n : ℕ) :
    (X ⟶ homObject U V hU n) ≃
      (U _⦋n⦌ → (X ⟶ V ^⦋n⦌)) := by
  letI : Finite (U _⦋n⦌) := (hU n).1
  change
    (X ⟶ ∏ᶜ fun _ : U _⦋n⦌ => V ^⦋n⦌) ≃
      (U _⦋n⦌ → (X ⟶ V ^⦋n⦌))
  exact
    { toFun := fun f u => f ≫ Pi.π _ u
      invFun := fun f => Pi.lift f
      left_inv := by
        intro f
        apply Pi.hom_ext
        intro u
        exact Pi.lift_π _ _
      right_inv := by
        intro f
        funext u
        exact Pi.lift_π _ _ }

/-- The product map has the source's stated action on `X`-valued points. -/
theorem homMapAt_pointwise
    {C : Type w} [Category.{v} C] [HasFiniteProducts C]
    (U : SSet.{u}) (V : CosimplicialObject C)
    (hU : Unit13.FiniteNonemptySimplicialSet U)
    {m n : ℕ} (φ : SimplexCategory.mk m ⟶ SimplexCategory.mk n)
    (X : C) (f : X ⟶ homObject U V hU m) (u : U _⦋n⦌) :
    homObjectHomEquiv U V hU X n (f ≫ homMapAt U V hU φ) u =
      homObjectHomEquiv U V hU X m f (U.map φ.op u) ≫ V.map φ := by
  let _ : Finite (U _⦋m⦌) := (hU m).1
  let _ : Finite (U _⦋n⦌) := (hU n).1
  change
    (f ≫ Pi.map' (U.map φ.op) (fun _ => V.map φ)) ≫
        Pi.π (fun _ : U _⦋n⦌ => V.obj (SimplexCategory.mk n)) u =
      (f ≫ Pi.π (fun _ : U _⦋m⦌ => V.obj (SimplexCategory.mk m)) (U.map φ.op u)) ≫
        V.map φ
  have h :
      Pi.map' (U.map φ.op) (fun _ => V.map φ) ≫
          Pi.π (fun _ : U _⦋n⦌ => V.obj (SimplexCategory.mk n)) u =
        Pi.π (fun _ : U _⦋m⦌ => V.obj (SimplexCategory.mk m)) (U.map φ.op u) ≫
          V.map φ :=
    Pi.map'_comp_π
      (f := fun _ : U _⦋m⦌ => V.obj (SimplexCategory.mk m))
      (g := fun _ : U _⦋n⦌ => V.obj (SimplexCategory.mk n))
      (U.map φ.op) (fun _ => V.map φ) u
  calc
    _ = f ≫ (Pi.map' (U.map φ.op) (fun _ => V.map φ) ≫
        Pi.π (fun _ : U _⦋n⦌ => V.obj (SimplexCategory.mk n)) u) :=
      Category.assoc f (Pi.map' (U.map φ.op) (fun _ => V.map φ))
        (Pi.π (fun _ : U _⦋n⦌ => V.obj (SimplexCategory.mk n)) u)
    _ = f ≫ (Pi.π (fun _ : U _⦋m⦌ => V.obj (SimplexCategory.mk m)) (U.map φ.op u) ≫
        V.map φ) := congrArg (fun k => f ≫ k) h
    _ = _ :=
      (Category.assoc f
        (Pi.π (fun _ : U _⦋m⦌ => V.obj (SimplexCategory.mk m)) (U.map φ.op u))
        (V.map φ)).symm

/-! ## Functoriality in the two variables -/

/-- The map induced by a simplicial map in the contravariant variable. -/
noncomputable def homPrecompApp
    {C : Type w} [Category.{v} C] [HasFiniteProducts C]
    {U U' : SSet.{u}} (f : U' ⟶ U) (V : CosimplicialObject C)
    (hU : Unit13.FiniteNonemptySimplicialSet U)
    (hU' : Unit13.FiniteNonemptySimplicialSet U')
    (X : SimplexCategory) :
    (hom U V hU).obj X ⟶ (hom U' V hU').obj X := by
  letI : Finite (U.obj (op X)) := by
    simpa only [SimplexCategory.mk_len] using (hU X.len).1
  letI : Finite (U'.obj (op X)) := by
    simpa only [SimplexCategory.mk_len] using (hU' X.len).1
  change
    (∏ᶜ fun _ : U.obj (op X) => V.obj X) ⟶
      (∏ᶜ fun _ : U'.obj (op X) => V.obj X)
  exact Pi.map' (f.app (op X)) (fun _ => 𝟙 (V.obj X))

/-- Precomposition makes `Hom(-,V)` contravariant in the simplicial set. -/
noncomputable def homPrecomp
    {C : Type w} [Category.{v} C] [HasFiniteProducts C]
    {U U' : SSet.{u}} (f : U' ⟶ U) (V : CosimplicialObject C)
    (hU : Unit13.FiniteNonemptySimplicialSet U)
    (hU' : Unit13.FiniteNonemptySimplicialSet U') :
    hom U V hU ⟶ hom U' V hU' where
  app X := homPrecompApp f V hU hU' X
  naturality := by
    intro X Y φ
    dsimp [homPrecompApp, homMapAt, homObjectAt]
    let _ : Finite (U.obj (op X)) := by
      simpa only [SimplexCategory.mk_len] using (hU X.len).1
    let _ : Finite (U.obj (op Y)) := by
      simpa only [SimplexCategory.mk_len] using (hU Y.len).1
    let _ : Finite (U'.obj (op X)) := by
      simpa only [SimplexCategory.mk_len] using (hU' X.len).1
    let _ : Finite (U'.obj (op Y)) := by
      simpa only [SimplexCategory.mk_len] using (hU' Y.len).1
    change
      (Pi.map'
          (f := fun _ : U.obj (op X) => V.obj X)
          (g := fun _ : U.obj (op Y) => V.obj Y)
          (U.map φ.op) (fun _ => V.map φ)) ≫
          (Pi.map'
            (f := fun _ : U.obj (op Y) => V.obj Y)
            (g := fun _ : U'.obj (op Y) => V.obj Y)
            (f.app (op Y)) (fun _ => 𝟙 (V.obj Y))) =
        (Pi.map'
            (f := fun _ : U.obj (op X) => V.obj X)
            (g := fun _ : U'.obj (op X) => V.obj X)
            (f.app (op X)) (fun _ => 𝟙 (V.obj X))) ≫
          (Pi.map'
            (f := fun _ : U'.obj (op X) => V.obj X)
            (g := fun _ : U'.obj (op Y) => V.obj Y)
            (U'.map φ.op) (fun _ => V.map φ))
    ext u
    simp [Pi.map'_comp_π, Category.assoc]

/-- The map induced by a cosimplicial map in the covariant variable. -/
noncomputable def homPostcompApp
    {C : Type w} [Category.{v} C] [HasFiniteProducts C]
    (U : SSet.{u}) {V V' : CosimplicialObject C} (f : V ⟶ V')
    (hU : Unit13.FiniteNonemptySimplicialSet U)
    (X : SimplexCategory) :
    (hom U V hU).obj X ⟶ (hom U V' hU).obj X := by
  letI : Finite (U.obj (op X)) := by
    simpa only [SimplexCategory.mk_len] using (hU X.len).1
  change
    (∏ᶜ fun _ : U.obj (op X) => V.obj X) ⟶
      (∏ᶜ fun _ : U.obj (op X) => V'.obj X)
  exact CategoryTheory.Limits.Pi.map (fun _ => f.app X)

/-- Postcomposition makes `Hom(U,-)` covariant in the cosimplicial object. -/
noncomputable def homPostcomp
    {C : Type w} [Category.{v} C] [HasFiniteProducts C]
    (U : SSet.{u}) {V V' : CosimplicialObject C} (f : V ⟶ V')
    (hU : Unit13.FiniteNonemptySimplicialSet U) :
    hom U V hU ⟶ hom U V' hU where
  app X := homPostcompApp U f hU X
  naturality := by
    intro X Y φ
    dsimp [homPostcompApp, homMapAt, homObjectAt]
    let _ : Finite (U.obj (op X)) := by
      simpa only [SimplexCategory.mk_len] using (hU X.len).1
    let _ : Finite (U.obj (op Y)) := by
      simpa only [SimplexCategory.mk_len] using (hU Y.len).1
    change
      (Pi.map' (U.map φ.op) (fun _ => V.map φ)) ≫
          (CategoryTheory.Limits.Pi.map (fun _ => f.app Y)) =
        (CategoryTheory.Limits.Pi.map (fun _ => f.app X)) ≫
          (Pi.map' (U.map φ.op) (fun _ => V'.map φ))
    ext u
    simp [Pi.map'_comp_π, Pi.map_π, Category.assoc]
    rw [f.naturality φ]

/-!
The following laws record the functoriality asserted in the source.  Their
maps are the canonical product maps above; the proofs are deferred to the
proof stage.
-/

theorem homPrecomp_id
    {C : Type w} [Category.{v} C] [HasFiniteProducts C]
    {U : SSet.{u}} (V : CosimplicialObject C)
    (hU : Unit13.FiniteNonemptySimplicialSet U) :
    homPrecomp (𝟙 U) V hU hU = 𝟙 (hom U V hU) := by
  ext X
  dsimp [homPrecomp, homPrecompApp, homObjectAt]
  let _ : Finite (U.obj (op X)) := by
    simpa only [SimplexCategory.mk_len] using (hU X.len).1
  change
    Pi.map' id (fun _ : U.obj (op X) => 𝟙 (V.obj X)) =
      𝟙 (∏ᶜ fun _ : U.obj (op X) => V.obj X)
  rw [Pi.map'_id_id]

theorem homPrecomp_comp
    {C : Type w} [Category.{v} C] [HasFiniteProducts C]
    {U₁ U₂ U₃ : SSet.{u}}
    (f : U₁ ⟶ U₂) (g : U₂ ⟶ U₃) (V : CosimplicialObject C)
    (h₁ : Unit13.FiniteNonemptySimplicialSet U₁)
    (h₂ : Unit13.FiniteNonemptySimplicialSet U₂)
    (h₃ : Unit13.FiniteNonemptySimplicialSet U₃) :
    homPrecomp g V h₃ h₂ ≫ homPrecomp f V h₂ h₁ =
      homPrecomp (f ≫ g) V h₃ h₁ := by
  ext X
  dsimp [homPrecomp, homPrecompApp, homObjectAt]
  let _ : Finite (U₁.obj (op X)) := by
    simpa only [SimplexCategory.mk_len] using (h₁ X.len).1
  let _ : Finite (U₂.obj (op X)) := by
    simpa only [SimplexCategory.mk_len] using (h₂ X.len).1
  let _ : Finite (U₃.obj (op X)) := by
    simpa only [SimplexCategory.mk_len] using (h₃ X.len).1
  change
    (Pi.map'
      (f := fun _ : U₃.obj (op X) => V.obj X)
      (g := fun _ : U₂.obj (op X) => V.obj X)
      (g.app (op X)) (fun _ => 𝟙 (V.obj X))) ≫
        Pi.map'
          (f := fun _ : U₂.obj (op X) => V.obj X)
          (g := fun _ : U₁.obj (op X) => V.obj X)
          (f.app (op X)) (fun _ => 𝟙 (V.obj X)) =
      Pi.map'
        (f := fun _ : U₃.obj (op X) => V.obj X)
        (g := fun _ : U₁.obj (op X) => V.obj X)
        (g.app (op X) ∘ f.app (op X)) (fun _ => 𝟙 (V.obj X))
  rw [Pi.map'_comp_map'
    (f := fun _ : U₃.obj (op X) => V.obj X)
    (g := fun _ : U₂.obj (op X) => V.obj X)
    (h := fun _ : U₁.obj (op X) => V.obj X)
    (g.app (op X)) (f.app (op X))
    (fun _ => 𝟙 (V.obj X)) (fun _ => 𝟙 (V.obj X))]
  simp

theorem homPostcomp_id
    {C : Type w} [Category.{v} C] [HasFiniteProducts C]
    (U : SSet.{u}) {V : CosimplicialObject C}
    (hU : Unit13.FiniteNonemptySimplicialSet U) :
    homPostcomp U (𝟙 V) hU = 𝟙 (hom U V hU) := by
  ext X
  dsimp [homPostcomp, homPostcompApp, homObjectAt]
  let _ : Finite (U.obj (op X)) := by
    simpa only [SimplexCategory.mk_len] using (hU X.len).1
  change
    CategoryTheory.Limits.Pi.map (fun _ : U.obj (op X) => 𝟙 (V.obj X)) =
      𝟙 (∏ᶜ fun _ : U.obj (op X) => V.obj X)
  simpa only using
    (CategoryTheory.Limits.Pi.map_id (f := fun _ : U.obj (op X) => V.obj X))

theorem homPostcomp_comp
    {C : Type w} [Category.{v} C] [HasFiniteProducts C]
    (U : SSet.{u}) {V V' V'' : CosimplicialObject C}
    (f : V ⟶ V') (g : V' ⟶ V'')
    (hU : Unit13.FiniteNonemptySimplicialSet U) :
    homPostcomp U f hU ≫ homPostcomp U g hU =
      homPostcomp U (f ≫ g) hU := by
  ext X
  dsimp [homPostcomp, homPostcompApp, homObjectAt]
  let _ : Finite (U.obj (op X)) := by
    simpa only [SimplexCategory.mk_len] using (hU X.len).1
  change
    (CategoryTheory.Limits.Pi.map (fun _ : U.obj (op X) => f.app X)) ≫
        CategoryTheory.Limits.Pi.map (fun _ : U.obj (op X) => g.app X) =
      CategoryTheory.Limits.Pi.map (fun _ : U.obj (op X) => f.app X ≫ g.app X)
  ext u
  simp [Category.assoc]

theorem homPrecomp_postcomp
    {C : Type w} [Category.{v} C] [HasFiniteProducts C]
    {U U' : SSet.{u}} {V V' : CosimplicialObject C}
    (f : U' ⟶ U) (g : V ⟶ V')
    (hU : Unit13.FiniteNonemptySimplicialSet U)
    (hU' : Unit13.FiniteNonemptySimplicialSet U') :
    homPrecomp f V hU hU' ≫ homPostcomp U' g hU' =
      homPostcomp U g hU ≫ homPrecomp f V' hU hU' := by
  ext X
  dsimp [homPrecomp, homPrecompApp, homPostcomp, homPostcompApp, homObjectAt]
  let _ : Finite (U.obj (op X)) := by
    simpa only [SimplexCategory.mk_len] using (hU X.len).1
  let _ : Finite (U'.obj (op X)) := by
    simpa only [SimplexCategory.mk_len] using (hU' X.len).1
  change
    (Pi.map' (f.app (op X)) (fun _ : U'.obj (op X) => 𝟙 (V.obj X))) ≫
        CategoryTheory.Limits.Pi.map (fun _ : U'.obj (op X) => g.app X) =
      CategoryTheory.Limits.Pi.map (fun _ : U.obj (op X) => g.app X) ≫
        Pi.map' (f.app (op X)) (fun _ : U'.obj (op X) => 𝟙 (V'.obj X))
  ext u
  simp [Pi.map'_comp_π, Category.assoc]

end Formalization.Books.Simplicial.Unit14
