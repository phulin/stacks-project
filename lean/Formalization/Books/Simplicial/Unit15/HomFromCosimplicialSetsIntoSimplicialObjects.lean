import Formalization.Books.Simplicial.Unit05.CosimplicialObjects
import Formalization.Books.Simplicial.Unit12.TruncatedSimplicialObjects
import Mathlib.CategoryTheory.Limits.Shapes.FiniteProducts

/-!
# Simplicial Methods, Chapter 15: Hom from cosimplicial sets into simplicial objects

The source's degreewise products are Mathlib's categorical products indexed by
the finite sets of simplices.  The maps between those products are the
canonical reindexing maps `Limits.Pi.map'`, followed by the maps of the
simplicial object.
-/

namespace Formalization.Books.Simplicial.Unit15

open CategoryTheory
open CategoryTheory.Limits
open Opposite
open scoped _root_.Simplicial

universe v u w

/-! ## The motivating set-valued construction -/

/--
The source's preliminary construction.  A cosimplicial object `U` and a
simplicial object `V` determine a simplicial set whose degree `n` consists of
morphisms `U_n ⟶ V_n`.
-/
def simplicialHomSet
    {C : Type w} [Category.{v} C]
    (U : CosimplicialObject C) (V : SimplicialObject C) :
    SimplicialObject (Type v) where
  obj X := U.obj X.unop ⟶ V.obj X
  map f := ↾fun g => U.map f.unop ≫ g ≫ V.map f
  map_id := by
    sorry
  map_comp := by
    sorry

theorem simplicialHomSet_obj
    {C : Type w} [Category.{v} C]
    (U : CosimplicialObject C) (V : SimplicialObject C) (n : ℕ) :
    (simplicialHomSet U V).obj (op (SimplexCategory.mk n)) =
      (U.obj (SimplexCategory.mk n) ⟶
        V.obj (op (SimplexCategory.mk n))) := rfl

theorem simplicialHomSet_map
    {C : Type w} [Category.{v} C]
    (U : CosimplicialObject C) (V : SimplicialObject C)
    {m n : ℕ} (φ : SimplexCategory.mk m ⟶ SimplexCategory.mk n)
    (f : U.obj (SimplexCategory.mk n) ⟶
      V.obj (op (SimplexCategory.mk n))) :
    (simplicialHomSet U V).map φ.op f =
      U.map φ ≫ f ≫ V.map φ.op := by
  change U.map φ ≫ f ≫ V.map φ.op = U.map φ ≫ f ≫ V.map φ.op
  rfl

/-! ## The finite-product Hom construction -/

/-- Every degree of a cosimplicial set is finite and nonempty. -/
abbrev FiniteNonemptyCosimplicialSet
    (U : CosimplicialObject (Type u)) : Prop :=
  ∀ n : ℕ,
    Finite (U.obj (SimplexCategory.mk n)) ∧
      Nonempty (U.obj (SimplexCategory.mk n))

/-- The chosen product defining the Hom object at an arbitrary object of `Δ`. -/
noncomputable def homObjectAt
    {C : Type w} [Category.{v} C] [HasFiniteProducts C]
    (U : CosimplicialObject (Type u)) (V : SimplicialObject C)
    (hU : FiniteNonemptyCosimplicialSet U) (X : SimplexCategory) : C :=
  letI : Finite (U.obj X) := by
    simpa only [SimplexCategory.mk_len] using (hU X.len).1
  ∏ᶜ fun _ : U.obj X => V.obj (op X)

/-- The source's product in degree `n`. -/
noncomputable def homObject
    {C : Type w} [Category.{v} C] [HasFiniteProducts C]
    (U : CosimplicialObject (Type u)) (V : SimplicialObject C)
    (hU : FiniteNonemptyCosimplicialSet U) (n : ℕ) : C :=
  homObjectAt U V hU (SimplexCategory.mk n)

/-- The map between the chosen products associated to a map in `Δ`. -/
noncomputable def homMapAt
    {C : Type w} [Category.{v} C] [HasFiniteProducts C]
    (U : CosimplicialObject (Type u)) (V : SimplicialObject C)
    (hU : FiniteNonemptyCosimplicialSet U) {X Y : SimplexCategory}
    (φ : X ⟶ Y) : homObjectAt U V hU Y ⟶ homObjectAt U V hU X := by
  letI : Finite (U.obj X) := by
    simpa only [SimplexCategory.mk_len] using (hU X.len).1
  letI : Finite (U.obj Y) := by
    simpa only [SimplexCategory.mk_len] using (hU Y.len).1
  change
    (∏ᶜ fun _ : U.obj Y => V.obj (op Y)) ⟶
      (∏ᶜ fun _ : U.obj X => V.obj (op X))
  exact Pi.map' (U.map φ) (fun _ => V.map φ.op)

/-- The simplicial object `Hom(U,V)`, formed degree by degree. -/
noncomputable def hom
    {C : Type w} [Category.{v} C] [HasFiniteProducts C]
    (U : CosimplicialObject (Type u)) (V : SimplicialObject C)
    (hU : FiniteNonemptyCosimplicialSet U) : SimplicialObject C where
  obj X := homObjectAt U V hU X.unop
  map := fun {X Y} f => homMapAt U V hU f.unop
  map_id := by
    sorry
  map_comp := by
    sorry

theorem hom_obj
    {C : Type w} [Category.{v} C] [HasFiniteProducts C]
    (U : CosimplicialObject (Type u)) (V : SimplicialObject C)
    (hU : FiniteNonemptyCosimplicialSet U) (n : ℕ) :
    (hom U V hU).obj (op (SimplexCategory.mk n)) = homObject U V hU n := rfl

theorem hom_map
    {C : Type w} [Category.{v} C] [HasFiniteProducts C]
    (U : CosimplicialObject (Type u)) (V : SimplicialObject C)
    (hU : FiniteNonemptyCosimplicialSet U) {m n : ℕ}
    (φ : SimplexCategory.mk m ⟶ SimplexCategory.mk n) :
    (hom U V hU).map φ.op = homMapAt U V hU φ := rfl

/-! ## The displayed `X`-valued-points formula -/

/--
The source's equality of hom-sets is the canonical product equivalence: a map
into the product is sent to its family of composites with the projections.
-/
noncomputable def homObjectHomEquiv
    {C : Type w} [Category.{v} C] [HasFiniteProducts C]
    (U : CosimplicialObject (Type u)) (V : SimplicialObject C)
    (hU : FiniteNonemptyCosimplicialSet U) (X : C) (n : ℕ) :
    (X ⟶ homObject U V hU n) ≃
      (U.obj (SimplexCategory.mk n) →
        (X ⟶ V.obj (op (SimplexCategory.mk n)))) := by
  letI : Finite (U.obj (SimplexCategory.mk n)) := (hU n).1
  change
    (X ⟶ ∏ᶜ fun _ : U.obj (SimplexCategory.mk n) =>
      V.obj (op (SimplexCategory.mk n))) ≃
      (U.obj (SimplexCategory.mk n) →
        (X ⟶ V.obj (op (SimplexCategory.mk n))))
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

/-- The projection from the chosen product to one coordinate. -/
noncomputable def homProjection
    {C : Type w} [Category.{v} C] [HasFiniteProducts C]
    (U : CosimplicialObject (Type u)) (V : SimplicialObject C)
    (hU : FiniteNonemptyCosimplicialSet U) (n : ℕ)
    (u : U.obj (SimplexCategory.mk n)) :
    homObject U V hU n ⟶ V.obj (op (SimplexCategory.mk n)) := by
  letI : Finite (U.obj (SimplexCategory.mk n)) := (hU n).1
  change
    (∏ᶜ fun _ : U.obj (SimplexCategory.mk n) =>
      V.obj (op (SimplexCategory.mk n))) ⟶
        V.obj (op (SimplexCategory.mk n))
  exact Pi.π _ u

/-- The coordinate form of the map in the finite-product construction. -/
theorem homMapAt_comp_projection
    {C : Type w} [Category.{v} C] [HasFiniteProducts C]
    (U : CosimplicialObject (Type u)) (V : SimplicialObject C)
    (hU : FiniteNonemptyCosimplicialSet U) {m n : ℕ}
    (φ : SimplexCategory.mk m ⟶ SimplexCategory.mk n)
    (u : U.obj (SimplexCategory.mk m)) :
    homMapAt U V hU φ ≫ homProjection U V hU m u =
      homProjection U V hU n (U.map φ u) ≫ V.map φ.op := by
  sorry

/-! ## Functoriality in the two variables -/

/-- The map induced by a cosimplicial map in the contravariant variable. -/
noncomputable def homPrecompApp
    {C : Type w} [Category.{v} C] [HasFiniteProducts C]
    {U U' : CosimplicialObject (Type u)}
    (f : U' ⟶ U) (V : SimplicialObject C)
    (hU : FiniteNonemptyCosimplicialSet U)
    (hU' : FiniteNonemptyCosimplicialSet U') (X : SimplexCategory) :
    (hom U V hU).obj (op X) ⟶ (hom U' V hU').obj (op X) := by
  letI : Finite (U.obj X) := by
    simpa only [SimplexCategory.mk_len] using (hU X.len).1
  letI : Finite (U'.obj X) := by
    simpa only [SimplexCategory.mk_len] using (hU' X.len).1
  change
    (∏ᶜ fun _ : U.obj X => V.obj (op X)) ⟶
      (∏ᶜ fun _ : U'.obj X => V.obj (op X))
  exact Pi.map' (f.app X) (fun _ => 𝟙 (V.obj (op X)))

/-- Precomposition makes `Hom(-,V)` contravariant in the cosimplicial set. -/
noncomputable def homPrecomp
    {C : Type w} [Category.{v} C] [HasFiniteProducts C]
    {U U' : CosimplicialObject (Type u)}
    (f : U' ⟶ U) (V : SimplicialObject C)
    (hU : FiniteNonemptyCosimplicialSet U)
    (hU' : FiniteNonemptyCosimplicialSet U') :
    hom U V hU ⟶ hom U' V hU' where
  app X := homPrecompApp f V hU hU' X.unop
  naturality := by
    sorry

/-- The map induced by a simplicial map in the covariant variable. -/
noncomputable def homPostcompApp
    {C : Type w} [Category.{v} C] [HasFiniteProducts C]
    (U : CosimplicialObject (Type u)) {V V' : SimplicialObject C}
    (f : V ⟶ V') (hU : FiniteNonemptyCosimplicialSet U)
    (X : SimplexCategory) :
    (hom U V hU).obj (op X) ⟶ (hom U V' hU).obj (op X) := by
  letI : Finite (U.obj X) := by
    simpa only [SimplexCategory.mk_len] using (hU X.len).1
  change
    (∏ᶜ fun _ : U.obj X => V.obj (op X)) ⟶
      (∏ᶜ fun _ : U.obj X => V'.obj (op X))
  exact CategoryTheory.Limits.Pi.map (fun _ => f.app (op X))

/-- Postcomposition makes `Hom(U,-)` covariant in the simplicial object. -/
noncomputable def homPostcomp
    {C : Type w} [Category.{v} C] [HasFiniteProducts C]
    (U : CosimplicialObject (Type u)) {V V' : SimplicialObject C}
    (f : V ⟶ V') (hU : FiniteNonemptyCosimplicialSet U) :
    hom U V hU ⟶ hom U V' hU where
  app X := homPostcompApp U f hU X.unop
  naturality := by
    sorry

/-!
The following laws record the functoriality asserted in the source.  Their
maps are the canonical product maps above; the proofs are deferred to the
proof stage.
-/

theorem homPrecomp_id
    {C : Type w} [Category.{v} C] [HasFiniteProducts C]
    {U : CosimplicialObject (Type u)} (V : SimplicialObject C)
    (hU : FiniteNonemptyCosimplicialSet U) :
    homPrecomp (𝟙 U) V hU hU = 𝟙 (hom U V hU) := by
  sorry

theorem homPrecomp_comp
    {C : Type w} [Category.{v} C] [HasFiniteProducts C]
    {U₁ U₂ U₃ : CosimplicialObject (Type u)}
    (f : U₁ ⟶ U₂) (g : U₂ ⟶ U₃) (V : SimplicialObject C)
    (h₁ : FiniteNonemptyCosimplicialSet U₁)
    (h₂ : FiniteNonemptyCosimplicialSet U₂)
    (h₃ : FiniteNonemptyCosimplicialSet U₃) :
    homPrecomp g V h₃ h₂ ≫ homPrecomp f V h₂ h₁ =
      homPrecomp (f ≫ g) V h₃ h₁ := by
  sorry

theorem homPostcomp_id
    {C : Type w} [Category.{v} C] [HasFiniteProducts C]
    (U : CosimplicialObject (Type u)) {V : SimplicialObject C}
    (hU : FiniteNonemptyCosimplicialSet U) :
    homPostcomp U (𝟙 V) hU = 𝟙 (hom U V hU) := by
  sorry

theorem homPostcomp_comp
    {C : Type w} [Category.{v} C] [HasFiniteProducts C]
    (U : CosimplicialObject (Type u)) {V V' V'' : SimplicialObject C}
    (f : V ⟶ V') (g : V' ⟶ V'')
    (hU : FiniteNonemptyCosimplicialSet U) :
    homPostcomp U f hU ≫ homPostcomp U g hU =
      homPostcomp U (f ≫ g) hU := by
  sorry

theorem homPrecomp_postcomp
    {C : Type w} [Category.{v} C] [HasFiniteProducts C]
    {U U' : CosimplicialObject (Type u)}
    {V V' : SimplicialObject C}
    (f : U' ⟶ U) (g : V ⟶ V')
    (hU : FiniteNonemptyCosimplicialSet U)
    (hU' : FiniteNonemptyCosimplicialSet U') :
    homPrecomp f V hU hU' ≫ homPostcomp U' g hU' =
      homPostcomp U g hU ≫ homPrecomp f V' hU hU' := by
  sorry

/-! ## The representable special case -/

/-- The exact self-product hypothesis needed for the representable example. -/
abbrev HasFiniteSelfProducts
    {C : Type w} [Category.{v} C] (X : C) : Prop :=
  ∀ (J : Type) [Finite J] [Nonempty J],
    HasLimit (Discrete.functor (fun _ : J => X))

/-- Every hom-set in `Δ` is nonempty, by a constant map. -/
instance simplexHom_nonempty (k : ℕ) (Y : SimplexCategory) :
    Nonempty (SimplexCategory.mk k ⟶ Y) :=
  ⟨SimplexCategory.const (SimplexCategory.mk k) Y 0⟩

/-- The product object in the special case, at an arbitrary simplex. -/
noncomputable def simplexHomProductObjectAt
    {C : Type w} [Category.{v} C] (X : C) (k : ℕ)
    (hX : HasFiniteSelfProducts X) (Y : SimplexCategory) : C := by
  letI := hX (SimplexCategory.mk k ⟶ Y)
  exact ∏ᶜ fun _ : (SimplexCategory.mk k ⟶ Y) => X

/-- The coordinate map in the special case. -/
noncomputable def simplexHomProductMapAt
    {C : Type w} [Category.{v} C] (X : C) (k : ℕ)
    (hX : HasFiniteSelfProducts X) {Y Z : SimplexCategory}
    (φ : Y ⟶ Z) :
    simplexHomProductObjectAt X k hX Z ⟶
      simplexHomProductObjectAt X k hX Y := by
  letI := hX (SimplexCategory.mk k ⟶ Y)
  letI := hX (SimplexCategory.mk k ⟶ Z)
  change
    (∏ᶜ fun _ : (SimplexCategory.mk k ⟶ Z) => X) ⟶
      (∏ᶜ fun _ : (SimplexCategory.mk k ⟶ Y) => X)
  exact Pi.map' (fun α => α ≫ φ) (fun _ => 𝟙 X)

/-- The special simplicial object with coordinates indexed by maps `[k] → [n]`. -/
noncomputable def simplexHomProduct
    {C : Type w} [Category.{v} C] (X : C) (k : ℕ)
    (hX : HasFiniteSelfProducts X) : SimplicialObject C where
  obj Y := simplexHomProductObjectAt X k hX Y.unop
  map := fun {Y Z} f => simplexHomProductMapAt X k hX f.unop
  map_id := by
    sorry
  map_comp := by
    sorry

theorem simplexHomProduct_obj
    {C : Type w} [Category.{v} C] (X : C) (k n : ℕ)
    (hX : HasFiniteSelfProducts X) :
    (simplexHomProduct X k hX).obj (op (SimplexCategory.mk n)) =
      simplexHomProductObjectAt X k hX (SimplexCategory.mk n) := rfl

theorem simplexHomProduct_map
    {C : Type w} [Category.{v} C] (X : C) (k : ℕ)
    (hX : HasFiniteSelfProducts X) {Y Z : SimplexCategory}
    (φ : Y ⟶ Z) :
    (simplexHomProduct X k hX).map φ.op =
      simplexHomProductMapAt X k hX φ := rfl

/-- The projection from the special product to one coordinate. -/
noncomputable def simplexHomProductProjection
    {C : Type w} [Category.{v} C] (X : C) (k n : ℕ)
    (hX : HasFiniteSelfProducts X)
    (α : SimplexCategory.mk k ⟶ SimplexCategory.mk n) :
    (simplexHomProduct X k hX).obj (op (SimplexCategory.mk n)) ⟶ X := by
  letI := hX (SimplexCategory.mk k ⟶ SimplexCategory.mk n)
  change
    (∏ᶜ fun _ : (SimplexCategory.mk k ⟶ SimplexCategory.mk n) => X) ⟶ X
  exact Pi.π _ α

/-- The coordinate formula for the maps of the special simplicial object. -/
theorem simplexHomProduct_map_projection
    {C : Type w} [Category.{v} C] (X : C) (k : ℕ)
    (hX : HasFiniteSelfProducts X) {m n : ℕ}
    (φ : SimplexCategory.mk m ⟶ SimplexCategory.mk n)
    (α : SimplexCategory.mk k ⟶ SimplexCategory.mk m) :
    simplexHomProductMapAt X k hX φ ≫
        simplexHomProductProjection X k m hX α =
      simplexHomProductProjection X k n hX (α ≫ φ) ≫ 𝟙 X := by
  sorry

/-- Maps into the special product are determined by the identity coordinate. -/
noncomputable def simplexHomProduct_hom_equiv
    {C : Type w} [Category.{v} C] (X : C) (k : ℕ)
    (hX : HasFiniteSelfProducts X) (V : SimplicialObject C) :
    (V ⟶ simplexHomProduct X k hX) ≃
      (V.obj (op (SimplexCategory.mk k)) ⟶ X) where
  toFun γ := by
    letI := hX (SimplexCategory.mk k ⟶ SimplexCategory.mk k)
    exact γ.app (op (SimplexCategory.mk k)) ≫
      Pi.π (fun _ : (SimplexCategory.mk k ⟶ SimplexCategory.mk k) => X)
        (𝟙 (SimplexCategory.mk k))
  invFun f :=
    { app := fun Y => by
        letI := hX (SimplexCategory.mk k ⟶ Y.unop)
        exact Pi.lift (fun α => V.map α.op ≫ f)
      naturality := by
        sorry }
  left_inv := by
    sorry
  right_inv := by
    sorry

/-- The truncated version of the identity-coordinate equivalence. -/
noncomputable def simplexHomProduct_truncated_hom_equiv
    {C : Type w} [Category.{v} C] (X : C) (k : ℕ)
    (hX : HasFiniteSelfProducts X)
    (W : SimplicialObject.Truncated C k) :
    (W ⟶ (SimplicialObject.truncation (C := C) k).obj
      (simplexHomProduct X k hX)) ≃
      (W.obj (op (⟨SimplexCategory.mk k, le_rfl⟩ :
        SimplexCategory.Truncated k)) ⟶ X) where
  toFun γ := by
    letI := hX (SimplexCategory.mk k ⟶ SimplexCategory.mk k)
    exact γ.app (op (⟨SimplexCategory.mk k, le_rfl⟩ :
        SimplexCategory.Truncated k)) ≫
      Pi.π (fun _ : (SimplexCategory.mk k ⟶ SimplexCategory.mk k) => X)
        (𝟙 (SimplexCategory.mk k))
  invFun f :=
    { app := fun Y => by
        letI := hX (SimplexCategory.mk k ⟶ Y.unop.obj)
        exact Pi.lift (fun α =>
          W.map (SimplexCategory.Truncated.Hom.tr α
            (by simp) Y.unop.property).op ≫ f)
      naturality := by
        sorry }
  left_inv := by
    sorry
  right_inv := by
    sorry

/-! ## Identification with the source's `C[k]` notation -/

theorem simplex_cosimplicial_set_finite_nonempty (k : ℕ) :
    FiniteNonemptyCosimplicialSet
      (Formalization.Books.Simplicial.Unit05.simplex_cosimplicial_set k) := by
  intro n
  refine ⟨?_, ?_⟩
  · rw [Formalization.Books.Simplicial.Unit05.simplex_cosimplicial_set_obj]
    infer_instance
  · rw [Formalization.Books.Simplicial.Unit05.simplex_cosimplicial_set_obj]
    exact ⟨SimplexCategory.const (SimplexCategory.mk k)
      (SimplexCategory.mk n) 0⟩

/-- The special product is the source's `Hom(C[k],X)`, up to the canonical
isomorphism between choices of the same finite products. -/
theorem simplexHomProduct_is_hom
    {C : Type w} [Category.{v} C] [HasFiniteProducts C]
    (X : C) (k : ℕ) (hX : HasFiniteSelfProducts X) :
    Nonempty
      (simplexHomProduct X k hX ≅
        hom
          (Formalization.Books.Simplicial.Unit05.simplex_cosimplicial_set k)
          ((SimplicialObject.const C).obj X)
          (simplex_cosimplicial_set_finite_nonempty k)) := by
  sorry

end Formalization.Books.Simplicial.Unit15
