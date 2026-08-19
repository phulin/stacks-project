import Formalization.Books.Simplicial.Unit12.TruncatedSimplicialObjects
import Formalization.Books.Simplicial.Unit11.SimplicialSets
import Formalization.Books.Categories.Unit05.CoproductsOfPairs
import Mathlib.CategoryTheory.Yoneda
import Mathlib.CategoryTheory.Limits.Constructions.FiniteProductsOfBinaryProducts
import Mathlib.CategoryTheory.Limits.Shapes.FiniteProducts

/-!
# Simplicial Methods, Chapter 13: Products with simplicial sets

The source forms a simplicial object with a simplicial set by taking a
degreewise coproduct of copies of the given object.  Mathlib's canonical
interface for these coproducts is `HasCoproduct` and its `Sigma` API.  The
construction below keeps the source's finite-nonempty hypothesis (so that
binary coproducts suffice) and also exposes the more general version in which
the displayed degreewise coproducts are supplied directly.
-/

namespace Formalization.Books.Simplicial.Unit13

open CategoryTheory
open CategoryTheory.Limits
open Opposite
open scoped _root_.Simplicial

universe v u w

/-! ## The hypotheses and the degreewise coproducts -/

private theorem hasCoproduct_fin_succ {C : Type u} [Category.{v} C]
    [HasBinaryCoproducts C] :
    ∀ (n : ℕ) (f : Fin (n + 1) → C), HasCoproduct f
  | 0, f =>
      HasColimit.mk ⟨Cofan.mk (f 0)
          (fun j => eqToHom (congrArg f (Fin.eq_zero j))),
        Cofan.IsColimit.mk _ (fun s => s.inj 0)
          (fun s j => by
            have hj : j = 0 := Fin.eq_zero j
            subst hj
            simp)
          (fun s m hm => by simpa using hm 0)⟩
  | n + 1, f =>
      let _ := hasCoproduct_fin_succ n (fun i : Fin (n + 1) => f i.succ)
      HasColimit.mk ⟨_, extendCofanIsColimit f (colimit.isColimit _) (colimit.isColimit _)⟩

/-- Every degree of `U` is finite and nonempty. -/
abbrev FiniteNonemptySimplicialSet (U : SSet.{w}) : Prop :=
  ∀ n : ℕ, Finite (U _⦋n⦌) ∧ Nonempty (U _⦋n⦌)

/-- The displayed degreewise coproducts needed for the direct construction. -/
abbrev HasDegreewiseCoproducts
    {C : Type u} [Category.{v} C]
    (U : SSet.{w}) (V : SimplicialObject C) : Prop :=
  ∀ n : ℕ,
    HasCoproduct (fun _ : U _⦋n⦌ => V.obj (op (SimplexCategory.mk n)))

/--
Binary coproducts give coproducts indexed by every finite nonempty type.  This
is the only bridge needed to pass from the source's categorical hypothesis to
the family of coproduct instances used below.
-/
theorem hasCoproduct_of_finite_nonempty_of_hasBinaryCoproducts
    {C : Type u} [Category.{v} C] [HasBinaryCoproducts C]
    {J : Type w} [Finite J] [Nonempty J] (F : J → C) :
    HasCoproduct F := by
  rcases Finite.exists_equiv_fin J with ⟨n, ⟨e⟩⟩
  have hn : n ≠ 0 := by
    intro hn
    let j : J := Classical.choice (inferInstance : Nonempty J)
    exact Fin.elim0 (hn ▸ e j)
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
  let _ := hasCoproduct_fin_succ k (fun i : Fin (k + 1) => F (e.symm i))
  exact hasCoproduct_of_equiv_of_iso (fun i : Fin (k + 1) => F (e.symm i)) F e
    (fun x => by simpa using (Iso.refl (F x)))

theorem degreewiseCoproductInstance
    {C : Type u} [Category.{v} C] [HasBinaryCoproducts C]
    (U : SSet.{w}) (V : SimplicialObject C)
    (hU : FiniteNonemptySimplicialSet U) (n : ℕ) :
    HasCoproduct (fun _ : U _⦋n⦌ => V.obj (op (SimplexCategory.mk n))) := by
  let _ : Finite (U _⦋n⦌) := (hU n).1
  let _ : Nonempty (U _⦋n⦌) := (hU n).2
  exact hasCoproduct_of_finite_nonempty_of_hasBinaryCoproducts
    (fun _ : U _⦋n⦌ => V.obj (op (SimplexCategory.mk n)))

theorem degreewiseCoproductInstanceAt
    {C : Type u} [Category.{v} C]
    {U : SSet.{w}} {V : SimplicialObject C}
    (h : HasDegreewiseCoproducts U V) (X : SimplexCategoryᵒᵖ) :
    HasCoproduct (fun _ : U.obj X => V.obj X) := by
  simpa only [SimplexCategory.mk_len] using h X.unop.len

/-- The chosen degree-`n` coproduct in the direct construction. -/
noncomputable def degreewiseSimplicialSetProduct
    {C : Type u} [Category.{v} C]
    (U : SSet.{w}) (V : SimplicialObject C)
    (h : HasDegreewiseCoproducts U V) (n : ℕ) : C :=
  letI := h n
  ∐ (fun _ : U _⦋n⦌ => V.obj (op (SimplexCategory.mk n)))

/-!
The source's direct construction.  Its map sends the component indexed by
`u` to the component indexed by `U.map f u`, using the map of `V`.
-/
noncomputable def simplicialSetProductOf
    {C : Type u} [Category.{v} C]
    (U : SSet.{w}) (V : SimplicialObject C)
    (h : HasDegreewiseCoproducts U V) : SimplicialObject C :=
  { obj := fun X =>
      let _ : HasCoproduct (fun _ : U.obj X => V.obj X) :=
        degreewiseCoproductInstanceAt h X
      ∐ (fun _ : U.obj X => V.obj X)
    map := fun {X Y} f =>
      let _ : HasCoproduct (fun _ : U.obj X => V.obj X) :=
        degreewiseCoproductInstanceAt h X
      let _ : HasCoproduct (fun _ : U.obj Y => V.obj Y) :=
        degreewiseCoproductInstanceAt h Y
      Sigma.desc (fun u =>
        V.map f ≫ Sigma.ι (fun _ : U.obj Y => V.obj Y) (U.map f u))
    map_id := by
      intro X
      let _ : HasCoproduct (fun _ : U.obj X => V.obj X) :=
        degreewiseCoproductInstanceAt h X
      change Sigma.desc (fun u =>
          V.map (𝟙 X) ≫ Sigma.ι (fun _ : U.obj X => V.obj X)
            (U.map (𝟙 X) u)) = 𝟙 _
      rw [U.map_id, V.map_id]
      apply Sigma.hom_ext
      intro u
      simp
    map_comp := by
      intro X Y Z f g
      let _ : HasCoproduct (fun _ : U.obj X => V.obj X) :=
        degreewiseCoproductInstanceAt h X
      let _ : HasCoproduct (fun _ : U.obj Y => V.obj Y) :=
        degreewiseCoproductInstanceAt h Y
      let _ : HasCoproduct (fun _ : U.obj Z => V.obj Z) :=
        degreewiseCoproductInstanceAt h Z
      change Sigma.desc (fun u =>
          V.map (f ≫ g) ≫ Sigma.ι (fun _ : U.obj Z => V.obj Z)
            (U.map (f ≫ g) u)) =
        Sigma.desc (fun u =>
            V.map f ≫ Sigma.ι (fun _ : U.obj Y => V.obj Y) (U.map f u)) ≫
          Sigma.desc (fun u =>
            V.map g ≫ Sigma.ι (fun _ : U.obj Z => V.obj Z) (U.map g u))
      rw [U.map_comp, V.map_comp]
      apply Sigma.hom_ext
      intro u
      simp [Category.assoc]
  }

/-! The finite-nonempty version stated in the source. -/

noncomputable def simplicialSetProduct
    {C : Type u} [Category.{v} C] [HasBinaryCoproducts C]
    (U : SSet.{w}) (V : SimplicialObject C)
    (hU : FiniteNonemptySimplicialSet U) : SimplicialObject C :=
  simplicialSetProductOf U V (degreewiseCoproductInstance U V hU)

theorem simplicialSetProduct_obj
    {C : Type u} [Category.{v} C]
    {U : SSet.{w}} {V : SimplicialObject C}
    (h : HasDegreewiseCoproducts U V) (n : ℕ) :
    (simplicialSetProductOf U V h).obj (op (SimplexCategory.mk n)) =
      degreewiseSimplicialSetProduct U V h n := by
  rfl

theorem simplicialSetProduct_map
    {C : Type u} [Category.{v} C]
    {U : SSet.{w}} {V : SimplicialObject C}
    (h : HasDegreewiseCoproducts U V)
    {m n : ℕ} (φ : SimplexCategory.mk m ⟶ SimplexCategory.mk n) :
    (simplicialSetProductOf U V h).map φ.op =
      letI := h n
      letI := h m
      Sigma.desc (fun u =>
        V.map φ.op ≫
          Sigma.ι (fun _ : U _⦋m⦌ => V.obj (op (SimplexCategory.mk m)))
            (U.map φ.op u)) := by
  rfl

/-! ## The displayed functor of compatible families -/

/-- A family of maps satisfying the compatibility equation in the source. -/
def CompatibleFamily
    {C : Type u} [Category.{v} C]
    (U : SSet.{w}) (V W : SimplicialObject C) : Type (max v w) :=
  {f : ∀ n : ℕ, U _⦋n⦌ →
      (V.obj (op (SimplexCategory.mk n)) ⟶
        W.obj (op (SimplexCategory.mk n))) //
    ∀ {m n : ℕ} (φ : SimplexCategory.mk m ⟶ SimplexCategory.mk n)
      (u : U _⦋n⦌),
      V.map φ.op ≫ f m (U.map φ.op u) =
        f n u ≫ W.map φ.op }

abbrev productWithSimplicialSetHomSet
    {C : Type u} [Category.{v} C]
    (U : SSet.{w}) (V W : SimplicialObject C) :
    Set (∀ n : ℕ, U _⦋n⦌ →
      (V.obj (op (SimplexCategory.mk n)) ⟶
        W.obj (op (SimplexCategory.mk n)))) :=
  {f | ∀ {m n : ℕ} (φ : SimplexCategory.mk m ⟶ SimplexCategory.mk n)
      (u : U _⦋n⦌),
      V.map φ.op ≫ f m (U.map φ.op u) =
        f n u ≫ W.map φ.op}

noncomputable def compatibleFamilyMap
    {C : Type u} [Category.{v} C]
    (U : SSet.{w}) {V W W' : SimplicialObject C}
    (f : CompatibleFamily U V W) (g : W ⟶ W') :
    CompatibleFamily U V W' := by
  refine ⟨fun n u => f.1 n u ≫ g.app (op (SimplexCategory.mk n)), ?_⟩
  intro m n φ u
  simp only [Category.assoc]
  rw [← Category.assoc, f.property φ u, Category.assoc, g.naturality]

/-- The source's covariant functor of compatible families. -/
noncomputable def productWithSimplicialSetHomFunctor
    {C : Type u} [Category.{v} C]
    (U : SSet.{w}) (V : SimplicialObject C) :
    SimplicialObject C ⥤ Type (max v w) where
  obj W := CompatibleFamily U V W
  map g := TypeCat.ofHom (fun f => compatibleFamilyMap U (V := V) f g)
  map_id := by
    intro W
    ext f
    apply Subtype.ext
    funext n u
    change f.1 n u ≫ 𝟙 (W.obj (op (SimplexCategory.mk n))) = f.1 n u
    simp
  map_comp := by
    intro W W' W'' f g
    ext x
    apply Subtype.ext
    funext n u
    change
      x.1 n u ≫ (f ≫ g).app (op (SimplexCategory.mk n)) =
        (x.1 n u ≫ f.app (op (SimplexCategory.mk n))) ≫
          g.app (op (SimplexCategory.mk n))
    rw [NatTrans.comp_app]
    simp [Category.assoc]

def compatibleFamilyEquivHomSet
    {C : Type u} [Category.{v} C]
    (U : SSet.{w}) (V W : SimplicialObject C) :
    CompatibleFamily U V W ≃ productWithSimplicialSetHomSet U V W :=
  Equiv.refl _

/-! ## The representability lemma -/

/-- The direct product represents the compatible-family functor. -/
noncomputable def simplicialSetProduct_hom_equiv
    {C : Type u} [Category.{v} C]
    {U : SSet.{w}} {V : SimplicialObject C}
    (h : HasDegreewiseCoproducts U V) (W : SimplicialObject C) :
    (simplicialSetProductOf U V h ⟶ W) ≃ CompatibleFamily U V W :=
  { toFun := fun γ =>
      ⟨fun n u =>
          let _ := h n
          Sigma.ι (fun _ : U _⦋n⦌ => V.obj (op (SimplexCategory.mk n))) u ≫
            γ.app (op (SimplexCategory.mk n)),
        by
          intro m n φ u
          simpa [Category.assoc, simplicialSetProductOf] using
            congrArg
              (fun k =>
                let _ := h n
                Sigma.ι (fun _ : U _⦋n⦌ => V.obj (op (SimplexCategory.mk n))) u ≫ k)
              (γ.naturality φ.op)⟩
    invFun := fun f =>
      { app := fun X =>
          let _ : HasCoproduct (fun _ : U.obj X => V.obj X) :=
            degreewiseCoproductInstanceAt h X
          Sigma.desc (fun u => f.1 X.unop.len u)
        naturality := by
          intro X Y g
          apply Sigma.hom_ext
          intro u
          simpa [simplicialSetProductOf, Category.assoc] using
            f.property g.unop u }
    left_inv := by
      intro γ
      apply NatTrans.ext
      funext X
      apply Sigma.hom_ext
      intro u
      simp [simplicialSetProductOf, Category.assoc]
    right_inv := by
      intro f
      apply Subtype.ext
      funext n u
      simp [simplicialSetProductOf, Category.assoc] }

theorem exists_simplicialSetProduct_hom_equiv
    {C : Type u} [Category.{v} C]
    {U : SSet.{w}} {V : SimplicialObject C}
    (h : HasDegreewiseCoproducts U V) (W : SimplicialObject C) :
    Nonempty ((simplicialSetProductOf U V h ⟶ W) ≃ CompatibleFamily U V W) :=
  ⟨simplicialSetProduct_hom_equiv h W⟩

noncomputable def finiteSimplicialSetProduct_hom_equiv
    {C : Type u} [Category.{v} C] [HasBinaryCoproducts C]
    (U : SSet.{w}) (V : SimplicialObject C)
    (hU : FiniteNonemptySimplicialSet U) (W : SimplicialObject C) :
    (simplicialSetProduct U V hU ⟶ W) ≃ CompatibleFamily U V W :=
  simplicialSetProduct_hom_equiv (degreewiseCoproductInstance U V hU) W

/-! The pointwise equivalences assemble to the functorial representability
statement from the source.  The `ULift` is only the standard universe lift
needed to compare the hom functor with the family type when the simplicial
set has elements in a larger universe. -/

theorem exists_simplicialSetProduct_hom_natIso
    {C : Type u} [Category.{v} C]
    {U : SSet.{w}} {V : SimplicialObject C}
    (h : HasDegreewiseCoproducts U V) :
    Nonempty
      (uliftCoyoneda.{w}.obj (op (simplicialSetProductOf U V h)) ≅
        productWithSimplicialSetHomFunctor U V) := by
  sorry

noncomputable def simplicialSetProduct_hom_natIso
    {C : Type u} [Category.{v} C]
    {U : SSet.{w}} {V : SimplicialObject C}
    (h : HasDegreewiseCoproducts U V) :
    uliftCoyoneda.{w}.obj (op (simplicialSetProductOf U V h)) ≅
      productWithSimplicialSetHomFunctor U V :=
  (exists_simplicialSetProduct_hom_natIso h).some

/-! ## The FSSets functor and the canonical map back to `V` -/

/-- The full subcategory of simplicial sets finite and nonempty in every degree. -/
def FSSets : Type (w + 1) :=
  ObjectProperty.FullSubcategory
    (fun U : SSet.{w} => FiniteNonemptySimplicialSet U)

instance fSSetsCategory : Category (FSSets.{w}) :=
  ObjectProperty.FullSubcategory.category _

/-! The maps on morphisms in the two variables are again degreewise
coproduct descents.  The proof that these components are natural is
propositional and is left for the proof stage, while the construction itself
is explicit. -/

noncomputable def productWithSimplicialSetMap
    {C : Type u} [Category.{v} C] [HasBinaryCoproducts C]
    {U U' : FSSets.{w}} {V V' : SimplicialObject C}
    (f : U ⟶ U') (g : V ⟶ V') :
    simplicialSetProduct U.obj V U.property ⟶
      simplicialSetProduct U'.obj V' U'.property :=
  { app := fun X =>
      let hUV : HasDegreewiseCoproducts U.obj V :=
        degreewiseCoproductInstance U.obj V U.property
      let hU'V' : HasDegreewiseCoproducts U'.obj V' :=
        degreewiseCoproductInstance U'.obj V' U'.property
      let _ : HasCoproduct (fun _ : U.obj.obj X => V.obj X) :=
        degreewiseCoproductInstanceAt hUV X
      let _ : HasCoproduct (fun _ : U'.obj.obj X => V'.obj X) :=
        degreewiseCoproductInstanceAt hU'V' X
      Sigma.desc (fun u =>
        g.app X ≫ Sigma.ι (fun _ : U'.obj.obj X => V'.obj X)
          (f.hom.app X u))
    naturality := by
      sorry }

/-! The source's rule `(U, V) ↦ U × V` is now given as an actual functor.
The two functor laws are proposition-valued interfaces for the proof stage. -/

noncomputable def productWithSimplicialSetBifunctor
    {C : Type u} [Category.{v} C] [HasBinaryCoproducts C] :
    FSSets.{w} × SimplicialObject C ⥤ SimplicialObject C :=
  { obj := fun Z => simplicialSetProduct Z.1.obj Z.2 Z.1.property
    map := fun f => productWithSimplicialSetMap f.1 f.2
    map_id := by
      sorry
    map_comp := by
      sorry }

theorem exists_productWithSimplicialSetFunctor
    {C : Type u} [Category.{v} C] [HasBinaryCoproducts C] :
    Nonempty (FSSets.{w} × SimplicialObject C ⥤ SimplicialObject C) :=
  ⟨productWithSimplicialSetBifunctor⟩

/-- The canonical map which is the identity on each coproduct component. -/
noncomputable def productWithSimplicialSetTo
    {C : Type u} [Category.{v} C]
    {U : SSet.{w}} {V : SimplicialObject C}
    (h : HasDegreewiseCoproducts U V) :
    simplicialSetProductOf U V h ⟶ V :=
  { app := fun X =>
      let _ : HasCoproduct (fun _ : U.obj X => V.obj X) :=
        degreewiseCoproductInstanceAt h X
      Sigma.desc (fun _ => 𝟙 (V.obj X))
    naturality := by
      intro X Y f
      let _ : HasCoproduct (fun _ : U.obj X => V.obj X) :=
        degreewiseCoproductInstanceAt h X
      let _ : HasCoproduct (fun _ : U.obj Y => V.obj Y) :=
        degreewiseCoproductInstanceAt h Y
      change
        Sigma.desc (fun u =>
            V.map f ≫ Sigma.ι (fun _ : U.obj Y => V.obj Y) (U.map f u)) ≫
          Sigma.desc (fun _ => 𝟙 (V.obj Y)) =
        Sigma.desc (fun _ => 𝟙 (V.obj X)) ≫ V.map f
      apply Sigma.hom_ext
      intro u
      simp [Category.assoc] }

theorem productWithSimplicialSetTo_app
    {C : Type u} [Category.{v} C]
    {U : SSet.{w}} {V : SimplicialObject C}
    (h : HasDegreewiseCoproducts U V) (X : SimplexCategoryᵒᵖ) :
    (productWithSimplicialSetTo h).app X =
      letI := degreewiseCoproductInstanceAt h X
      Sigma.desc (fun _ => 𝟙 (V.obj X)) := by
  rfl

/-! ## The standard simplex special case -/

theorem standardSimplex_finite_nonempty (k : ℕ) :
    FiniteNonemptySimplicialSet (Δ[k] : SSet.{w}) := by
  intro n
  let e := SSet.stdSimplex.objEquiv
    (n := SimplexCategory.mk k) (m := op (SimplexCategory.mk n))
  refine ⟨Finite.of_injective e e.injective, ?_⟩
  exact ⟨e.symm (SimplexCategory.const (SimplexCategory.mk n)
    (SimplexCategory.mk k) 0)⟩

/-- The product of a constant object with a standard simplex. -/
noncomputable def constantObjectProductWithSimplex
    {C : Type u} [Category.{v} C] [HasBinaryCoproducts C]
    (X : C) (k : ℕ) : SimplicialObject C :=
  simplicialSetProduct (Δ[k] : SSet.{w})
    ((SimplicialObject.const C).obj X) (standardSimplex_finite_nonempty k)

/-! The source's canonical maps from this product. -/

/-- The same special product when its displayed degreewise coproducts are
supplied directly, without assuming all binary coproducts in `C`. -/
noncomputable def constantObjectProductWithSimplexOf
    {C : Type u} [Category.{v} C]
    (X : C) (k : ℕ)
    (h : HasDegreewiseCoproducts (Δ[k] : SSet.{w})
      ((SimplicialObject.const C).obj X)) : SimplicialObject C :=
  simplicialSetProductOf (Δ[k] : SSet.{w})
    ((SimplicialObject.const C).obj X) h

noncomputable def constantObjectProductWithSimplexOf_hom_equiv
    {C : Type u} [Category.{v} C]
    (X : C) (k : ℕ)
    (h : HasDegreewiseCoproducts (Δ[k] : SSet.{w})
      ((SimplicialObject.const C).obj X)) (V : SimplicialObject C) :
    (constantObjectProductWithSimplexOf X k h ⟶ V) ≃
      (X ⟶ V.obj (op (SimplexCategory.mk k))) where
  toFun γ :=
    (simplicialSetProduct_hom_equiv h V γ).1 k
      (SSet.stdSimplex.objEquiv.symm (𝟙 (SimplexCategory.mk k)))
  invFun f :=
    (simplicialSetProduct_hom_equiv h V).symm
      ⟨fun n α =>
        f ≫ V.map (SSet.stdSimplex.objEquiv α).op, by
        sorry⟩
  left_inv := by
    sorry
  right_inv := by
    sorry

theorem exists_constantObjectProductWithSimplexOf_hom_equiv
    {C : Type u} [Category.{v} C]
    (X : C) (k : ℕ)
    (h : HasDegreewiseCoproducts (Δ[k] : SSet.{w})
      ((SimplicialObject.const C).obj X)) (V : SimplicialObject C) :
    Nonempty ((constantObjectProductWithSimplexOf X k h ⟶ V) ≃
      (X ⟶ V.obj (op (SimplexCategory.mk k)))) :=
  ⟨constantObjectProductWithSimplexOf_hom_equiv X k h V⟩

theorem exists_constantObjectProductWithSimplexOf_truncated_hom_equiv
    {C : Type u} [Category.{v} C]
    (X : C) (k n : ℕ) (hkn : k ≤ n)
    (h : HasDegreewiseCoproducts (Δ[k] : SSet.{w})
      ((SimplicialObject.const C).obj X))
    (W : SimplicialObject.Truncated C n) :
    Nonempty (((SimplicialObject.truncation (C := C) n).obj
        (constantObjectProductWithSimplexOf X k h) ⟶ W) ≃
      (X ⟶ W.obj (op (⟨SimplexCategory.mk k, hkn⟩ :
        SimplexCategory.Truncated n)))) := by
  sorry

noncomputable def constantObjectProductWithSimplexOf_truncated_hom_equiv
    {C : Type u} [Category.{v} C]
    (X : C) (k n : ℕ) (hkn : k ≤ n)
    (h : HasDegreewiseCoproducts (Δ[k] : SSet.{w})
      ((SimplicialObject.const C).obj X))
    (W : SimplicialObject.Truncated C n) :
    ((SimplicialObject.truncation (C := C) n).obj
        (constantObjectProductWithSimplexOf X k h) ⟶ W) ≃
      (X ⟶ W.obj (op (⟨SimplexCategory.mk k, hkn⟩ :
        SimplexCategory.Truncated n))) :=
  (exists_constantObjectProductWithSimplexOf_truncated_hom_equiv
    X k n hkn h W).some

noncomputable def constantObjectProductWithSimplex_hom_equiv
    {C : Type u} [Category.{v} C] [HasBinaryCoproducts C]
    (X : C) (k : ℕ) (V : SimplicialObject C) :
    (constantObjectProductWithSimplex X k ⟶ V) ≃
      (X ⟶ V.obj (op (SimplexCategory.mk k))) :=
  constantObjectProductWithSimplexOf_hom_equiv X k
    (degreewiseCoproductInstance (Δ[k] : SSet.{w})
      ((SimplicialObject.const C).obj X)
      (standardSimplex_finite_nonempty k)) V

theorem exists_constantObjectProductWithSimplex_hom_equiv
    {C : Type u} [Category.{v} C] [HasBinaryCoproducts C]
    (X : C) (k : ℕ) (V : SimplicialObject C) :
    Nonempty ((constantObjectProductWithSimplex X k ⟶ V) ≃
      (X ⟶ V.obj (op (SimplexCategory.mk k)))) :=
  ⟨constantObjectProductWithSimplex_hom_equiv X k V⟩

theorem exists_constantObjectProductWithSimplex_truncated_hom_equiv
    {C : Type u} [Category.{v} C] [HasBinaryCoproducts C]
    (X : C) (k n : ℕ) (hkn : k ≤ n)
    (W : SimplicialObject.Truncated C n) :
    Nonempty (((SimplicialObject.truncation (C := C) n).obj
        (constantObjectProductWithSimplex X k) ⟶ W) ≃
      (X ⟶ W.obj (op (⟨SimplexCategory.mk k, hkn⟩ :
        SimplexCategory.Truncated n)))) := by
  sorry

noncomputable def constantObjectProductWithSimplex_truncated_hom_equiv
    {C : Type u} [Category.{v} C] [HasBinaryCoproducts C]
    (X : C) (k n : ℕ) (hkn : k ≤ n)
    (W : SimplicialObject.Truncated C n) :
    ((SimplicialObject.truncation (C := C) n).obj
        (constantObjectProductWithSimplex X k) ⟶ W) ≃
      (X ⟶ W.obj (op (⟨SimplexCategory.mk k, hkn⟩ :
        SimplexCategory.Truncated n))) :=
  (exists_constantObjectProductWithSimplex_truncated_hom_equiv
    X k n hkn W).some

noncomputable def constant_simplicial_object_hom_equiv
    {C : Type u} [Category.{v} C]
    (X : C) (V : SimplicialObject C) :
    (((SimplicialObject.const C).obj X) ⟶ V) ≃
      (X ⟶ V.obj (op (SimplexCategory.mk 0))) where
  toFun γ := γ.app (op (SimplexCategory.mk 0))
  invFun f :=
    { app := fun Y =>
        f ≫ V.map (SimplexCategory.const Y.unop
          (SimplexCategory.mk 0) 0).op
      naturality := by
        sorry }
  left_inv := by
    sorry
  right_inv := by
    sorry

theorem exists_constant_simplicial_object_hom_equiv
    {C : Type u} [Category.{v} C]
    (X : C) (V : SimplicialObject C) :
    Nonempty ((((SimplicialObject.const C).obj X) ⟶ V) ≃
      (X ⟶ V.obj (op (SimplexCategory.mk 0)))) :=
  ⟨constant_simplicial_object_hom_equiv X V⟩

end Formalization.Books.Simplicial.Unit13
