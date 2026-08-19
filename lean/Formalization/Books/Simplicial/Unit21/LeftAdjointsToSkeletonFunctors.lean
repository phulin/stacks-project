import Formalization.Books.Simplicial.Unit14.HomFromSimplicialSetsIntoCosimplicialObjects
import Formalization.Books.Simplicial.Unit18.SplittingSimplicialObjects
import Formalization.Books.Simplicial.Unit19.CoskeletonFunctors
import Mathlib.AlgebraicTopology.SimplicialSet.Boundary
import Mathlib.AlgebraicTopology.SimplicialSet.Finite
import Mathlib.CategoryTheory.Functor.KanExtension.Adjunction
import Mathlib.CategoryTheory.Limits.Shapes.FiniteLimits
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-!
# Simplicial Methods, Chapter 21: Left adjoints to the skeleton functors

The source's `iₙ!` is Mathlib's left Kan extension along the inclusion of the
truncated simplex category.  The declarations below retain the source's
pointwise colimit indexing, while using `CostructuredArrow`, `SSet.boundary`,
and the earlier skeleton and degreewise-coproduct interfaces.
-/

namespace Formalization.Books.Simplicial.Unit21

open CategoryTheory
open CategoryTheory.Limits
open Opposite
open scoped _root_.Simplicial
open scoped ZeroObject

universe v u w

/-! ## The left Kan extension and its indexing category -/

/-- The inclusion used for the left Kan extension defining `iₘ!`. -/
abbrev leftSkeletonInclusion (m : ℕ) :
    (SimplexCategory.Truncated m)ᵒᵖ ⥤ SimplexCategoryᵒᵖ :=
  (SimplexCategory.Truncated.inclusion m).op

/-- Existence of the left Kan extension for every `m`-truncated object. -/
abbrev HasLeftSkeletonFunctor
    (C : Type u) [Category.{v} C] (m : ℕ) : Prop :=
  ∀ U : SimplicialObject.Truncated C m,
    (leftSkeletonInclusion m).HasLeftKanExtension U

private noncomputable instance leftSkeletonIndexFinCategory (m : ℕ) (X : SimplexCategoryᵒᵖ) :
    FinCategory (CostructuredArrow (leftSkeletonInclusion m) X) := by
  letI : Finite (SimplexCategory.Truncated m) := by
    let f : SimplexCategory.Truncated m → Fin (m + 1) :=
      fun X => ⟨X.obj.len, Nat.lt_succ_of_le X.property⟩
    apply Finite.of_injective f
    intro X Y h
    cases X with
    | mk X hX =>
      cases Y with
      | mk Y hY =>
        apply ObjectProperty.FullSubcategory.ext
        exact SimplexCategory.ext (congrArg Fin.val h)
  letI : Finite ((SimplexCategory.Truncated m)ᵒᵖ) := by
    apply Finite.of_injective (fun X => X.unop)
    intro X Y h
    exact congrArg op h
  letI : ∀ a b : (SimplexCategory.Truncated m)ᵒᵖ, Finite (a ⟶ b) := fun a b => by
    apply Finite.of_injective (fun f => f.unop.hom)
    intro f g h
    apply Quiver.Hom.unop_inj
    apply ObjectProperty.hom_ext
    exact h
  letI : ∀ a : (SimplexCategory.Truncated m)ᵒᵖ,
      Finite ((leftSkeletonInclusion m).obj a ⟶ X) := fun a => by
    apply Finite.of_injective (fun f => f.unop)
    intro f g h
    exact Quiver.Hom.unop_inj h
  letI : Finite (CostructuredArrow (leftSkeletonInclusion m) X) := by
    let f : CostructuredArrow (leftSkeletonInclusion m) X →
        Σ a : (SimplexCategory.Truncated m)ᵒᵖ,
          (leftSkeletonInclusion m).obj a ⟶ X :=
      fun A => ⟨A.left, A.hom⟩
    apply Finite.of_injective f
    intro X Y h
    apply Comma.ext
    · exact congrArg Sigma.fst h
    · exact Subsingleton.elim _ _
    · cases X
      cases Y
      cases h
      rfl
  letI : ∀ a b : CostructuredArrow (leftSkeletonInclusion m) X, Finite (a ⟶ b) := fun a b => by
    apply Finite.of_injective (fun f => f.left)
    intro f g h
    apply CommaMorphism.ext
    · exact h
    · exact Subsingleton.elim _ _
  exact { fintypeObj := Fintype.ofFinite _, fintypeHom := fun a b => Fintype.ofFinite _ }

private noncomputable instance hasPointwiseLeftSkeleton
    {C : Type u} [Category.{v} C] [HasFiniteColimits C] (m : ℕ)
    (U : SimplicialObject.Truncated C m) :
    Functor.HasPointwiseLeftKanExtension (leftSkeletonInclusion m) U := fun X => by
  infer_instance

/-- Finite colimits provide the left adjoint required in this chapter. -/
theorem has_left_skeleton_functor_of_has_finite_colimits
    {C : Type u} [Category.{v} C] [HasFiniteColimits C] (m : ℕ) :
    HasLeftSkeletonFunctor C m := by
  intro U
  exact Functor.HasLeftKanExtension.mk _
    (Functor.pointwiseLeftKanExtensionUnit (leftSkeletonInclusion m) U)

/-- The source's left adjoint `iₘ!`, implemented by Mathlib's `lan`. -/
noncomputable def leftAdjoint
    {C : Type u} [Category.{v} C] [HasFiniteColimits C] (m : ℕ) :
    SimplicialObject.Truncated C m ⥤ SimplicialObject C :=
  letI : HasLeftSkeletonFunctor C m :=
    has_left_skeleton_functor_of_has_finite_colimits m
  SimplicialObject.Truncated.sk m

/-- The adjunction `iₘ! ⊣ skₘ`, using the canonical Kan-extension adjunction. -/
noncomputable def leftAdjunction
    {C : Type u} [Category.{v} C] [HasFiniteColimits C] (m : ℕ) :
    leftAdjoint (C := C) m ⊣ SimplicialObject.truncation m :=
  letI : HasLeftSkeletonFunctor C m :=
    has_left_skeleton_functor_of_has_finite_colimits m
  Functor.lanAdjunction (leftSkeletonInclusion m) C

/-- The source's mapping-property equivalence for `iₘ!`. -/
noncomputable def leftAdjointHomEquiv
    {C : Type u} [Category.{v} C] [HasFiniteColimits C] (m : ℕ)
    (U : SimplicialObject.Truncated C m) (V : SimplicialObject C) :
    ((leftAdjoint m).obj U ⟶ V) ≃
      (U ⟶ (SimplicialObject.truncation m).obj V) :=
  (leftAdjunction m).homEquiv U V

/-- The unit map `U → skₘ(iₘ!U)`. -/
noncomputable def leftAdjointUnit
    {C : Type u} [Category.{v} C] [HasFiniteColimits C] (m : ℕ)
    (U : SimplicialObject.Truncated C m) :
    U ⟶ (SimplicialObject.truncation m).obj ((leftAdjoint m).obj U) :=
  (leftAdjunction m).unit.app U

/-- The counit map `iₘ!(skₘV) → V`. -/
noncomputable def leftAdjointCounit
    {C : Type u} [Category.{v} C] [HasFiniteColimits C] (m : ℕ)
    (V : SimplicialObject C) :
    (leftAdjoint m).obj ((SimplicialObject.truncation m).obj V) ⟶ V :=
  (leftAdjunction m).counit.app V

/-- The source's indexing category for the degree-`n` colimit. -/
abbrev leftSkeletonIndex (m n : ℕ) :=
  CostructuredArrow (leftSkeletonInclusion m)
    (op (SimplexCategory.mk n))

/-- The diagram `U(n)` whose colimit gives the degree-`n` value of `iₘ!U`. -/
def leftSkeletonDiagram
    {C : Type u} [Category.{v} C] (m n : ℕ)
    (U : SimplicialObject.Truncated C m) : leftSkeletonIndex m n ⥤ C :=
  CostructuredArrow.proj (leftSkeletonInclusion m)
    (op (SimplexCategory.mk n)) ⋙ U

/-- The functorial map of indexing categories induced by a simplex map. -/
def leftSkeletonIndexMap
    {m n n' : ℕ} (φ : SimplexCategory.mk n ⟶ SimplexCategory.mk n') :
    leftSkeletonIndex m n' ⥤ leftSkeletonIndex m n :=
  CostructuredArrow.map φ.op

/-- Precomposition by `φ̲` gives the source's equality of diagrams. -/
theorem leftSkeletonDiagram_map
    {C : Type u} [Category.{v} C]
    {m n n' : ℕ} (U : SimplicialObject.Truncated C m)
    (φ : SimplexCategory.mk n ⟶ SimplexCategory.mk n') :
    leftSkeletonIndexMap φ ⋙ leftSkeletonDiagram m n U =
      leftSkeletonDiagram m n' U := by
  rfl

/-- The colimit in the source's pointwise formula. -/
noncomputable def leftSkeletonColimit
    {C : Type u} [Category.{v} C] (m n : ℕ)
    (U : SimplicialObject.Truncated C m)
    (h : HasColimit (leftSkeletonDiagram m n U)) : C :=
  letI := h
  colimit (leftSkeletonDiagram m n U)

/-- Finite colimits supply each pointwise colimit in the displayed formula. -/
theorem has_left_skeleton_colimit_of_has_finite_colimits
    {C : Type u} [Category.{v} C] [HasFiniteColimits C]
    (m n : ℕ) (U : SimplicialObject.Truncated C m) :
    HasColimit (leftSkeletonDiagram m n U) := by
  infer_instance

/-- The left Kan extension has the source's pointwise colimit description. -/
theorem leftAdjoint_obj_iso_colimit
    {C : Type u} [Category.{v} C] [HasFiniteColimits C]
    (m n : ℕ) (U : SimplicialObject.Truncated C m)
    (h : HasColimit (leftSkeletonDiagram m n U)) :
    Nonempty (((leftAdjoint m).obj U).obj
        (op (SimplexCategory.mk n)) ≅ leftSkeletonColimit m n U h) := by
  exact ⟨Functor.leftKanExtensionObjIsoColimit (leftSkeletonInclusion m) U
    (op (SimplexCategory.mk n))⟩

/-- The simplicial map of `iₘ!U` is the map transported from the functorial
colimit construction along the degreewise colimit isomorphisms. -/
theorem leftAdjoint_map_is_functorial_colimit
    {C : Type u} [Category.{v} C] [HasFiniteColimits C]
    (m n n' : ℕ) (U : SimplicialObject.Truncated C m)
    (φ : SimplexCategory.mk n ⟶ SimplexCategory.mk n')
    (h_n : HasColimit (leftSkeletonDiagram m n U))
    (h_n' : HasColimit (leftSkeletonDiagram m n' U)) :
    ∃ (f : leftSkeletonColimit m n' U h_n' ⟶
        leftSkeletonColimit m n U h_n)
      (e_n : ((leftAdjoint m).obj U).obj
        (op (SimplexCategory.mk n)) ≅ leftSkeletonColimit m n U h_n)
      (e_n' : ((leftAdjoint m).obj U).obj
        (op (SimplexCategory.mk n')) ≅ leftSkeletonColimit m n' U h_n'),
      e_n'.hom ≫ f =
        ((leftAdjoint m).obj U).map φ.op ≫ e_n.hom := by
  sorry

/-- In the truncation range the unit of the adjunction is an isomorphism. -/
theorem leftAdjoint_unit_is_iso
    {C : Type u} [Category.{v} C] [HasFiniteColimits C]
    (m : ℕ) (U : SimplicialObject.Truncated C m) :
    IsIso (leftAdjointUnit m U) := by
  sorry

/-- The degree-`n` colimit exists from the initial object when `n ≤ m`. -/
theorem has_left_skeleton_colimit_of_degree_le
    {C : Type u} [Category.{v} C]
    (m n : ℕ) (U : SimplicialObject.Truncated C m) (hn : n ≤ m) :
    HasColimit (leftSkeletonDiagram m n U) := by
  sorry

/-- The source's recovery statement at an individual degree. -/
theorem leftSkeleton_recovering_degree
    {C : Type u} [Category.{v} C]
    (m n : ℕ) (U : SimplicialObject.Truncated C m) (hn : n ≤ m) :
    Nonempty (leftSkeletonColimit m n U
      (has_left_skeleton_colimit_of_degree_le m n U hn) ≅
      U.obj (op ⟨SimplexCategory.mk n, hn⟩)) := by
  sorry

/-- Some authors call truncation followed by `iₘ!` the `m`-skeleton. -/
noncomputable def sourceSkeletonEndofunctor
    {C : Type u} [Category.{v} C] [HasFiniteColimits C] (m : ℕ) :
    SimplicialObject C ⥤ SimplicialObject C :=
  SimplicialObject.truncation m ⋙ leftAdjoint m

/-- The analogous source notation for truncation followed by the coskeleton. -/
noncomputable def sourceCoskeletonEndofunctor
    {C : Type u} [Category.{v} C] [HasFiniteLimits C] (m : ℕ) :
    SimplicialObject C ⥤ SimplicialObject C :=
  letI : Unit19.HasCoskeletonFunctor (C := C) m :=
    Unit19.has_coskeleton_functor_of_has_finite_limits m
  SimplicialObject.truncation m ⋙ SimplicialObject.Truncated.cosk m

/-! ## Simplicial sets and the boundary of a simplex -/

/-- The left adjoint on simplicial sets. -/
noncomputable def simplicialSetLeftAdjoint (m : ℕ) :
    SimplicialObject.Truncated (Type u) m ⥤ SSet.{u} :=
  leftAdjoint (C := Type u) m

/-- The counit map from the `m`-skeleton of a simplicial set. -/
noncomputable def simplicialSetLeftAdjointCounit
    (U : SSet.{u}) (m : ℕ) :
    (simplicialSetLeftAdjoint m).obj
        ((SimplicialObject.truncation (C := Type u) m).obj U) ⟶ U :=
  leftAdjointCounit (C := Type u) m U

/-- Every simplex of `iₘ!U` above degree `m` is degenerate. -/
theorem simplicialSetLeftAdjoint_high_degenerate
    (m n : ℕ) (U : SimplicialObject.Truncated (Type u) m) (h : m < n) :
    ∀ x : ((simplicialSetLeftAdjoint m).obj U) _⦋n⦌,
      x ∈ ((simplicialSetLeftAdjoint m).obj U).degenerate n := by
  sorry

/-- The simplicial-set counit identifies `iₙ!skₙU` with the earlier skeleton. -/
theorem simplicialSetLeftAdjoint_identifies_skeleton
    (U : SSet.{u}) (n : ℕ) :
    ∃ e : (simplicialSetLeftAdjoint n).obj
          ((SimplicialObject.truncation (C := Type u) n).obj U) ≅
        (Unit18.simplicialSetNSkeleton U n : SSet),
      e.hom ≫ Unit18.simplicialSetNSkeletonInclusion U n =
        simplicialSetLeftAdjointCounit U n := by
  sorry

/-- The source's `iₙ!skₙ` notation as an endofunctor on simplicial sets. -/
noncomputable def sourceSimplicialSetSkeleton (n : ℕ) :
    SSet.{u} ⥤ SSet.{u} :=
  sourceSkeletonEndofunctor (C := Type u) n

/-- The source's boundary construction written using the left adjoint. -/
noncomputable def boundaryViaLeftAdjoint (n : ℕ) (_hn : 0 < n) : SSet.{u} :=
  (simplicialSetLeftAdjoint (n - 1)).obj
    ((SimplicialObject.truncation (C := Type u) (n - 1)).obj
      (Δ[n] : SSet.{u}))

/-- For positive `n`, the source's left-adjoint boundary is `∂Δ[n]`. -/
theorem boundaryViaLeftAdjoint_iso_boundary
    (n : ℕ) (hn : 0 < n) :
    Nonempty (boundaryViaLeftAdjoint n hn ≅ (∂Δ[n] : SSet.{u})) := by
  sorry

/-! ## Attaching one simplex -/

/-- The exact hypotheses in the source's simplex-gluing lemma.

The source's displayed boundary is represented by the canonical `SSet.boundary`;
in degree zero Mathlib identifies it with the empty sub-simplicial set.
-/
structure SimplexAttachment
    {U V : SSet.{u}} (i : U ⟶ V) (n : ℕ) (x : V _⦋n⦌) : Prop where
  mono_i : Mono i
  agrees_below : ∀ {j : ℕ}, j < n →
    Function.Surjective (i.app (op ⦋j⦌))
  exactly_one_new : ∀ y : V _⦋n⦌,
    y ∈ Set.range (i.app (op ⦋n⦌)) ∨ y = x
  new_not_in_range : x ∉ Set.range (i.app (op ⦋n⦌))
  outside_degenerate : ∀ {j : ℕ}, n < j →
    ∀ y : V _⦋j⦌, y ∉ Set.range (i.app (op ⦋j⦌)) →
      y ∈ V.degenerate j

/-- The unique map from a standard simplex represented by its top simplex. -/
def simplexMapOfSimplex (V : SSet.{u}) (n : ℕ) (x : V _⦋n⦌) :
    (Δ[n] : SSet.{u}) ⟶ V :=
  SSet.yonedaEquiv.symm x

/-- The defining property of `simplexMapOfSimplex`. -/
theorem simplexMapOfSimplex_apply (V : SSet.{u}) (n : ℕ) (x : V _⦋n⦌) :
    SSet.yonedaEquiv (simplexMapOfSimplex V n x) = x := by
  exact SSet.yonedaEquiv.apply_symm_apply x

/-- The simplex map represented by `x` is unique. -/
theorem simplexMapOfSimplex_unique (V : SSet.{u}) (n : ℕ) (x : V _⦋n⦌) :
    ∃! f : (Δ[n] : SSet.{u}) ⟶ V,
      SSet.yonedaEquiv f = x := by
  refine ⟨simplexMapOfSimplex V n x, simplexMapOfSimplex_apply V n x, ?_⟩
  intro f hf
  exact SSet.yonedaEquiv.injective
    (hf.trans (simplexMapOfSimplex_apply V n x).symm)

/-- The degree-zero boundary is the initial (empty) simplicial set. -/
theorem boundary_zero_is_empty :
    Nonempty ((∂Δ[0] : SSet.{u}) ≅ initial SSet.{u}) := by
  sorry

/-- A new simplex gives the source's pushout square. -/
theorem glue_simplex
    {U V : SSet.{u}} (i : U ⟶ V) (n : ℕ) (x : V _⦋n⦌)
    (h : SimplexAttachment i n x) :
    ∃ f : (∂Δ[n] : SSet.{u}) ⟶ U,
      f ≫ i = (SSet.boundary n).ι ≫ simplexMapOfSimplex V n x ∧
      IsPushout (SSet.boundary n).ι f
        (simplexMapOfSimplex V n x) i := by
  sorry

/-- A finite inclusion is obtained by adjoining finitely many simplices. -/
theorem finite_simplicial_set_filtration
    {U V : SSet.{u}} (i : U ⟶ V) [Mono i]
    (hU : ∀ n, Finite (U _⦋n⦌) ∧ Nonempty (U _⦋n⦌))
    (hV : ∀ n, Finite (V _⦋n⦌) ∧ Nonempty (V _⦋n⦌))
    [U.Finite] [V.Finite] :
    ∃ (r : ℕ) (W : Fin (r + 1) → SSet.{u})
      (f : ∀ j : Fin r, W j.castSucc ⟶ W j.succ)
      (g : ∀ j : Fin (r + 1), W j ⟶ V),
      W 0 = U ∧ W ⟨r, Nat.lt_succ_self r⟩ = V ∧
      (∀ h₀ : W 0 = U, g 0 = eqToHom h₀ ≫ i) ∧
      (∀ hᵣ : W ⟨r, Nat.lt_succ_self r⟩ = V,
        g ⟨r, Nat.lt_succ_self r⟩ = eqToHom hᵣ) ∧
      (∀ j, f j ≫ g j.succ = g j.castSucc) ∧
      (∀ j, Mono (f j)) ∧
      (∀ j, ∃ (n : ℕ) (x : (W j.succ) _⦋n⦌),
        SimplexAttachment (f j) n x) := by
  sorry

/-! ## The abelian-category consequence -/

/-- The normalized object of `iₘ!U` vanishes above the truncation degree. -/
theorem leftAdjoint_normalizedObject_eq_zero
    {C : Type u} [Category.{v} C] [Abelian C]
    (m : ℕ) (U : SimplicialObject.Truncated C m) (n : ℕ) (h : m < n) :
    Unit18.normalizedObject ((leftAdjoint (C := C) m).obj U) n = 0 := by
  sorry

/-- The abelian `n`-skeleton is the earlier normalized-subobject skeleton. -/
theorem leftAdjoint_identifies_abelian_skeleton
    {C : Type u} [Category.{v} C] [Abelian C] (n : ℕ)
    (U : SimplicialObject C) :
    ∃ (U' : SimplicialObject C) (i : U' ⟶ U),
      Mono i ∧
      (∀ m, imageSubobject (i.app (op ⦋m⦌)) =
        Unit18.abelianNSkeletonSubobject U n m) ∧
      (∀ m, m ≤ n → imageSubobject (i.app (op ⦋m⦌)) = ⊤) ∧
      (∀ m, n < m → Unit18.normalizedSubobject U' m = ⊥) ∧
      ∃ e : (leftAdjoint (C := C) n).obj
          ((SimplicialObject.truncation (C := C) n).obj U) ≅ U',
        e.hom ≫ i = leftAdjointCounit (C := C) n U := by
  sorry

/-! ## The final `coskₙ skₙ` formula -/

/-- The degreewise coproduct used for the source's notation `X × U`. -/
noncomputable def objectProductWithSimplicialSet
    {C : Type u} [Category.{v} C] [HasFiniteCoproducts C]
    (X : C) (U : SSet.{w})
    (hU : Unit13.FiniteNonemptySimplicialSet U) : SimplicialObject C :=
  Unit13.simplicialSetProduct U ((SimplicialObject.const C).obj X) hU

/-- The restriction of `X × Δ[n+1]`, i.e. `X × skₙΔ[n+1]`. -/
noncomputable def truncatedProductWithStandardSimplex
    {C : Type u} [Category.{v} C] [HasFiniteCoproducts C]
    (X : C) (n : ℕ) : SimplicialObject.Truncated C n :=
    (SimplicialObject.truncation (C := C) n).obj
    (objectProductWithSimplicialSet X (Δ[n + 1] : SSet.{w})
      (Unit13.standardSimplex_finite_nonempty (n + 1)))

/-- The first product identity in the source is definitional for this model. -/
theorem truncation_product_with_standard_simplex
    {C : Type u} [Category.{v} C] [HasFiniteCoproducts C]
    (X : C) (n : ℕ) :
    (SimplicialObject.truncation (C := C) n).obj
        (objectProductWithSimplicialSet X (Δ[n + 1] : SSet.{w})
          (Unit13.standardSimplex_finite_nonempty (n + 1))) =
      truncatedProductWithStandardSimplex X n := by
  sorry

/-- The product compatibility of `iₙ!` used in the final proof. -/
theorem leftAdjoint_product_with_standard_simplex
    {C : Type u} [Category.{v} C] [HasFiniteCoproducts C]
    [HasFiniteColimits C] (X : C) (n : ℕ)
    (hA : Unit13.FiniteNonemptySimplicialSet
      ((simplicialSetLeftAdjoint n).obj
        ((SimplicialObject.truncation (C := Type w) n).obj
          (Δ[n + 1] : SSet.{w})))) :
    Nonempty (
      (leftAdjoint (C := C) n).obj
          (truncatedProductWithStandardSimplex X n) ≅
        objectProductWithSimplicialSet X
          ((simplicialSetLeftAdjoint n).obj
            ((SimplicialObject.truncation (C := Type w) n).obj
              (Δ[n + 1] : SSet.{w})))
          hA) := by
  sorry

/-- The simplicial set `Mor_C(X,W)` used in the source's proof. -/
def objectHomSimplicialSet
    {C : Type u} [Category.{v} C] (X : C) (W : SimplicialObject C) :
    SSet.{v} where
  obj A := X ⟶ W.obj A
  map f := ↾fun g => g ≫ W.map f
  map_id A := by
    ext g
    change g ≫ W.map (𝟙 A) = g
    simp
  map_comp f g := by
    ext h
    change h ≫ W.map (f ≫ g) =
      (h ≫ W.map f) ≫ W.map g
    simp [Category.assoc]

/-- The same `Mor_C(X,W)` construction for a truncated simplicial object. -/
def objectHomTruncatedSimplicialSet
    {C : Type u} [Category.{v} C] (n : ℕ) (X : C)
    (W : SimplicialObject.Truncated C n) :
    SimplicialObject.Truncated (Type v) n where
  obj A := X ⟶ W.obj A
  map f := ↾fun g => g ≫ W.map f
  map_id A := by
    ext g
    change g ≫ W.map (𝟙 A) = g
    simp
  map_comp f g := by
    ext h
    change h ≫ W.map (f ≫ g) =
      (h ≫ W.map f) ≫ W.map g
    simp [Category.assoc]

/-- Restricting `Mor_C(X,W)` agrees with the truncated construction. -/
theorem objectHomTruncatedSimplicialSet_truncation
    {C : Type u} [Category.{v} C] (n : ℕ) (X : C)
    (W : SimplicialObject C) :
    objectHomTruncatedSimplicialSet n X
        ((SimplicialObject.truncation (C := C) n).obj W) =
      (SimplicialObject.truncation (C := Type v) n).obj
        (objectHomSimplicialSet X W) := by
  sorry

/-- The source's `Mor(U × X,W)=Mor(U,Mor_C(X,W))` equivalence. -/
theorem objectHomSimplicialSet_product_hom_equiv
    {C : Type u} [Category.{v} C] [HasFiniteCoproducts C]
    (X : C) (U : SSet.{v})
    (hU : Unit13.FiniteNonemptySimplicialSet U) (W : SimplicialObject C) :
    Nonempty ((objectProductWithSimplicialSet X U hU ⟶ W) ≃
      (U ⟶ objectHomSimplicialSet X W)) := by
  sorry

/-- Data for the degree-zero simplicial-object Hom used by the source. -/
structure SimplicialSetHomZeroData
    {C : Type u} [Category.{v} C] [HasFiniteCoproducts C]
    (U : SSet.{v}) (V : SimplicialObject C)
    (hU : Unit13.FiniteNonemptySimplicialSet U) where
  object : C
  homEquiv : ∀ X : C,
    (X ⟶ object) ≃ (objectProductWithSimplicialSet X U hU ⟶ V)

/-- Existence of the degree-zero object `Hom(U,V)₀`. -/
abbrev HasSimplicialSetHomZero
    {C : Type u} [Category.{v} C] [HasFiniteCoproducts C]
    (U : SSet.{v}) (V : SimplicialObject C)
    (hU : Unit13.FiniteNonemptySimplicialSet U) : Prop :=
  Nonempty (SimplicialSetHomZeroData U V hU)

/-- A chosen degree-zero Hom object. -/
noncomputable def simplicialSetHomZero
    {C : Type u} [Category.{v} C] [HasFiniteCoproducts C]
    (U : SSet.{v}) (V : SimplicialObject C)
    (hU : Unit13.FiniteNonemptySimplicialSet U)
    (h : HasSimplicialSetHomZero U V hU) : C :=
  (Classical.choice h).object

/-- Its representing equivalence. -/
noncomputable def simplicialSetHomZeroHomEquiv
    {C : Type u} [Category.{v} C] [HasFiniteCoproducts C]
    (U : SSet.{v}) (V : SimplicialObject C)
    (hU : Unit13.FiniteNonemptySimplicialSet U)
    (h : HasSimplicialSetHomZero U V hU) (X : C) :
    (X ⟶ simplicialSetHomZero U V hU h) ≃
      (objectProductWithSimplicialSet X U hU ⟶ V) :=
  (Classical.choice h).homEquiv X

/-- The finite/degenerate hypotheses from the preceding Hom construction give `Hom(U,V)₀`. -/
theorem exists_simplicialSetHomZero
    {C : Type u} [Category.{v} C] [HasFiniteCoproducts C] [HasFiniteLimits C]
    (U : SSet.{v}) (V : SimplicialObject C)
    (hU : Unit13.FiniteNonemptySimplicialSet U)
    (hUdeg : ∃ N : ℕ, ∀ n, N ≤ n →
      ∀ x : U _⦋n⦌, x ∈ U.degenerate n) :
    HasSimplicialSetHomZero U V hU := by
  sorry

/-- The standard simplex after applying `skₙ` and `iₙ!`. -/
noncomputable def standardSimplexLeftSkeleton (n : ℕ) : SSet.{v} :=
  (simplicialSetLeftAdjoint n).obj
    ((SimplicialObject.truncation (C := Type v) n).obj
      (Δ[n + 1] : SSet.{v}))

/-- The standard simplex left skeleton has the finite nonempty property. -/
theorem standardSimplexLeftSkeleton_finite_nonempty (n : ℕ) :
    Unit13.FiniteNonemptySimplicialSet
      (standardSimplexLeftSkeleton n) := by
  sorry

/-- The preceding finite Hom construction applies to `iₙ!skₙΔ[n+1]`. -/
theorem standardSimplexLeftSkeleton_has_hom_zero
    {C : Type u} [Category.{v} C] [HasFiniteCoproducts C] [HasFiniteLimits C]
    (n : ℕ) (V : SimplicialObject C) :
    HasSimplicialSetHomZero (standardSimplexLeftSkeleton n) V
      (standardSimplexLeftSkeleton_finite_nonempty n) := by
  sorry

/-- The source notation `Hom(iₙ!skₙΔ[n+1],V)₀`. -/
noncomputable def standardSimplexHomZero
    {C : Type u} [Category.{v} C] [HasFiniteCoproducts C] [HasFiniteLimits C]
    (n : ℕ) (V : SimplicialObject C) : C :=
  simplicialSetHomZero (standardSimplexLeftSkeleton n) V
    (standardSimplexLeftSkeleton_finite_nonempty n)
    (standardSimplexLeftSkeleton_has_hom_zero n V)

/-- The Hom object represents maps from `X × iₙ!skₙΔ[n+1]` into `V`. -/
theorem standardSimplexHomZero_hom_equiv
    {C : Type u} [Category.{v} C] [HasFiniteCoproducts C] [HasFiniteLimits C]
    (n : ℕ) (V : SimplicialObject C) (X : C) :
    Nonempty ((X ⟶ standardSimplexHomZero n V) ≃
      (objectProductWithSimplicialSet X
        (standardSimplexLeftSkeleton n)
        (standardSimplexLeftSkeleton_finite_nonempty n) ⟶ V)) := by
  sorry

/-- The final degree formula for `coskₙskₙV`. -/
theorem coskeleton_skeleton_degree_formula
    {C : Type u} [Category.{v} C] [HasFiniteCoproducts C] [HasFiniteLimits C]
    (n : ℕ) (V : SimplicialObject C) :
    Nonempty (
      ((sourceCoskeletonEndofunctor (C := C) n).obj
          V).obj
            (op (SimplexCategory.mk (n + 1))) ≅
        standardSimplexHomZero n V) := by
  sorry

/-- The complete chain of mapping objects used to prove the final formula. -/
theorem coskeleton_skeleton_mapping_chain
    {C : Type u} [Category.{v} C] [HasFiniteCoproducts C] [HasFiniteLimits C]
    (n : ℕ) (V : SimplicialObject C) (X : C) :
    Nonempty (
      (objectProductWithSimplicialSet X (Δ[n + 1] : SSet.{v})
          (Unit13.standardSimplex_finite_nonempty (n + 1)) ⟶
        (sourceCoskeletonEndofunctor (C := C) n).obj V) ≃
      (objectProductWithSimplicialSet X
          (standardSimplexLeftSkeleton n)
          (standardSimplexLeftSkeleton_finite_nonempty n) ⟶ V)) := by
  sorry

/-- The first displayed mapping equivalence in the proof of the final formula. -/
theorem coskeleton_skeleton_first_mapping_equiv
    {C : Type u} [Category.{v} C] [HasFiniteCoproducts C] [HasFiniteLimits C]
    (n : ℕ) (V : SimplicialObject C) (X : C) :
    Nonempty (
      (objectProductWithSimplicialSet X (Δ[n + 1] : SSet.{v})
          (Unit13.standardSimplex_finite_nonempty (n + 1)) ⟶
        (sourceCoskeletonEndofunctor (C := C) n).obj V) ≃
      (truncatedProductWithStandardSimplex X n ⟶
        (SimplicialObject.truncation (C := C) n).obj V)) := by
  sorry

/-- The second displayed mapping equivalence in the proof of the final formula. -/
theorem coskeleton_skeleton_second_mapping_equiv
    {C : Type u} [Category.{v} C] [HasFiniteCoproducts C]
    [HasFiniteColimits C]
    (n : ℕ) (V : SimplicialObject C) (X : C)
    (hA : Unit13.FiniteNonemptySimplicialSet
      ((simplicialSetLeftAdjoint n).obj
        ((SimplicialObject.truncation (C := Type v) n).obj
          (Δ[n + 1] : SSet.{v})))) :
    Nonempty (
      (truncatedProductWithStandardSimplex X n ⟶
        (SimplicialObject.truncation (C := C) n).obj V) ≃
      (objectProductWithSimplicialSet X
          ((simplicialSetLeftAdjoint n).obj
            ((SimplicialObject.truncation (C := Type v) n).obj
              (Δ[n + 1] : SSet.{v}))) hA ⟶ V)) := by
  sorry

end Formalization.Books.Simplicial.Unit21
