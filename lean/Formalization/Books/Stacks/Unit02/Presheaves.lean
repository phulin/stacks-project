import Formalization.Books.Stacks.Unit01.Presheaves

/-!
# Stacks, Chapter 2: presheaves of morphisms associated to fibred categories

The canonical implementation of the source construction is already provided
by Mathlib's `Pseudofunctor.presheafHom` API and exposed by the preceding
Stacks interfaces as `MorphismPresheaf` and `IsomorphismPresheaf`.  This file
keeps that implementation and records the source-facing formulas and
statements in the chapter namespace.  In particular, it does not introduce a
second pullback convention or a second definition of the morphism presheaf.

The explicit `\alpha_{g,f}` terms in the source are the coherence isomorphisms
used by `Pseudofunctor.presheafHom`; its `pullHom` identity and composition
lemmas are the presheaf verification.  The source's final 2-fibre-product
claim is represented by `TwoFiberProductPresentation`, whose fields record a
setoid-valued fibred category and the associated isomorphism presheaf.
-/

namespace Formalization.Books.Stacks.Unit02

open CategoryTheory
open Opposite
open Formalization.Books.Stacks.Unit01

universe w v u

/-! ## The morphism and isomorphism presheaves -/

@[simp]
theorem morphism_presheaf_obj
    {C : Type u} [Category.{v} C]
    (F : FiberedCategory C) {U V : C} (x y : Fiber F U)
    (f : V ⟶ U) :
    (MorphismPresheaf F x y).obj (op (Over.mk f)) =
      ((F.map f.op.toLoc).toFunctor.obj x ⟶
        (F.map f.op.toLoc).toFunctor.obj y) := by
  rfl

@[simp]
theorem isomorphism_presheaf_obj
    {C : Type u} [Category.{v} C]
    (F : FiberedCategory C) {U V : C} (x y : Fiber F U)
    (f : V ⟶ U) :
    (IsomorphismPresheaf F x y).obj (op (Over.mk f)) =
      { φ : (MorphismPresheaf F x y).obj (op (Over.mk f)) // IsIso φ } := by
  rfl

/- The assertion that the restriction construction is a presheaf is already
   the functor equality supplied by the canonical implementation. -/
theorem mor_presheaf_is_presheaf
    {C : Type u} [Category.{v} C]
    (F : FiberedCategory C) {U : C} (x y : Fiber F U) :
    MorphismPresheaf F x y = F.presheafHom x y :=
  Formalization.Books.Stacks.Unit01.mor_presheaf_is_presheaf F x y

@[simp]
theorem morphism_presheaf_map_id
    {C : Type u} [Category.{v} C]
    (F : FiberedCategory C) {U : C} (x y : Fiber F U)
    (T : (Over C U)ᵒᵖ) (φ : (MorphismPresheaf F x y).obj T) :
    (MorphismPresheaf F x y).map (𝟙 T) φ = φ := by
  simp

theorem morphism_presheaf_map_comp
    {C : Type u} [Category.{v} C]
    (F : FiberedCategory C) {U : C} (x y : Fiber F U)
    {T₀ T₁ T₂ : (Over C U)ᵒᵖ}
    (q₀₁ : T₀ ⟶ T₁) (q₁₂ : T₁ ⟶ T₂)
    (φ : (MorphismPresheaf F x y).obj T₀) :
    (MorphismPresheaf F x y).map (q₀₁ ≫ q₁₂) φ =
      (MorphismPresheaf F x y).map q₁₂
        ((MorphismPresheaf F x y).map q₀₁ φ) := by
  simp

/- The objectwise subtype is the source's subpresheaf of isomorphisms. -/
theorem isomorphism_presheaf_is_subpresheaf
    {C : Type u} [Category.{v} C]
    (F : FiberedCategory C) {U : C} (x y : Fiber F U)
    (T : (Over C U)ᵒᵖ)
    (φ : (IsomorphismPresheaf F x y).obj T) :
    IsIso φ.1 :=
  Formalization.Books.Stacks.Unit01.isom_presheaf_is_subpresheaf F x y T φ

theorem isomorphism_presheaf_inclusion_app
    {C : Type u} [Category.{v} C]
    (F : FiberedCategory C) {U : C} (x y : Fiber F U)
    (T : (Over C U)ᵒᵖ)
    (φ : (IsomorphismPresheaf F x y).obj T) :
    (isomorphismPresheafInclusion F x y).app T φ = φ.1 :=
  Formalization.Books.Stacks.Unit01.isomorphism_presheaf_inclusion_app F x y T φ

/-! ## Maps induced by morphisms of fibred categories -/

/- The imported definition
`presheaf_mor_map_fibred_categories` is the canonical map.  Its component is
the source formula `β_V⁻¹ ≫ F(φ) ≫ α_V`, and the following statement records
the existence of that natural transformation in the chapter namespace. -/
theorem presheaf_mor_map_fibred_categories_exists
    {C : Type u} [Category.{v} C]
    {F G : FiberedCategory C} (η : FiberedMorphism F G) {U : C}
    (x y : Fiber F U) :
    Nonempty
      (F.presheafHom x y ⟶
        G.presheafHom ((η.app (.mk (op U))).toFunctor.obj x)
          ((η.app (.mk (op U))).toFunctor.obj y)) :=
  Formalization.Books.Stacks.Unit01.presheaf_mor_map_fibred_categories_exists η x y

theorem presheaf_mor_map_fibred_categories_is_induced
    {C : Type u} [Category.{v} C]
    {F G : FiberedCategory C} (η : FiberedMorphism F G) {U : C}
    (x y : Fiber F U) :
    IsInducedMorphismPresheafMap η x y
      (Formalization.Books.Stacks.Unit01.presheaf_mor_map_fibred_categories η x y) := by
  sorry

/-! ## Groupoids and the 2-fibre-product presentation -/

theorem isom_presheaf_is_morphism_presheaf_of_groupoid
    {C : Type u} [Category.{v} C] {F : FiberedCategory C}
    (hF : FiberwiseGroupoid F) {U : C} (x y : Fiber F U) :
    Nonempty (IsomorphismPresheaf F x y ≅ MorphismPresheaf F x y) :=
  Formalization.Books.Stacks.Unit01.isom_presheaf_is_morphism_presheaf_of_groupoid
    hF x y

theorem isom_as_two_fibre_product
    {C : Type u} [Category.{v} C]
    (F : FiberedCategory C) {U : C} (x y : Fiber F U) :
    Nonempty (TwoFiberProductPresentation F x y) :=
  Formalization.Books.Stacks.Unit01.isom_as_two_fibre_product F x y

/- The source's strict groupoid presentation remark is proof guidance: the
   preceding groupoid equivalence and the canonical induced presheaf map are
   already the relevant interfaces, so no second strictification is defined
   here.  The mathematical invariance assertion is recorded explicitly. -/
theorem equivalent_fibred_categories_preserve_morphism_presheaf
    {C : Type u} [Category.{v} C]
    {F G : FiberedCategory C} (η : FiberedMorphism F G)
    (hη : FiberwiseEquivalence η) {U : C} (x y : Fiber F U) :
    Nonempty
      (MorphismPresheaf F x y ≅
        MorphismPresheaf G
          ((η.app (.mk (op U))).toFunctor.obj x)
          ((η.app (.mk (op U))).toFunctor.obj y)) := by
  sorry

end Formalization.Books.Stacks.Unit02
