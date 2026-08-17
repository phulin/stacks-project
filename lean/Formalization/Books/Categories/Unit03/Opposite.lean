import Mathlib.CategoryTheory.ConcreteCategory.EpiMono
import Mathlib.CategoryTheory.Yoneda

/-!
# Categories, Chapter 3: Opposite Categories and the Yoneda Lemma

The source section is formalized with Mathlib's canonical opposite-category
and Yoneda interfaces.  In particular, `Cᵒᵖ`, `yoneda`, `yonedaEquiv`,
`yonedaLemma`, and `Functor.IsRepresentable` are the existing constructions;
the declarations below record the source-facing formulas and universal
properties that are useful when reading the chapter.

The source's `Sets` and `PSh(C)` are represented at the fixed universe level
of the hom types of `C` by `Presheaf C := Cᵒᵖ ⥤ Type v`.  This is the usual
universe-bounded Lean replacement for the source's proper-class remark.
-/

namespace Formalization.Books.Categories.Unit03

open CategoryTheory
open CategoryTheory.Functor
open Opposite

universe v u v' u'

/-! ## Opposite categories, contravariant functors, and presheaves -/

abbrev ContravariantFunctor (C : Type u) [Category.{v} C]
    (S : Type u') [Category.{v'} S] := Cᵒᵖ ⥤ S

abbrev Presheaf (C : Type u) [Category.{v} C] := Cᵒᵖ ⥤ Type v

abbrev PresheafCategory (C : Type u) [Category.{v} C] := Presheaf C

/- The hom-set reversal in the source is the canonical `op`/`unop` equivalence. -/
def oppositeHomEquiv {C : Type u} [Category.{v} C] (X Y : C) :
    (op X ⟶ op Y) ≃ (Y ⟶ X) where
  toFun f := f.unop
  invFun f := f.op
  left_inv f := by simp
  right_inv f := by simp

theorem opposite_composition {C : Type u} [Category.{v} C]
    {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) :
    g.op ≫ f.op = (f ≫ g).op := by
  simp

theorem contravariant_map_id {C : Type u} [Category.{v} C]
    {S : Type u'} [Category.{v'} S] (F : ContravariantFunctor C S) (X : C) :
    F.map (𝟙 X).op = 𝟙 (F.obj (op X)) := by
  simp

theorem contravariant_map_comp {C : Type u} [Category.{v} C]
    {S : Type u'} [Category.{v'} S] (F : ContravariantFunctor C S)
    {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) :
    F.map (f ≫ g).op = F.map g.op ≫ F.map f.op := by
  simp

/-! ## Presheaves and the functor of points -/

/- Mathlib's `yoneda` is the source's functor of points. -/
abbrev functorOfPoints {C : Type u} [Category.{v} C] : C ⥤ Presheaf C :=
  yoneda

/- The representable presheaf `h_U` is the object `yoneda.obj U`. -/
abbrev representablePresheaf {C : Type u} [Category.{v} C] (U : C) : Presheaf C :=
  (functorOfPoints (C := C)).obj U

theorem representablePresheaf_obj {C : Type u} [Category.{v} C]
    (U X : C) :
    (representablePresheaf U).obj (op X) = (X ⟶ U) := rfl

theorem representablePresheaf_map_apply {C : Type u} [Category.{v} C]
    {U X Y : C} (f : X ⟶ Y) (g : Y ⟶ U) :
    (representablePresheaf U).map f.op g = f ≫ g := rfl

theorem functorOfPoints_map_app_apply {C : Type u} [Category.{v} C]
    {U V X : C} (φ : U ⟶ V) (f : X ⟶ U) :
    ((functorOfPoints (C := C)).map φ).app (op X) f = f ≫ φ := rfl

theorem functorOfPoints_map_id {C : Type u} [Category.{v} C] (U : C) :
    (functorOfPoints (C := C)).map (𝟙 U) = 𝟙 (representablePresheaf U) := by
  exact (functorOfPoints (C := C)).map_id U

theorem functorOfPoints_map_comp {C : Type u} [Category.{v} C]
    {U V W : C} (φ : U ⟶ V) (ψ : V ⟶ W) :
    (functorOfPoints (C := C)).map (φ ≫ ψ) =
      (functorOfPoints (C := C)).map φ ≫ (functorOfPoints (C := C)).map ψ := by
  exact (functorOfPoints (C := C)).map_comp φ ψ

def functorOfPoints_fully_faithful {C : Type u} [Category.{v} C] :
    (functorOfPoints (C := C)).FullyFaithful :=
  Yoneda.fullyFaithful

theorem functorOfPoints_map_unique {C : Type u} [Category.{v} C]
    {U V : C} (s : representablePresheaf U ⟶ representablePresheaf V) :
    ∃! φ : U ⟶ V, (functorOfPoints (C := C)).map φ = s := by
  let h := functorOfPoints_fully_faithful (C := C)
  refine ⟨h.preimage s, h.map_preimage s, ?_⟩
  intro φ hφ
  apply h.map_injective
  rw [h.map_preimage s]
  exact hφ

/-! ## The Yoneda lemma -/

def yonedaBijection {C : Type u} [Category.{v} C]
    (U : C) (F : Presheaf C) :
    (representablePresheaf U ⟶ F) ≃ F.obj (op U) :=
  yonedaEquiv

theorem yonedaBijection_apply {C : Type u} [Category.{v} C]
    {U : C} {F : Presheaf C} (s : representablePresheaf U ⟶ F) :
    yonedaBijection U F s = s.app (op U) (𝟙 U) :=
  yonedaEquiv_apply s

theorem yonedaBijection_inverse_app_apply {C : Type u} [Category.{v} C]
    {U V : C} {F : Presheaf C} (ξ : F.obj (op U)) (f : V ⟶ U) :
    ((yonedaBijection U F).symm ξ).app (op V) f = F.map f.op ξ := by
  exact yonedaEquiv_symm_app_apply ξ (op V) f

theorem yonedaBijection_natural_in_presheaf {C : Type u} [Category.{v} C]
    {U : C} {F G : Presheaf C} (s : representablePresheaf U ⟶ F)
    (t : F ⟶ G) :
    yonedaBijection U G (s ≫ t) = t.app (op U) (yonedaBijection U F s) := by
  exact yonedaEquiv_comp s t

theorem yonedaBijection_natural_in_object {C : Type u} [Category.{v} C]
    {U V : C} {F : Presheaf C} (s : representablePresheaf U ⟶ F)
    (f : V ⟶ U) :
    F.map f.op (yonedaBijection U F s) =
      yonedaBijection V F ((functorOfPoints (C := C)).map f ≫ s) := by
  exact yonedaEquiv_naturality s f

/- The element-induced natural transformation in the source is the inverse
   direction of `yonedaBijection`. -/
theorem yonedaBijection_inverse_formula {C : Type u} [Category.{v} C]
    {U V : C} {F : Presheaf C} (ξ : F.obj (op U)) :
    ∀ f : V ⟶ U,
      ((yonedaBijection U F).symm ξ).app (op V) f = F.map f.op ξ := by
  intro f
  exact yonedaEquiv_symm_app_apply ξ (op V) f

/-! ## Representability and universal elements -/

theorem isRepresentable_iff_exists_yoneda_iso {C : Type u} [Category.{v} C]
    (F : Presheaf C) :
    Functor.IsRepresentable F ↔
      ∃ U : C, Nonempty (representablePresheaf U ≅ F) := by
  constructor
  · intro hF
    rcases hF.has_representation with ⟨U, ⟨e⟩⟩
    exact ⟨U, ⟨Functor.RepresentableBy.toIso e⟩⟩
  · rintro ⟨U, ⟨e⟩⟩
    exact Functor.IsRepresentable.mk' e

def representingObjectIso {C : Type u} [Category.{v} C]
    {F : Presheaf C} {U V : C}
    (sU : representablePresheaf U ≅ F)
    (sV : representablePresheaf V ≅ F) : U ≅ V :=
  (Functor.representableByEquiv.symm sU).uniqueUpToIso
    (Functor.representableByEquiv.symm sV)

theorem representing_objects_unique_up_to_unique_iso
    {C : Type u} [Category.{v} C] {F : Presheaf C} {U V : C}
    (sU : representablePresheaf U ≅ F)
    (sV : representablePresheaf V ≅ F) :
    ∃! e : U ≅ V,
      (functorOfPoints (C := C)).map e.hom ≫ sV.hom = sU.hom := by
  let h := functorOfPoints_fully_faithful (C := C)
  let e : U ≅ V := h.preimageIso (sU ≪≫ sV.symm)
  have he : (functorOfPoints (C := C)).map e.hom ≫ sV.hom = sU.hom := by
    dsimp [e, Functor.FullyFaithful.preimageIso]
    rw [h.map_preimage]
    simp
  refine ⟨e, he, ?_⟩
  intro e' he'
  apply Iso.ext
  apply h.map_injective
  apply (cancel_mono sV.hom).1
  rw [he', he]

def universalElement {C : Type u} [Category.{v} C]
    {F : Presheaf C} {U : C} (s : representablePresheaf U ≅ F) :
    F.obj (op U) :=
  yonedaBijection U F s.hom

theorem universalElement_eq {C : Type u} [Category.{v} C]
    {F : Presheaf C} {U : C} (s : representablePresheaf U ≅ F) :
    universalElement s = s.hom.app (op U) (𝟙 U) := by
  exact yonedaBijection_apply s.hom

theorem universalElement_induced_map {C : Type u} [Category.{v} C]
    {F : Presheaf C} {U V : C} (s : representablePresheaf U ≅ F)
    (f : V ⟶ U) :
    F.map f.op (universalElement s) = s.hom.app (op V) f := by
  exact map_yonedaEquiv s.hom f

theorem universalElement_map_bijective {C : Type u} [Category.{v} C]
    {F : Presheaf C} {U : C} (s : representablePresheaf U ≅ F) :
    ∀ V : C, Function.Bijective
      (fun f : V ⟶ U => F.map f.op (universalElement s)) := by
  intro V
  have hbij : Function.Bijective
      (fun f : V ⟶ U => (s.app (op V)).hom f) :=
    ConcreteCategory.bijective_of_isIso (s.app (op V)).hom
  constructor
  · intro f g hfg
    change F.map f.op (universalElement s) = F.map g.op (universalElement s) at hfg
    apply hbij.1
    change s.hom.app (op V) f = s.hom.app (op V) g
    rw [← universalElement_induced_map s f, ← universalElement_induced_map s g]
    exact hfg
  · intro ξ
    rcases hbij.2 ξ with ⟨f, hf⟩
    refine ⟨f, ?_⟩
    change F.map f.op (universalElement s) = ξ
    rw [universalElement_induced_map s f]
    change s.hom.app (op V) f = ξ at hf
    exact hf

theorem universalElement_exists_unique {C : Type u} [Category.{v} C]
    {F : Presheaf C} {U V : C} (s : representablePresheaf U ≅ F)
    (ξ : F.obj (op V)) :
    ∃! f : V ⟶ U, F.map f.op (universalElement s) = ξ := by
  exact (universalElement_map_bijective s V).existsUnique ξ

end Formalization.Books.Categories.Unit03
