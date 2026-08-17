import Formalization.Books.Sheaves.Unit03.Presheaves
import Mathlib.Algebra.Category.Grp.Basic
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.Algebra.Category.Ring.Basic
import Mathlib.CategoryTheory.Whiskering

/-!
# Sheaves on Spaces, Chapter 5: Presheaves of algebraic structures

This file formalizes the source section `books/sheaves.tex:287-381`.
Category-valued presheaves are represented by Mathlib's canonical
`TopCat.Presheaf`, so the object and restriction data in the source are a
functor and its maps.  The underlying-set construction is composition with a
faithful functor to `Type`; this also gives the source's uniqueness statement
for lifts of restriction maps.

The source's preliminary presentation by a set-valued presheaf together with
chosen objects is therefore accounted for by the canonical category-valued
presheaf and its underlying presheaf, without introducing a parallel
structure with transported carrier equalities.
-/

namespace Formalization.Books.Sheaves.Unit05

open CategoryTheory Opposite TopologicalSpace

universe w v u c

/-! ## Underlying sets, maps, and algebraic-structure morphisms -/

/-- The underlying set of an object for a functor to `Type`. -/
abbrev underlyingSet {C : Type u} [Category.{c} C] (F : C ⥤ Type w) (M : C) :=
  F.obj M

/- The morphisms of `Type` are functions, so this is the source's underlying
   map of sets. -/
/-- The underlying map of a morphism for a functor to `Type`. -/
abbrev underlyingMap {C : Type u} [Category.{c} C] (F : C ⥤ Type w)
    {M M' : C} (f : M ⟶ M') :
    underlyingSet F M → underlyingSet F M' := F.map f

/-- A map between underlying sets is a morphism of the algebraic structures
when it is induced by a morphism in the source category. -/
def IsAlgebraicStructureMorphism {C : Type u} [Category.{c} C]
    (F : C ⥤ Type w) {M M' : C}
    (f : underlyingSet F M → underlyingSet F M') : Prop :=
  ∃ φ : M ⟶ M', underlyingMap F φ = f

/-- Faithfulness makes an algebraic-structure morphism between fixed objects
unique. -/
theorem existsUnique_algebraicStructureMorphism {C : Type u} [Category.{c} C]
    (F : C ⥤ Type w)
    [F.Faithful] {M M' : C} (f : underlyingSet F M → underlyingSet F M')
    (hf : IsAlgebraicStructureMorphism F f) :
    ∃! φ : M ⟶ M', underlyingMap F φ = f := by
  rcases hf with ⟨φ, hφ⟩
  refine ⟨φ, hφ, ?_⟩
  intro ψ hψ
  apply F.map_injective
  apply ConcreteCategory.coe_ext
  simpa only [underlyingMap] using hψ.trans hφ.symm

/-! ## Presheaves with values in a category -/

/-- A presheaf on `X` with values in `C`, represented by the canonical
contravariant functor on the category of opens. -/
abbrev PresheafWithValues (X : TopCat.{v}) (C : Type u) [Category.{c} C] :=
  TopCat.Presheaf C X

/-- A morphism of `C`-valued presheaves, represented by a natural
transformation. -/
abbrev PresheafWithValuesMorphism {X : TopCat.{v}} {C : Type u}
    [Category.{c} C] {𝒜 ℬ : PresheafWithValues X C} := 𝒜 ⟶ ℬ

/-- The object assigned by a category-valued presheaf to an open. -/
abbrev presheafObject {X : TopCat.{v}} {C : Type u} [Category.{c} C]
    (𝒜 : PresheafWithValues X C) (U : Opens X) : C :=
  𝒜.obj (op U)

/-- The restriction morphism of a category-valued presheaf along an open
inclusion. -/
abbrev presheafRestriction {X : TopCat.{v}} {C : Type u} [Category.{c} C]
    (𝒜 : PresheafWithValues X C) {U V : Opens X} (h : V ≤ U) :
    presheafObject 𝒜 U ⟶ presheafObject 𝒜 V :=
  𝒜.map (homOfLE h).op

/- The identity and composition axioms in the source definition are the
   corresponding functor laws. -/
/-- Restriction to an open itself is the identity. -/
@[simp]
theorem presheafRestriction_self {X : TopCat.{v}} {C : Type u}
    [Category.{c} C] (𝒜 : PresheafWithValues X C) (U : Opens X) :
    presheafRestriction 𝒜 (le_refl U) = 𝟙 (presheafObject 𝒜 U) := by
  simp [presheafRestriction, presheafObject]

/-- Successive restrictions agree with direct restriction. -/
theorem presheafRestriction_comp {X : TopCat.{v}} {C : Type u}
    [Category.{c} C] (𝒜 : PresheafWithValues X C)
    {U V W : Opens X} (hWV : W ≤ V) (hVU : V ≤ U) :
    presheafRestriction 𝒜 hVU ≫ presheafRestriction 𝒜 hWV =
      presheafRestriction 𝒜 (hWV.trans hVU) := by
  change 𝒜.map (homOfLE hVU).op ≫ 𝒜.map (homOfLE hWV).op =
    𝒜.map (homOfLE (hWV.trans hVU)).op
  rw [← 𝒜.map_comp]
  congr 1

/-- The component of a morphism of category-valued presheaves over an open. -/
abbrev presheafMorphismComponent {X : TopCat.{v}} {C : Type u}
    [Category.{c} C] {𝒜 ℬ : PresheafWithValues X C}
    (φ : PresheafWithValuesMorphism (𝒜 := 𝒜) (ℬ := ℬ)) (U : Opens X) :
    presheafObject 𝒜 U ⟶ presheafObject ℬ U :=
  φ.app (op U)

/-- Compatibility of a presheaf morphism with restriction morphisms. -/
theorem presheafMorphism_compatible {X : TopCat.{v}} {C : Type u}
    [Category.{c} C] {𝒜 ℬ : PresheafWithValues X C}
    (φ : PresheafWithValuesMorphism (𝒜 := 𝒜) (ℬ := ℬ))
    {U V : Opens X} (h : V ≤ U) :
    presheafRestriction 𝒜 h ≫ presheafMorphismComponent φ V =
      presheafMorphismComponent φ U ≫ presheafRestriction ℬ h := by
  exact φ.naturality (homOfLE h).op

/-! ## Underlying presheaves of sets -/

/-- The underlying set-valued presheaf of a `C`-valued presheaf. -/
def underlyingPresheaf {X : TopCat.{v}} {C : Type u} [Category.{c} C]
    (F : C ⥤ Type w) (𝒜 : PresheafWithValues X C) :
    TopCat.Presheaf (Type w) X :=
  𝒜 ⋙ F

/-- Sections of the underlying presheaf are the underlying sets of the
category-valued sections. -/
@[simp]
theorem underlyingPresheaf_obj {X : TopCat.{v}} {C : Type u}
    [Category.{c} C] (F : C ⥤ Type w) (𝒜 : PresheafWithValues X C)
    (U : Opens X) :
    (underlyingPresheaf F 𝒜).obj (op U) =
      F.obj (presheafObject 𝒜 U) := rfl

/-- Restriction in the underlying presheaf is the underlying map of the
category-valued restriction morphism. -/
@[simp]
theorem underlyingPresheaf_map {X : TopCat.{v}} {C : Type u}
    [Category.{c} C] (F : C ⥤ Type w) (𝒜 : PresheafWithValues X C)
    {U V : Opens X} (h : V ≤ U) :
    (underlyingPresheaf F 𝒜).map (homOfLE h).op =
      F.map (presheafRestriction 𝒜 h) := rfl

/-- Every restriction map of the underlying presheaf is a morphism of the
algebraic structures. -/
theorem underlyingPresheaf_restriction_isAlgebraicStructureMorphism
    {X : TopCat.{v}} {C : Type u} [Category.{c} C]
    (F : C ⥤ Type w) (𝒜 : PresheafWithValues X C)
    {U V : Opens X} (h : V ≤ U) :
    IsAlgebraicStructureMorphism F
      ((underlyingPresheaf F 𝒜).map (homOfLE h).op) :=
  ⟨presheafRestriction 𝒜 h, rfl⟩

/-- The category-valued restriction morphism is the unique lift of the
corresponding underlying restriction map when the underlying functor is
faithful. -/
theorem underlyingPresheaf_restriction_lift_unique
    {X : TopCat.{v}} {C : Type u} [Category.{c} C]
    (F : C ⥤ Type w) [F.Faithful] (𝒜 : PresheafWithValues X C)
    {U V : Opens X} (h : V ≤ U) :
    ∃! α : presheafObject 𝒜 U ⟶ presheafObject 𝒜 V,
      F.map α = (underlyingPresheaf F 𝒜).map (homOfLE h).op := by
  refine ⟨presheafRestriction 𝒜 h, rfl, ?_⟩
  intro α hα
  apply F.map_injective
  simpa only [underlyingPresheaf_map, presheafRestriction] using hα

/-- Applying the underlying functor to a morphism of presheaves gives the
corresponding morphism of set-valued presheaves. -/
def underlyingPresheafMorphism {X : TopCat.{v}} {C : Type u}
    [Category.{c} C] (F : C ⥤ Type w) {𝒜 ℬ : PresheafWithValues X C}
  (φ : PresheafWithValuesMorphism (𝒜 := 𝒜) (ℬ := ℬ)) :
    underlyingPresheaf F 𝒜 ⟶ underlyingPresheaf F ℬ :=
  Functor.whiskerRight φ F

/-- The underlying map of a presheaf morphism at each open. -/
@[simp]
theorem underlyingPresheafMorphism_app {X : TopCat.{v}} {C : Type u}
    [Category.{c} C] (F : C ⥤ Type w) {𝒜 ℬ : PresheafWithValues X C}
    (φ : PresheafWithValuesMorphism (𝒜 := 𝒜) (ℬ := ℬ)) (U : Opens X) :
    (underlyingPresheafMorphism F φ).app (op U) =
      F.map (presheafMorphismComponent φ U) := by
  rfl

/-! ## The standard algebraic-structure examples -/

/-- Presheaves of (not necessarily abelian) groups. -/
abbrev PresheafOfGroups (X : TopCat.{v}) :=
  PresheafWithValues X (GrpCat.{w})

/-- Presheaves of rings. -/
abbrev PresheafOfRings (X : TopCat.{v}) :=
  PresheafWithValues X (RingCat.{w})

/-- Presheaves of modules over a fixed ring. -/
abbrev PresheafOfModules (X : TopCat.{v}) (R : Type u) [Ring R] :=
  PresheafWithValues X (ModuleCat.{w} R)

/-- Presheaves of vector spaces over a fixed field. -/
abbrev PresheafOfVectorSpaces (X : TopCat.{v}) (K : Type u) [Field K] :=
  PresheafWithValues X (ModuleCat.{w} K)

/- The canonical forgetful functors used in these examples are faithful;
   these declarations make the source's use of underlying sets explicit. -/
/-- The forgetful functor from groups to sets is faithful. -/
theorem groups_forget_faithful : (forget GrpCat.{w}).Faithful := inferInstance

/-- The forgetful functor from rings to sets is faithful. -/
theorem rings_forget_faithful : (forget RingCat.{w}).Faithful := inferInstance

/-- The forgetful functor from modules to sets is faithful. -/
theorem modules_forget_faithful (R : Type u) [Ring R] :
    (forget (ModuleCat.{w} R)).Faithful := inferInstance

end Formalization.Books.Sheaves.Unit05
