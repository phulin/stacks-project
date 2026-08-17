import Formalization.Books.Sheaves.Unit03.Presheaves
import Formalization.Books.Categories.Unit04.Products
import Mathlib.Algebra.Category.Grp.Basic
import Mathlib.Algebra.DirectSum.Basic
import Mathlib.CategoryTheory.Monoidal.Cartesian.CommGrp_
import Mathlib.CategoryTheory.Monoidal.Cartesian.FunctorCategory

/-!
# Sheaves on Spaces, Chapter 4: Abelian presheaves

This file formalizes the precise assertions in `books/sheaves.tex`, lines
136--286.  Set-valued presheaves and their restriction maps are reused from
Chapter 3.  Abelian presheaves use Mathlib's canonical presheaves valued in
`AddCommGrpCat`; this is the established implementation of a presheaf whose
sections are abelian groups and whose restriction maps are homomorphisms.
-/

namespace Formalization.Books.Sheaves.Unit04

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open MonoidalCategory CartesianMonoidalCategory
open Formalization.Books.Sheaves.Unit03
open scoped DirectSum

universe w v

/-! ## The singleton presheaf and products -/

/-- The presheaf which has `PUnit` as its sections on every open set. -/
def singletonPresheaf (X : TopCat.{v}) : Presheaf X :=
  constantPresheaf (X := X) (PUnit : Type w)

/-- Every open has the singleton type of sections. -/
@[simp] theorem singletonPresheaf_sections {X : TopCat.{v}} (U : Opens X) :
    Sections (singletonPresheaf.{w, v} X) U = PUnit :=
  rfl

/-- Every restriction map of the singleton presheaf is the unique map. -/
@[simp] theorem singletonPresheaf_map {X : TopCat.{v}} {U V : Opens X} (h : V ≤ U) :
    (singletonPresheaf.{w, v} X).map (homOfLE h).op = 𝟙 (PUnit : Type w) :=
  rfl

/-- The singleton presheaf is terminal in the category of presheaves. -/
def singletonPresheafIsTerminal (X : TopCat.{v}) :
    IsTerminal (singletonPresheaf.{w, v} X) := by
  change IsTerminal ((Functor.const (Opens X)ᵒᵖ).obj (PUnit : Type w))
  exact Functor.isTerminalConst _ Types.isTerminalPUnit

/-- Any terminal presheaf is uniquely isomorphic to the singleton presheaf. -/
noncomputable def terminalPresheafIso {X : TopCat.{v}} (F : Presheaf X)
    (hF : IsTerminal F) : F ≅ singletonPresheaf.{w, v} X :=
  hF.uniqueUpToIso (singletonPresheafIsTerminal.{w, v} X)

/-- Any two isomorphisms between terminal presheaves are equal. -/
theorem terminalPresheafIso_unique {X : TopCat.{v}} (F : Presheaf X)
    (hF : IsTerminal F) (e : F ≅ singletonPresheaf.{w, v} X) :
    e = terminalPresheafIso F hF := by
  apply Iso.ext
  exact (singletonPresheafIsTerminal.{w, v} X).hom_ext e.hom
    (terminalPresheafIso F hF).hom

/-!
The functor-category instances are not inferred through the universe-polymorphic
`Presheaf` abbreviation at this point, so this explicit bridge exposes the
canonical pointwise cartesian structure at the source-facing type.
-/

noncomputable instance presheafCartesianMonoidalCategory (X : TopCat.{v}) :
    CartesianMonoidalCategory (Presheaf.{w, v} X) := by
  change CartesianMonoidalCategory ((Opens X)ᵒᵖ ⥤ Type w)
  infer_instance

/-- The standard braided structure induced by the cartesian structure. -/
noncomputable instance presheafBraidedCategory (X : TopCat.{v}) :
    BraidedCategory (Presheaf.{w, v} X) :=
  .ofCartesianMonoidalCategory

/-- The chosen product of two set-valued presheaves. -/
noncomputable abbrev presheafProduct {X : TopCat.{v}} (F G : Presheaf X) := F ⊗ G

/-- The first projection from the product of two presheaves. -/
noncomputable abbrev presheafProductFst {X : TopCat.{v}} {F G : Presheaf X} :
    presheafProduct F G ⟶ F := CartesianMonoidalCategory.fst F G

/-- The second projection from the product of two presheaves. -/
noncomputable abbrev presheafProductSnd {X : TopCat.{v}} {F G : Presheaf X} :
    presheafProduct F G ⟶ G := CartesianMonoidalCategory.snd F G

/-- The chosen presheaf product satisfies the binary-product universal property. -/
noncomputable def presheafProductIsProduct {X : TopCat.{v}} (F G : Presheaf X) :
    IsLimit (BinaryFan.mk (presheafProductFst (F := F) (G := G))
      (presheafProductSnd (F := F) (G := G))) :=
  CartesianMonoidalCategory.tensorProductIsBinaryProduct F G

/-- Sections of a product presheaf are canonically pairs of sections. -/
noncomputable def presheafProductSectionsEquiv {X : TopCat.{v}}
    (F G : Presheaf X) (U : Opens X) :
    Sections (presheafProduct F G) U ≃ Sections F U × Sections G U :=
  Equiv.refl _

/-- Restriction in the product presheaf is componentwise restriction. -/
theorem presheafProduct_restriction {X : TopCat.{v}}
    {F G : Presheaf X} {U V : Opens X} (h : V ≤ U)
    (s : Sections F U) (t : Sections G U) :
    (presheafProduct F G).map (homOfLE h).op
        ((presheafProductSectionsEquiv F G U).symm (s, t)) =
      (restriction (F := F) h s, restriction (F := G) h t) := by
  rfl

/-- The product projections give the source's hom-set product bijection. -/
noncomputable def presheafProductHomEquiv {X : TopCat.{v}}
    (F G H : Presheaf X) :
    (H ⟶ presheafProduct F G) ≃ (H ⟶ F) × (H ⟶ G) :=
  Formalization.Books.Categories.Unit04.productHomEquiv
    (presheafProductIsProduct F G) H

/-- For an abelian-group law, the zero and negation operations are unique. -/
theorem addCommGroup_zero_neg_unique {A : Type w} (g₁ g₂ : AddCommGroup A)
    (hadd :
      (letI := g₁; fun x y : A ↦ x + y) =
        (letI := g₂; fun x y : A ↦ x + y)) :
    (letI := g₁; (0 : A)) = (letI := g₂; (0 : A)) ∧
      (letI := g₁; fun x : A ↦ -x) = (letI := g₂; fun x : A ↦ -x) := by
  sorry

/-! ## The four presentations of an abelian presheaf -/

/-- A map of presheaves which is pointwise written as an addition operation. -/
abbrev PresheafAdditionMap {X : TopCat.{v}} (F : Presheaf X) :=
  presheafProduct F F ⟶ F

/-- A map of presheaves which is pointwise written as a negation operation. -/
abbrev PresheafNegationMap {X : TopCat.{v}} (F : Presheaf X) := F ⟶ F

/-- A map from the singleton presheaf, pointwise written as zero. -/
abbrev PresheafZeroMap {X : TopCat.{v}} (F : Presheaf X) :=
  singletonPresheaf X ⟶ F

/-- The section-level operation induced by a natural addition map. -/
noncomputable def presheafAdditionAt {X : TopCat.{v}} {F : Presheaf X}
    (add : PresheafAdditionMap F) (U : Opens X)
    (s t : Sections F U) : Sections F U :=
  add.app (op U) ((presheafProductSectionsEquiv F F U).symm (s, t))

/-- The section-level operation induced by a natural negation map. -/
def presheafNegationAt {X : TopCat.{v}} {F : Presheaf X}
    (neg : PresheafNegationMap F) (U : Opens X)
    (s : Sections F U) : Sections F U :=
  neg.app (op U) s

/-- The section-level operation induced by a natural zero map. -/
def presheafZeroAt {X : TopCat.{v}} {F : Presheaf X}
    (zero : PresheafZeroMap F) (U : Opens X) : Sections F U :=
  zero.app (op U) PUnit.unit

/-!
The first presentation in the source is a family of abelian-group structures
on sections, with additive restriction maps.  Preservation of addition and
zero is the concrete form of being an additive-group homomorphism.
-/

structure PointwiseAbelianPresheafData {X : TopCat.{v}} (F : Presheaf X) where
  /-- The abelian-group structure on the sections over each open. -/
  group : ∀ U : Opens X, AddCommGroup (Sections F U)
  /-- Restriction maps preserve addition. -/
  restriction_add : ∀ {U V : Opens X} (h : V ≤ U),
    letI := group U
    letI := group V
    ∀ s t : Sections F U,
      restriction (F := F) h (s + t) =
        restriction (F := F) h s + restriction (F := F) h t
  /-- Restriction maps preserve zero. -/
  restriction_zero : ∀ {U V : Opens X} (h : V ≤ U),
    letI := group U
    letI := group V
    restriction (F := F) h (0 : Sections F U) = (0 : Sections F V)

/-!
Mathlib's internal commutative-group-object interface is the source-facing
version of item (2): its operations are morphisms in the presheaf category,
and its fields are the group-object axioms.
-/

/-- The categorical commutative-group-object presentation of an abelian presheaf. -/
abbrev PresheafAbelianGroupObjectData {X : TopCat.{v}} (F : Presheaf X) :=
  CommGrpObj F

/-!
The third and fourth presentations retain the natural-operation maps but make
the pointwise abelian-group structures explicit.  The operation-compatibility
fields identify those maps with the displayed operations on sections.
-/

structure PointwiseAbelianOperationsData {X : TopCat.{v}} (F : Presheaf X) where
  /-- The natural addition map. -/
  add : PresheafAdditionMap F
  /-- The natural negation map. -/
  neg : PresheafNegationMap F
  /-- The natural zero map. -/
  zero : PresheafZeroMap F
  /-- The abelian-group structure on every section type. -/
  group : ∀ U : Opens X, AddCommGroup (Sections F U)
  /-- The natural addition map is the pointwise group addition. -/
  add_apply : ∀ U : Opens X,
    letI := group U
    ∀ s t : Sections F U, presheafAdditionAt add U s t = s + t
  /-- The natural negation map is the pointwise group negation. -/
  neg_apply : ∀ U : Opens X,
    letI := group U
    ∀ s : Sections F U, presheafNegationAt neg U s = -s
  /-- The natural zero map is the pointwise group zero. -/
  zero_apply : ∀ U : Opens X,
    letI := group U
    presheafZeroAt zero U = (0 : Sections F U)

structure AdditionOnlyAbelianPresheafData {X : TopCat.{v}} (F : Presheaf X) where
  /-- The natural addition map. -/
  add : PresheafAdditionMap F
  /-- The pointwise abelian-group structures whose addition is `add`. -/
  group : ∀ U : Opens X, AddCommGroup (Sections F U)
  /-- The natural addition map is the chosen pointwise addition. -/
  add_apply : ∀ U : Opens X,
    letI := group U
    ∀ s t : Sections F U, presheafAdditionAt add U s t = s + t

/-- The four data types in the source lemma are pairwise naturally bijective.

The theorem is stated as existence of equivalences so that the four source
presentations remain separate, while the proof of their equivalence is left to
the proof stage.
-/
theorem abelianPresheafData_bijections {X : TopCat.{v}} (F : Presheaf X) :
    Nonempty (PointwiseAbelianPresheafData F ≃ PresheafAbelianGroupObjectData F) ∧
    Nonempty (PointwiseAbelianPresheafData F ≃ PointwiseAbelianOperationsData F) ∧
    Nonempty (PointwiseAbelianPresheafData F ≃ AdditionOnlyAbelianPresheafData F) ∧
    Nonempty (PresheafAbelianGroupObjectData F ≃ PointwiseAbelianOperationsData F) ∧
    Nonempty (PresheafAbelianGroupObjectData F ≃ AdditionOnlyAbelianPresheafData F) ∧
    Nonempty (PointwiseAbelianOperationsData F ≃ AdditionOnlyAbelianPresheafData F) := by
  sorry

/-! ## Presheaves of abelian groups -/

/-- A presheaf of abelian groups, represented canonically by an `AddCommGrpCat`-valued functor. -/
abbrev AbelianPresheaf (X : TopCat.{v}) : Type (max (w + 1) v) :=
  TopCat.Presheaf AddCommGrpCat.{w} X

/-- A morphism of abelian presheaves. -/
abbrev AbelianPresheafMorphism {X : TopCat.{v}}
    (F G : AbelianPresheaf X) := F ⟶ G

/-- The category denoted `PAb(X)` in the source. -/
abbrev PAb (X : TopCat.{v}) := AbelianPresheaf X

/-- The underlying set-valued presheaf of an abelian presheaf. -/
def underlyingPresheaf {X : TopCat.{v}} (F : AbelianPresheaf X) : Presheaf X :=
  F ⋙ (forget AddCommGrpCat)

/-- Sections of an abelian presheaf, viewed as an ordinary type. -/
abbrev AbelianSections {X : TopCat.{v}} (F : AbelianPresheaf X) (U : Opens X) :=
  ToType (F.obj (op U))

/-- The pointwise additive-group structure inherited by the underlying presheaf. -/
instance underlyingPresheafAddCommGroup {X : TopCat.{v}} (F : AbelianPresheaf X)
    (U : Opens X) : AddCommGroup (Sections (underlyingPresheaf F) U) := by
  change AddCommGroup (ToType (F.obj (op U)))
  exact AddCommGrpCat.str (F.obj (op U))

/-- The canonical pointwise abelian-presheaf data carried by an abelian presheaf. -/
def abelianPresheafPointwiseData {X : TopCat.{v}} (F : AbelianPresheaf X) :
    PointwiseAbelianPresheafData (underlyingPresheaf F) where
  group U := inferInstance
  restriction_add {U V} h s t := by
    change F.map (homOfLE h).op (s + t) =
      F.map (homOfLE h).op s + F.map (homOfLE h).op t
    exact (F.map (homOfLE h).op).hom.map_add s t
  restriction_zero {U V} h := by
    change F.map (homOfLE h).op (0 : AbelianSections F _) = 0
    exact (F.map (homOfLE h).op).hom.map_zero

/-- The section map of an abelian-presheaf morphism is an additive homomorphism. -/
abbrev abelianPresheafMorphismAt {X : TopCat.{v}}
    {F G : AbelianPresheaf X} (φ : AbelianPresheafMorphism F G) (U : Opens X) :
    AbelianSections F U →+ AbelianSections G U :=
  (φ.app (op U)).hom

/-! ## The direct-sum-over-points example -/

variable {X : TopCat.{v}} (M : X → Type w) [∀ x, AddCommGroup (M x)]

/-- The additive restriction map which discards summands outside `V`. -/
noncomputable def directSumRestriction {U V : Opens X} (_h : V ≤ U) :
    (⨁ x : U, M x) →+ (⨁ x : V, M x) := by
  classical
  exact DirectSum.toAddMonoid fun x ↦
    if hx : (x : X) ∈ V then
      DirectSum.of (fun y : V ↦ M y) ⟨x, hx⟩
    else
      0

/-- Restriction to the same open is the identity on the direct sum. -/
theorem directSumRestriction_self {U : Opens X} :
    directSumRestriction M (le_refl U) = AddMonoidHom.id _ := by
  classical
  apply DirectSum.addHom_ext
  intro x m
  simp [directSumRestriction]

/-- Successive direct-sum restrictions agree with direct restriction. -/
theorem directSumRestriction_comp {U V W : Opens X} (hWV : W ≤ V) (hVU : V ≤ U) :
    (directSumRestriction M hWV).comp (directSumRestriction M hVU) =
      directSumRestriction M (hWV.trans hVU) := by
  classical
  apply DirectSum.addHom_ext
  intro x m
  by_cases hxV : (x : X) ∈ V
  · by_cases hxW : (x : X) ∈ W
    · simp [directSumRestriction, hxV, hxW]
    · simp [directSumRestriction, hxV, hxW]
  · have hxW : ¬ (x : X) ∈ W := fun hxW ↦ hxV (hWV hxW)
    simp [directSumRestriction, hxV, hxW]

/-- The presheaf whose sections over `U` are `⨁ x ∈ U, M x`. -/
noncomputable def directSumPresheaf : AbelianPresheaf X where
  obj U := AddCommGrpCat.of (⨁ x : U.unop, M x)
  map {U V} f := AddCommGrpCat.ofHom (directSumRestriction M f.unop.le)
  map_id U := by
    apply AddCommGrpCat.ext
    intro s
    simpa using DFunLike.congr_fun
      (directSumRestriction_self M (U := U.unop)) s
  map_comp f g := by
    apply AddCommGrpCat.ext
    intro s
    simpa using DFunLike.congr_fun
      (directSumRestriction_comp M g.unop.le f.unop.le).symm s

/-- The restriction map of the direct-sum presheaf is the pointwise truncation map. -/
theorem directSumPresheaf_map {U V : Opens X} (h : V ≤ U) :
    (directSumPresheaf M).map (homOfLE h).op =
      AddCommGrpCat.ofHom (directSumRestriction M h) := rfl

end Formalization.Books.Sheaves.Unit04
