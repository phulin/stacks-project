import Formalization.Books.Sheaves.Unit03.Presheaves
import Formalization.Books.Categories.Unit04.Products
import Mathlib.Algebra.Category.Grp.Basic
import Mathlib.Algebra.Group.Ext
import Mathlib.Algebra.Group.MinimalAxioms
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
The functor-category instance is not inferred through the universe-polymorphic
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
  have hgroups : g₁ = g₂ := AddCommGroup.ext hadd
  subst g₂
  exact ⟨rfl, rfl⟩

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
  let addOf (P : PointwiseAbelianPresheafData F) : PresheafAdditionMap F :=
    { app := fun U => TypeCat.ofHom (fun st : (presheafProduct F F).obj U =>
        let p := (presheafProductSectionsEquiv F F U.unop) st
        letI := P.group U.unop
        p.1 + p.2)
      naturality := by
        intro U V f
        ext st
        let p := (presheafProductSectionsEquiv F F U.unop) st
        change (letI := P.group V.unop;
            restriction (F := F) f.unop.le p.1 + restriction (F := F) f.unop.le p.2) =
          (letI := P.group U.unop;
            restriction (F := F) f.unop.le (p.1 + p.2))
        exact (P.restriction_add f.unop.le p.1 p.2).symm }
  let negOf (P : PointwiseAbelianPresheafData F) : PresheafNegationMap F :=
    { app := fun U => TypeCat.ofHom (fun s : F.obj U =>
        letI := P.group U.unop; -s)
      naturality := by
        intro U V f
        ext s
        let _ := P.group U.unop
        let _ := P.group V.unop
        let r : Sections F U.unop →+ Sections F V.unop :=
          { toFun := restriction (F := F) f.unop.le
            map_zero' := P.restriction_zero f.unop.le
            map_add' := P.restriction_add f.unop.le }
        change (letI := P.group V.unop; -restriction (F := F) f.unop.le s) =
          (letI := P.group U.unop; restriction (F := F) f.unop.le (-s))
        exact (r.map_neg s).symm }
  let zeroOf (P : PointwiseAbelianPresheafData F) : PresheafZeroMap F :=
    { app := fun U => TypeCat.ofHom (fun _ : PUnit =>
        letI := P.group U.unop
        (0 : Sections F U.unop))
      naturality := by
        intro U V f
        ext u
        cases u
        change (letI := P.group V.unop; (0 : Sections F V.unop)) =
          (letI := P.group U.unop; restriction (F := F) f.unop.le (0 : Sections F U.unop))
        exact (P.restriction_zero f.unop.le).symm }
  let pointwiseToOperations (P : PointwiseAbelianPresheafData F) :
      PointwiseAbelianOperationsData F :=
    { add := addOf P
      neg := negOf P
      zero := zeroOf P
      group := P.group
      add_apply := by intro U s t; rfl
      neg_apply := by intro U s; rfl
      zero_apply := by intro U; rfl }
  let operationsToPointwise (Q : PointwiseAbelianOperationsData F) :
      PointwiseAbelianPresheafData F :=
    { group := Q.group
      restriction_add {U V} h := by
        let _ := Q.group U
        let _ := Q.group V
        intro s t
        have e := Q.add.naturality (homOfLE h).op
        have e' := congrArg (fun k =>
          (ConcreteCategory.hom k)
            ((presheafProductSectionsEquiv F F U).symm (s, t))) e
        change Q.add.app (op V)
            ((presheafProductSectionsEquiv F F V).symm
              (restriction (F := F) h s,
                restriction (F := F) h t)) =
          (F.map (homOfLE h).op)
            (Q.add.app (op U)
              ((presheafProductSectionsEquiv F F U).symm (s, t))) at e'
        change presheafAdditionAt Q.add V (restriction (F := F) h s)
            (restriction (F := F) h t) =
          restriction (F := F) h (presheafAdditionAt Q.add U s t) at e'
        rw [Q.add_apply V, Q.add_apply U] at e'
        exact e'.symm
      restriction_zero {U V} h := by
        let _ := Q.group U
        let _ := Q.group V
        have e := Q.zero.naturality (homOfLE h).op
        have e' := congrArg (fun k => (ConcreteCategory.hom k) PUnit.unit) e
        change Q.zero.app (op V) PUnit.unit =
          (F.map (homOfLE h).op) (Q.zero.app (op U) PUnit.unit) at e'
        change presheafZeroAt Q.zero V =
          restriction (F := F) h (presheafZeroAt Q.zero U) at e'
        rw [Q.zero_apply V, Q.zero_apply U] at e'
        exact e'.symm }
  let pointwiseOperationsEquiv :
      PointwiseAbelianPresheafData F ≃ PointwiseAbelianOperationsData F :=
    { toFun := pointwiseToOperations
      invFun := operationsToPointwise
      left_inv := by
        intro P
        cases P
        rfl
      right_inv := by
        intro Q
        have operations_ext : ∀ (R S : PointwiseAbelianOperationsData F),
            R.add = S.add → R.neg = S.neg → R.zero = S.zero → R.group = S.group → R = S := by
          intro R S hadd hneg hzero hgroup
          cases R
          cases S
          cases hadd
          cases hneg
          cases hzero
          cases hgroup
          rfl
        have hadd : addOf (operationsToPointwise Q) = Q.add := by
          ext U s
          let p := (presheafProductSectionsEquiv F F U) s
          let _ := Q.group U
          change p.1 + p.2 = presheafAdditionAt Q.add U p.1 p.2
          exact (Q.add_apply U p.1 p.2).symm
        have hneg : negOf (operationsToPointwise Q) = Q.neg := by
          ext U s
          change (letI := Q.group U; -s) = presheafNegationAt Q.neg U s
          exact (Q.neg_apply U s).symm
        have hzero : zeroOf (operationsToPointwise Q) = Q.zero := by
          ext U u
          cases u
          change (letI := Q.group U; (0 : Sections F U)) = presheafZeroAt Q.zero U
          exact (Q.zero_apply U).symm
        apply operations_ext
        · exact hadd
        · exact hneg
        · exact hzero
        · rfl }
  let additionOnlyRestrictionAdd (R : AdditionOnlyAbelianPresheafData F)
      {U V : Opens X} (h : V ≤ U) (s t : Sections F U) :
      (letI := R.group U; letI := R.group V;
        restriction (F := F) h (s + t) =
          restriction (F := F) h s + restriction (F := F) h t) := by
    let _ := R.group U
    let _ := R.group V
    have e := R.add.naturality (homOfLE h).op
    have e' := congrArg (fun k =>
      (ConcreteCategory.hom k)
        ((presheafProductSectionsEquiv F F U).symm (s, t))) e
    change presheafAdditionAt R.add V (restriction (F := F) h s)
        (restriction (F := F) h t) =
      restriction (F := F) h (presheafAdditionAt R.add U s t) at e'
    rw [R.add_apply V, R.add_apply U] at e'
    exact e'.symm
  let additionOnlyToPointwise (R : AdditionOnlyAbelianPresheafData F) :
      PointwiseAbelianPresheafData F :=
    { group := R.group
      restriction_add {U V} h := by
        intro s t
        exact additionOnlyRestrictionAdd R h s t
      restriction_zero {U V} h := by
        let _ := R.group U
        let _ := R.group V
        have e := R.add.naturality (homOfLE h).op
        have e' := congrArg (fun k =>
          (ConcreteCategory.hom k)
            ((presheafProductSectionsEquiv F F U).symm ((0 : Sections F U), 0))) e
        change presheafAdditionAt R.add V
            (restriction (F := F) h (0 : Sections F U))
            (restriction (F := F) h (0 : Sections F U)) =
          restriction (F := F) h (presheafAdditionAt R.add U
            (0 : Sections F U) (0 : Sections F U)) at e'
        rw [R.add_apply V, R.add_apply U] at e'
        have hz : restriction (F := F) h (0 : Sections F U) +
            restriction (F := F) h (0 : Sections F U) =
            restriction (F := F) h (0 : Sections F U) := by
          simpa using e'
        have hz' : restriction (F := F) h (0 : Sections F U) +
            restriction (F := F) h (0 : Sections F U) =
            restriction (F := F) h (0 : Sections F U) + 0 := by
          simpa using hz
        exact add_left_cancel hz' }
  let pointwiseToAdditionOnly (P : PointwiseAbelianPresheafData F) :
      AdditionOnlyAbelianPresheafData F :=
    { add := addOf P
      group := P.group
      add_apply := by intro U s t; rfl }
  let pointwiseAdditionOnlyEquiv :
      PointwiseAbelianPresheafData F ≃ AdditionOnlyAbelianPresheafData F :=
    { toFun := pointwiseToAdditionOnly
      invFun := additionOnlyToPointwise
      left_inv := by
        intro P
        cases P
        rfl
      right_inv := by
        intro R
        have addition_only_ext : ∀ (A B : AdditionOnlyAbelianPresheafData F),
            A.add = B.add → A.group = B.group → A = B := by
          intro A B hadd hgroup
          cases A
          cases B
          cases hadd
          cases hgroup
          rfl
        have hadd : addOf (additionOnlyToPointwise R) = R.add := by
          ext U s
          let p := (presheafProductSectionsEquiv F F U) s
          let _ := R.group U
          change p.1 + p.2 = presheafAdditionAt R.add U p.1 p.2
          exact (R.add_apply U p.1 p.2).symm
        apply addition_only_ext
        · exact hadd
        · rfl }
  let pointwiseToComm (P : PointwiseAbelianPresheafData F) :
      PresheafAbelianGroupObjectData F :=
    { toMonObj :=
        { one := zeroOf P
          mul := addOf P
          one_mul := by
            ext U s
            rcases s with ⟨u, s⟩
            cases u
            let _ := P.group U
            change (0 : Sections F U) + s = s
            exact zero_add s
          mul_one := by
            ext U s
            rcases s with ⟨s, u⟩
            cases u
            let _ := P.group U
            change s + (0 : Sections F U) = s
            exact add_zero s
          mul_assoc := by
            ext U s
            rcases s with ⟨⟨s, t⟩, u⟩
            let _ := P.group U
            change (s + t) + u = s + (t + u)
            exact add_assoc s t u }
      inv := negOf P
      left_inv := by
        ext U s
        let _ := P.group U
        change -s + s = (0 : Sections F U)
        exact neg_add_cancel s
      right_inv := by
        ext U s
        let _ := P.group U
        change s + -s = (0 : Sections F U)
        exact add_neg_cancel s
      mul_comm := by
        ext U s
        rcases s with ⟨s, t⟩
        let _ := P.group U
        change t + s = s + t
        exact add_comm t s }
  let commGroupAt (G : PresheafAbelianGroupObjectData F) (U : Opens X) :
      AddCommGroup (Sections F U) := by
    let add : Sections F U → Sections F U → Sections F U :=
      presheafAdditionAt G.toMonObj.mul U
    let zero : Sections F U := presheafZeroAt G.toMonObj.one U
    let neg : Sections F U → Sections F U := presheafNegationAt G.inv U
    letI : Add (Sections F U) := ⟨add⟩
    letI : Zero (Sections F U) := ⟨zero⟩
    letI : Neg (Sections F U) := ⟨neg⟩
    have assoc : ∀ s t u : Sections F U, (s + t) + u = s + (t + u) := by
      intro s t u
      have e := G.toMonObj.mul_assoc
      have e' := congrArg (fun k =>
        (ConcreteCategory.hom (k.app (op U)))
          ((presheafProductSectionsEquiv (presheafProduct F F) F U).symm
            ((presheafProductSectionsEquiv F F U).symm (s, t), u))) e
      change (s + t) + u = s + (t + u) at e'
      exact e'
    have zero_add' : ∀ s : Sections F U, 0 + s = s := by
      intro s
      have e := G.toMonObj.one_mul
      have e' := congrArg (fun k =>
        (ConcreteCategory.hom (k.app (op U))) (PUnit.unit, s)) e
      change (0 : Sections F U) + s = s at e'
      exact e'
    have neg_add_cancel' : ∀ s : Sections F U, -s + s = 0 := by
      intro s
      have e := G.left_inv
      have e' := congrArg (fun k =>
        (ConcreteCategory.hom (k.app (op U))) s) e
      change (-s : Sections F U) + s = 0 at e'
      exact e'
    have add_comm' : ∀ s t : Sections F U, s + t = t + s := by
      intro s t
      have e := G.mul_comm
      have e' := congrArg (fun k =>
        (ConcreteCategory.hom (k.app (op U))) (s, t)) e
      change t + s = s + t at e'
      exact e'.symm
    letI : AddGroup (Sections F U) :=
      AddGroup.ofLeftAxioms assoc zero_add' neg_add_cancel'
    exact { add_comm := add_comm' }
  let commToPointwise (G : PresheafAbelianGroupObjectData F) :
      PointwiseAbelianPresheafData F :=
    { group := commGroupAt G
      restriction_add {U V} h := by
        let _ := commGroupAt G U
        let _ := commGroupAt G V
        intro s t
        have e := G.toMonObj.mul.naturality (homOfLE h).op
        have e' := congrArg (fun k =>
          (ConcreteCategory.hom k)
            ((presheafProductSectionsEquiv F F U).symm (s, t))) e
        change presheafAdditionAt G.toMonObj.mul V
            (restriction (F := F) h s) (restriction (F := F) h t) =
          restriction (F := F) h (presheafAdditionAt G.toMonObj.mul U s t) at e'
        exact e'.symm
      restriction_zero {U V} h := by
        let _ := commGroupAt G U
        let _ := commGroupAt G V
        have e := G.toMonObj.one.naturality (homOfLE h).op
        have e' := congrArg (fun k => (ConcreteCategory.hom k) PUnit.unit) e
        change presheafZeroAt G.toMonObj.one V =
          restriction (F := F) h (presheafZeroAt G.toMonObj.one U) at e'
        exact e'.symm }
  let pointwise_ext : ∀ (P Q : PointwiseAbelianPresheafData F),
      P.group = Q.group → P = Q := by
    intro P Q hgroup
    cases P
    cases Q
    cases hgroup
    rfl
  let grp_ext : ∀ (G H : GrpObj F),
      G.toMonObj = H.toMonObj → G.inv = H.inv → G = H := by
    intro G H hmon hinv
    cases G
    cases H
    cases hmon
    cases hinv
    rfl
  let comm_ext : ∀ (G H : PresheafAbelianGroupObjectData F),
      G.toMonObj = H.toMonObj → G.inv = H.inv → G = H := by
    intro G H hmon hinv
    have hgrp : G.toGrpObj = H.toGrpObj := grp_ext G.toGrpObj H.toGrpObj hmon hinv
    cases G
    cases H
    cases hgrp
    rfl
  let pointwiseCommEquiv :
      PointwiseAbelianPresheafData F ≃ PresheafAbelianGroupObjectData F :=
    { toFun := pointwiseToComm
      invFun := commToPointwise
      left_inv := by
        intro P
        apply pointwise_ext
        funext U
        apply AddCommGroup.ext
        rfl
      right_inv := by
        intro G
        have hadd : addOf (commToPointwise G) = G.toMonObj.mul := by
          ext U s
          let p := (presheafProductSectionsEquiv F F U) s
          let _ := commGroupAt G U
          change p.1 + p.2 = presheafAdditionAt G.toMonObj.mul U p.1 p.2
          rfl
        have hneg : negOf (commToPointwise G) = G.inv := by
          ext U s
          let _ := commGroupAt G U
          change -s = presheafNegationAt G.inv U s
          rfl
        have hzero : zeroOf (commToPointwise G) = G.toMonObj.one := by
          ext U u
          cases u
          let _ := commGroupAt G U
          change (0 : Sections F U) = presheafZeroAt G.toMonObj.one U
          rfl
        apply comm_ext
        · exact MonObj.ext _ _ hadd
        · exact hneg }
  exact ⟨⟨pointwiseCommEquiv⟩, ⟨pointwiseOperationsEquiv⟩,
    ⟨pointwiseAdditionOnlyEquiv⟩,
    ⟨pointwiseCommEquiv.symm.trans pointwiseOperationsEquiv⟩,
    ⟨pointwiseCommEquiv.symm.trans pointwiseAdditionOnlyEquiv⟩,
    ⟨pointwiseOperationsEquiv.symm.trans pointwiseAdditionOnlyEquiv⟩⟩

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
