import Formalization.Books.Sheaves.Unit15.AlgebraicStructures
import Formalization.Books.Sheaves.Unit17.Sheafification

/-!
# Sheaves on Spaces, Chapter 17, Section 3: Sheafification of presheaves of
algebraic structures

The source span is `books/sheaves.tex:1778-1820`.  The category-valued
presheaf and the underlying set-valued presheaf are the canonical objects
from Chapter 5.  The existence theorem records the source's two properties:
the underlying sheaf is the ordinary sheafification, and maps to a sheaf
factor uniquely through the chosen algebraic sheafification.
-/

namespace Formalization.Books.Sheaves.Unit17

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Formalization.Books.Sheaves.Unit05
open Formalization.Books.Sheaves.Unit15

universe u v

noncomputable section

/-! ## The source-facing existence package -/

/-- A candidate sheafification of a presheaf valued in an algebraic category.

The underlying isomorphism identifies the underlying sheaf with ordinary
sheafification, and `underlying_unit` records that this identification is
the one induced by the algebraic unit rather than an unrelated isomorphism. -/
structure AlgebraicSheafificationData
    {C : Type u} [Category.{v} C] (U : C ⥤ Type v)
    [AlgebraicStructureType C U] {X : TopCat.{v}}
    (F : PresheafWithValues X C) where
  sheaf : TopCat.Sheaf C X
  unit : F ⟶ sheaf.presheaf
  underlying_iso :
    underlyingPresheaf U sheaf.presheaf ≅
      (sheafification (underlyingPresheaf U F)).presheaf
  underlying_unit :
    underlyingPresheafMorphism U unit ≫ underlying_iso.hom =
      sheafificationUnit (underlyingPresheaf U F)

/-- The chosen algebraic sheafification object. -/
abbrev algebraicSheafification
    {C : Type u} [Category.{v} C] (U : C ⥤ Type v)
    [AlgebraicStructureType C U] {X : TopCat.{v}}
    {F : PresheafWithValues X C}
    (D : AlgebraicSheafificationData U F) : TopCat.Sheaf C X :=
  D.sheaf

/-- The chosen unit into the algebraic sheafification. -/
abbrev algebraicSheafificationUnit
    {C : Type u} [Category.{v} C] (U : C ⥤ Type v)
    [AlgebraicStructureType C U] {X : TopCat.{v}}
    {F : PresheafWithValues X C}
    (D : AlgebraicSheafificationData U F) : F ⟶
      (algebraicSheafification U D).presheaf :=
  D.unit

/-- Existence and the universal factorization property for algebraic
sheafification. -/
theorem exists_algebraicSheafification
    {C : Type u} [Category.{v} C] (U : C ⥤ Type v)
    [AlgebraicStructureType C U] {X : TopCat.{v}}
    (F : PresheafWithValues X C) :
    ∃ D : AlgebraicSheafificationData U F,
      ∀ (G : TopCat.Sheaf C X) (φ : F ⟶ G.presheaf),
        ∃! ψ : D.sheaf ⟶ G, D.unit ≫ ψ.1 = φ := by
  let J := Opens.grothendieckTopology X
  let FD : C → C → Type v :=
    fun A B => {f : U.obj A ⟶ U.obj B // ∃ g : A ⟶ B, U.map g = f}
  let _ : ∀ A B, FunLike (FD A B) (U.obj A) (U.obj B) :=
    fun A B => ⟨fun f => f.1, fun f g h => Subtype.ext (by
      apply ConcreteCategory.ext
      apply TypeCat.Fun.ext
      exact h)⟩
  let _ : ConcreteCategory C FD := {
    hom := fun f => ⟨U.map f, ⟨f, rfl⟩⟩
    ofHom := fun f => Classical.choose f.2
    hom_ofHom := by
      intro A B f
      apply Subtype.ext
      apply ConcreteCategory.ext
      apply TypeCat.Fun.ext
      exact congrArg TypeCat.Fun.toFun
        (congrArg (ConcreteCategory.hom (C := Type v)) (Classical.choose_spec f.2))
    ofHom_hom := by
      intro A B f
      apply U.map_injective
      apply ConcreteCategory.ext
      apply TypeCat.Fun.ext
      exact congrArg TypeCat.Fun.toFun
        (congrArg (ConcreteCategory.hom (C := Type v))
          (Classical.choose_spec (show ∃ g : A ⟶ B, U.map g = U.map f from ⟨f, rfl⟩)))
    id_apply := by
      intro A x
      change U.map (𝟙 A) x = x
      simp
    comp_apply := by
      intro A B E f g x
      change U.map (f ≫ g) x = U.map g (U.map f x)
      rw [U.map_comp]
      rfl
  }
  let S : TopCat.Sheaf C X :=
    (CategoryTheory.presheafToSheaf J C).obj F
  let P := underlyingPresheaf U F
  let G : TopCat.Sheaf (Type v) X :=
    ⟨underlyingPresheaf U S.presheaf,
      (TopCat.Presheaf.isSheaf_iff_isSheaf_comp U S.presheaf).mp S.property⟩
  let H : TopCat.Sheaf (Type v) X :=
    (CategoryTheory.presheafToSheaf J (Type v)).obj P
  let p := CategoryTheory.sheafifyLift J (sheafificationUnit P)
    (sheafification_isSheaf P)
  let q := sheafificationLift P H (CategoryTheory.toSheafify J P)
  have hp : CategoryTheory.toSheafify J P ≫ p = sheafificationUnit P := by
    exact CategoryTheory.toSheafify_sheafifyLift _ _ _
  have hq : sheafificationUnit P ≫ q = CategoryTheory.toSheafify J P := by
    exact sheafificationUnit_comp_lift P H (CategoryTheory.toSheafify J P)
  have hqp : q ≫ p = 𝟙 _ := by
    have h₁ : q ≫ p =
        sheafificationLift P (sheafification P) (sheafificationUnit P) := by
      apply sheafificationLift_unique P (sheafification P) (sheafificationUnit P)
      rw [← Category.assoc, hq, hp]
    have h₂ : (𝟙 _) =
        sheafificationLift P (sheafification P) (sheafificationUnit P) :=
      sheafificationLift_unique P (sheafification P) (sheafificationUnit P) (𝟙 _)
        (by simp)
    exact h₁.trans h₂.symm
  have hpq : p ≫ q = 𝟙 _ := by
    apply CategoryTheory.sheafify_hom_ext J (p ≫ q) (𝟙 _) H.property
    rw [← Category.assoc, hp, hq]
    simp
  let eLocal : H.presheaf ≅ (sheafification P).presheaf :=
    { hom := p, inv := q, hom_inv_id := hpq, inv_hom_id := hqp }
  let e := CategoryTheory.presheafToSheafCompComposeAndSheafifyIso J U
  let eF := e.app F
  let eK0 := (CategoryTheory.sheafToPresheaf J (Type v)).mapIso eF
  let iG := CategoryTheory.isoSheafify J G.property
  let iG' : G.presheaf ≅
      (CategoryTheory.sheafToPresheaf J (Type v)).obj
        ((CategoryTheory.presheafToSheaf J (Type v)).obj G.presheaf) := by
    exact iG
  let eGH : G.presheaf ≅ H.presheaf := by
    simpa [P, G, H,
      Formalization.Books.Sheaves.Unit05.underlyingPresheaf,
      S, CategoryTheory.Sheaf.composeAndSheafify] using
      (iG'.trans eK0)
  let eFinal : G.presheaf ≅ (sheafification P).presheaf :=
    eGH ≪≫ eLocal
  have hGH :
      underlyingPresheafMorphism U (CategoryTheory.toSheafify J F) ≫ eGH.hom =
        CategoryTheory.toSheafify J P := by
    change underlyingPresheafMorphism U (CategoryTheory.toSheafify J F) ≫
      iG'.hom ≫ eK0.hom = _
    change (underlyingPresheafMorphism U (CategoryTheory.toSheafify J F) ≫
          CategoryTheory.toSheafify J G.presheaf) ≫
        (CategoryTheory.sheafToPresheaf J (Type v)).map eF.hom = _
    rw [CategoryTheory.toSheafify_naturality]
    rw [Category.assoc]
    have hα := e.inv_hom_id_app F
    change CategoryTheory.toSheafify J
        (F ⋙ U) ≫
        (CategoryTheory.sheafToPresheaf J (Type v)).map (e.inv.app F) ≫
          (CategoryTheory.sheafToPresheaf J (Type v)).map (e.hom.app F) =
      CategoryTheory.toSheafify J (F ⋙ U)
    rw [← (CategoryTheory.sheafToPresheaf J (Type v)).map_comp,
      hα]
    simp
  have hcomp :
      underlyingPresheafMorphism U (CategoryTheory.toSheafify J F) ≫ eFinal.hom =
        sheafificationUnit P := by
    change underlyingPresheafMorphism U (CategoryTheory.toSheafify J F) ≫
      eGH.hom ≫ eLocal.hom = _
    rw [← Category.assoc, hGH, hp]
  refine ⟨
    { sheaf := S
      unit := CategoryTheory.toSheafify J F
      underlying_iso := eFinal
      underlying_unit := hcomp }, ?_⟩
  intro G' φ
  let A := CategoryTheory.sheafificationAdjunction J C
  let ψ : S ⟶ G' := (A.homEquiv F G').symm φ
  refine ⟨ψ, ?_, ?_⟩
  · change CategoryTheory.toSheafify J F ≫ ψ.hom = φ
    exact (A.homEquiv F G').apply_symm_apply φ
  · intro ψ' hψ'
    apply (A.homEquiv F G').injective
    change CategoryTheory.toSheafify J F ≫ ψ'.hom =
      CategoryTheory.toSheafify J F ≫ ψ.hom
    have hψ : CategoryTheory.toSheafify J F ≫ ψ.hom = φ := by
      exact (A.homEquiv F G').apply_symm_apply φ
    exact hψ'.trans hψ.symm

/-- The underlying sheaf assertion in the source, exposed independently for
users that do not need the universal property. -/
theorem algebraicSheafification_underlying_iso
    {C : Type u} [Category.{v} C] (U : C ⥤ Type v)
    [AlgebraicStructureType C U] {X : TopCat.{v}}
    {F : PresheafWithValues X C}
    (D : AlgebraicSheafificationData U F) :
    Nonempty
      (underlyingPresheaf U D.sheaf.presheaf ≅
        (sheafification (underlyingPresheaf U F)).presheaf) := by
  exact ⟨D.underlying_iso⟩

end

end Formalization.Books.Sheaves.Unit17
