import Formalization.Books.Categories.Unit31.TwoFibreProducts
import Formalization.Books.Categories.Unit35.CategoriesFibredInGroupoids
import Mathlib.CategoryTheory.Equivalence

/-!
# Categories, Chapter 44: Categories of dotted arrows

This file formalizes the source's categories of dotted arrows in a strict
locally groupoidal bicategory.  The comparison 2-morphisms which the source
calls 2-isomorphisms are stored with explicit `IsIso` fields, following the
fixed-square and 2-fibre-product interfaces in the preceding chapters.
-/

namespace Formalization.Books.Categories.Unit44

open CategoryTheory
open CategoryTheory.Bicategory
open CategoryTheory.Functor
open Formalization.Books.Categories.Unit31
open Formalization.Books.Categories.Unit31.TwoCommutativeDiagram

universe w v u

/-! ## The dotted-arrow category -/

/-- A solid square together with its chosen invertible comparison 2-morphism.

The fields correspond to
`S --x--> X`, `S --j--> T`, `X --f--> Y`, and `T --y--> Y`, with
`gamma : j ≫ y ⟶ x ≫ f`.
-/
structure DottedArrowSquare (C : Type u) [Bicategory.{w, v} C]
    [Bicategory.Strict C] where
  objS : C
  objX : C
  objT : C
  objY : C
  j : objS ⟶ objT
  x : objS ⟶ objX
  f : objX ⟶ objY
  y : objT ⟶ objY
  gamma : j ≫ y ⟶ x ≫ f
  gamma_isIso : IsIso gamma

attribute [instance] DottedArrowSquare.gamma_isIso

/-- An object of the category of dotted arrows for a fixed solid square. -/
structure DottedArrow {C : Type u} [Bicategory.{w, v} C]
    [Bicategory.Strict C] (D : DottedArrowSquare C) where
  /-- The dotted 1-morphism `a : T ⟶ X`. -/
  a : D.objT ⟶ D.objX
  /-- The comparison `a ∘ j ⟶ x`. -/
  alpha : D.j ≫ a ⟶ D.x
  /-- The comparison `y ⟶ f ∘ a`. -/
  beta : D.y ⟶ a ≫ D.f
  alpha_isIso : IsIso alpha
  beta_isIso : IsIso beta
  /-- The defining 2-commutativity identity for the dotted arrow. -/
  commutes : D.gamma =
    (Bicategory.whiskerLeft D.j beta) ≫
      strictAssocInv D.j a D.f ≫
      Bicategory.whiskerRight alpha D.f

attribute [instance] DottedArrow.alpha_isIso DottedArrow.beta_isIso

namespace DottedArrow

/-- A morphism of dotted arrows, with its two naturality identities. -/
structure Hom {C : Type u} [Bicategory.{w, v} C]
    [Bicategory.Strict C] {D : DottedArrowSquare C}
    (A A' : DottedArrow D) where
  /-- The 2-arrow `theta : a ⟶ a'`. -/
  hom : A.a ⟶ A'.a
  /-- `alpha = alpha' ∘ (theta ⋆ id_j)`, in strict bicategory notation. -/
  alpha_naturality :
    Bicategory.whiskerLeft D.j hom ≫ A'.alpha = A.alpha
  /-- `beta' = (id_f ⋆ theta) ∘ beta`, in strict bicategory notation. -/
  beta_naturality :
    A.beta ≫ Bicategory.whiskerRight hom D.f = A'.beta

@[ext]
lemma Hom.ext {C : Type u} [Bicategory.{w, v} C]
    [Bicategory.Strict C] {D : DottedArrowSquare C}
    {A A' : DottedArrow D} {h k : Hom A A'} (e : h.hom = k.hom) : h = k := by
  cases h
  cases k
  cases e
  rfl

/-- The identity morphism of a dotted arrow. -/
def Hom.id {C : Type u} [Bicategory.{w, v} C]
    [Bicategory.Strict C] {D : DottedArrowSquare C} (A : DottedArrow D) :
    Hom A A where
  hom := 𝟙 A.a
  alpha_naturality := by simp
  beta_naturality := by simp

/-- Composition of morphisms of dotted arrows. -/
def Hom.comp {C : Type u} [Bicategory.{w, v} C]
    [Bicategory.Strict C] {D : DottedArrowSquare C}
    {A A' A'' : DottedArrow D} (h : Hom A A') (k : Hom A' A'') :
    Hom A A'' where
  hom := h.hom ≫ k.hom
  alpha_naturality := by
    rw [Bicategory.whiskerLeft_comp, Category.assoc,
      k.alpha_naturality, h.alpha_naturality]
  beta_naturality := by
    rw [Bicategory.comp_whiskerRight, ← Category.assoc,
      h.beta_naturality, k.beta_naturality]

/- The category laws use only the whiskering functoriality already supplied by
the bicategory interface. -/
instance category {C : Type u} [Bicategory.{w, v} C]
    [Bicategory.Strict C] (D : DottedArrowSquare C) : Category (DottedArrow D) where
  Hom A A' := Hom A A'
  id A := Hom.id A
  comp h k := Hom.comp h k
  id_comp := by
    intro A A' h
    apply Hom.ext
    simp [Hom.comp, Hom.id]
  comp_id := by
    intro A A' h
    apply Hom.ext
    simp [Hom.comp, Hom.id]
  assoc := by
    intro A A' A'' A''' h k l
    apply Hom.ext
    simp [Hom.comp, Category.assoc]

end DottedArrow

private lemma dottedArrow_ext_fields
    {C : Type u} [Bicategory.{w, v} C] [Bicategory.Strict C]
    {D : DottedArrowSquare C} {A A' : DottedArrow D}
    (ha : A.a = A'.a) (hα : HEq A.alpha A'.alpha)
    (hβ : HEq A.beta A'.beta) : A = A' := by
  cases A
  cases A'
  cases ha
  cases hα
  cases hβ
  rfl

private lemma dottedArrow_eqToHom_hom
    {C : Type u} [Bicategory.{w, v} C] [Bicategory.Strict C]
    {D : DottedArrowSquare C} {A A' : DottedArrow D} (h : A = A') :
    (eqToHom h : A ⟶ A').hom =
      eqToHom (congrArg (fun X : DottedArrow D => X.a) h) := by
  cases h
  rfl

private lemma dottedArrow_comp_hom
    {C : Type u} [Bicategory.{w, v} C] [Bicategory.Strict C]
    {D : DottedArrowSquare C} {A A' A'' : DottedArrow D}
    (f : DottedArrow.Hom A A') (g : DottedArrow.Hom A' A'') :
    (DottedArrow.Hom.comp f g).hom = f.hom ≫ g.hom := rfl

/-- The category of dotted arrows for `D` (the category instance is induced by
the source and target structures above). -/
abbrev DottedArrowCategory {C : Type u} [Bicategory.{w, v} C]
    [Bicategory.Strict C] (D : DottedArrowSquare C) := DottedArrow D

/-- In a locally groupoidal bicategory, the category of dotted arrows is a
groupoid. -/
theorem dottedArrowCategory_isGroupoid
    {C : Type u} [Bicategory.{w, v} C] [Bicategory.Strict C]
    (hC : Bicategory.IsLocallyGroupoid C)
    (D : DottedArrowSquare C) : IsGroupoid (DottedArrowCategory D) := by
  constructor
  intro A A' h
  let _ : IsGroupoid (D.objT ⟶ D.objX) := hC D.objT D.objX
  let e : A.a ≅ A'.a := asIso h.hom
  let hinv : DottedArrow.Hom A' A :=
    { hom := e.inv
      alpha_naturality := by
        rw [← h.alpha_naturality]
        rw [← Category.assoc, ← Bicategory.whiskerLeft_comp]
        simp [e]
      beta_naturality := by
        rw [← h.beta_naturality]
        rw [Category.assoc, ← Bicategory.comp_whiskerRight]
        simp [e] }
  exact ⟨⟨hinv, by
    apply DottedArrow.Hom.ext
    change h.hom ≫ e.inv = 𝟙 _
    exact e.hom_inv_id, by
    apply DottedArrow.Hom.ext
    change e.inv ≫ h.hom = 𝟙 _
    exact e.inv_hom_id⟩⟩

/-! ## Base change -/

/-- The fixed-square form of 2-cartesianness used by the base-change lemma.

This is the preceding chapter's final-object definition applied to the
displayed square, with the comparison oriented as `p ≫ g ⟶ q ≫ f`.
-/
def IsTwoCartesianSquare
    {C : Type u} [Bicategory.{w, v} C] [Bicategory.Strict C]
    (hC : Bicategory.IsLocallyGroupoid C)
    {xPrime xTarget yPrime yTarget : C}
    (p : xPrime ⟶ yPrime) (q : xPrime ⟶ xTarget)
    (f : xTarget ⟶ yTarget) (g : yPrime ⟶ yTarget)
    (phi : p ≫ g ⟶ q ≫ f)
    (hphi : IsIso phi) : Prop :=
  let D : TwoCommutativeDiagram g f :=
    { vertex := xPrime
      left := p
      right := q
      comparison := phi
      comparison_isIso := hphi }
  TwoCommutativeDiagram.IsFinalTwoCommutativeDiagram hC D

/-- All data in the base-change square of the source lemma. -/
structure BaseChangeData {C : Type u} [Bicategory.{w, v} C]
    [Bicategory.Strict C] (hC : Bicategory.IsLocallyGroupoid C) where
  objS : C
  objXp : C
  objX : C
  objT : C
  objYp : C
  objY : C
  j : objS ⟶ objT
  x' : objS ⟶ objXp
  p : objXp ⟶ objYp
  q : objXp ⟶ objX
  y' : objT ⟶ objYp
  g : objYp ⟶ objY
  f : objX ⟶ objY
  phi : p ≫ g ⟶ q ≫ f
  phi_isIso : IsIso phi
  right_cartesian : IsTwoCartesianSquare hC p q f g phi phi_isIso
  gamma' : j ≫ y' ⟶ x' ≫ p
  gamma'_isIso : IsIso gamma'

attribute [instance] BaseChangeData.phi_isIso BaseChangeData.gamma'_isIso

namespace BaseChangeData

/-- The comparison on the outer rectangle, with the strict associativity
transports made explicit in Mathlib's bicategory interface. -/
def gamma {C : Type u} [Bicategory.{w, v} C] [Bicategory.Strict C]
    {hC : Bicategory.IsLocallyGroupoid C} (B : BaseChangeData hC) :
    B.j ≫ (B.y' ≫ B.g) ⟶ (B.x' ≫ B.q) ≫ B.f :=
  strictAssocInv B.j B.y' B.g ≫
    Bicategory.whiskerRight B.gamma' B.g ≫
    strictAssocHom B.x' B.p B.g ≫
    Bicategory.whiskerLeft B.x' B.phi ≫
    strictAssocInv B.x' B.q B.f

theorem gamma_isIso {C : Type u} [Bicategory.{w, v} C]
    [Bicategory.Strict C] {hC : Bicategory.IsLocallyGroupoid C}
    (B : BaseChangeData hC) : IsIso B.gamma := by
  dsimp [gamma]
  infer_instance

attribute [instance] gamma_isIso

/-- The left square and the outer rectangle as dotted-arrow squares. -/
def leftSquare {C : Type u} [Bicategory.{w, v} C]
    [Bicategory.Strict C] {hC : Bicategory.IsLocallyGroupoid C}
    (B : BaseChangeData hC) : DottedArrowSquare C where
  objS := B.objS
  objX := B.objXp
  objT := B.objT
  objY := B.objYp
  j := B.j
  x := B.x'
  f := B.p
  y := B.y'
  gamma := B.gamma'
  gamma_isIso := B.gamma'_isIso

abbrev outerSquare {C : Type u} [Bicategory.{w, v} C]
    [Bicategory.Strict C] {hC : Bicategory.IsLocallyGroupoid C}
    (B : BaseChangeData hC) : DottedArrowSquare C where
  objS := B.objS
  objX := B.objX
  objT := B.objT
  objY := B.objY
  j := B.j
  x := B.x' ≫ B.q
  f := B.f
  y := B.y' ≫ B.g
  gamma := B.gamma
  gamma_isIso := gamma_isIso B

end BaseChangeData

/-- Base change along a 2-cartesian square gives an equivalence of dotted-arrow
categories. -/
theorem dottedArrow_baseChange_equivalence
    {C : Type u} [Bicategory.{w, v} C] [Bicategory.Strict C]
    {hC : Bicategory.IsLocallyGroupoid C} (B : BaseChangeData hC) :
    Nonempty
      (DottedArrowCategory (BaseChangeData.leftSquare B) ≌
        DottedArrowCategory (BaseChangeData.outerSquare B)) := by
  let forward : DottedArrowCategory (BaseChangeData.leftSquare B) ⥤
      DottedArrowCategory (BaseChangeData.outerSquare B) := {
    obj := fun A => by
      dsimp [BaseChangeData.leftSquare] at A ⊢
      exact
        { a := A.a ≫ B.q
          alpha := strictAssocInv B.j A.a B.q ≫
            Bicategory.whiskerRight A.alpha B.q
          beta := Bicategory.whiskerRight A.beta B.g ≫
            strictAssocHom A.a B.p B.g ≫
            Bicategory.whiskerLeft A.a B.phi ≫
            strictAssocInv A.a B.q B.f
          alpha_isIso := by infer_instance
          beta_isIso := by infer_instance
          commutes := by
            dsimp [BaseChangeData.gamma]
            have hA := A.commutes
            dsimp [BaseChangeData.leftSquare] at hA
            let hX : strictAssocHom B.x' B.q B.f =
                (Bicategory.associator B.x' B.q B.f).hom := by
              simpa [strictAssocHom] using congrArg Iso.hom
                (Bicategory.Strict.associator_eqToIso B.x' B.q B.f) |>.symm
            let hJY : strictAssocInv B.j B.y' B.g =
                (Bicategory.associator B.j B.y' B.g).inv := by
              simpa [strictAssocInv] using congrArg Iso.inv
                (Bicategory.Strict.associator_eqToIso B.j B.y' B.g) |>.symm
            let hJaq : strictAssocInv B.j (A.a ≫ B.q) B.f =
                (Bicategory.associator B.j (A.a ≫ B.q) B.f).inv := by
              simpa [strictAssocInv] using congrArg Iso.inv
                (Bicategory.Strict.associator_eqToIso B.j (A.a ≫ B.q) B.f) |>.symm
            let hJaq' : strictAssocInv B.j A.a B.q =
                (Bicategory.associator B.j A.a B.q).inv := by
              simpa [strictAssocInv] using congrArg Iso.inv
                (Bicategory.Strict.associator_eqToIso B.j A.a B.q) |>.symm
            let hAq : strictAssocInv A.a B.q B.f =
                (Bicategory.associator A.a B.q B.f).inv := by
              simpa [strictAssocInv] using congrArg Iso.inv
                (Bicategory.Strict.associator_eqToIso A.a B.q B.f) |>.symm
            let hApg : strictAssocHom A.a B.p B.g =
                (Bicategory.associator A.a B.p B.g).hom := by
              simpa [strictAssocHom] using congrArg Iso.hom
                (Bicategory.Strict.associator_eqToIso A.a B.p B.g) |>.symm
            let hXpg : strictAssocHom B.x' B.p B.g =
                (Bicategory.associator B.x' B.p B.g).hom := by
              simpa [strictAssocHom] using congrArg Iso.hom
                (Bicategory.Strict.associator_eqToIso B.x' B.p B.g) |>.symm
            have hβassoc :
                (Bicategory.associator B.j B.y' B.g).inv ≫
                    (Bicategory.whiskerLeft B.j A.beta) ▷ B.g =
                  Bicategory.whiskerLeft B.j (A.beta ▷ B.g) ≫
                    (Bicategory.associator B.j (A.a ≫ B.p) B.g).inv := by
              apply (cancel_mono
                (Bicategory.associator B.j (A.a ≫ B.p) B.g).hom).1
              simp only [Category.assoc]
              rw [Bicategory.whisker_assoc_symm]
              simp only [Category.assoc, Iso.inv_hom_id_assoc, Iso.hom_inv_id_assoc]
            letI : IsIso (strictAssocHom B.x' B.q B.f) := by
              dsimp [strictAssocHom]
              infer_instance
            apply (cancel_mono (strictAssocHom B.x' B.q B.f)).1
            simp only [Category.assoc]
            rw [hX, hJY, hJaq, hJaq', hAq, hApg, hXpg]
            have hAg := congrArg
              (fun t => Bicategory.whiskerRight t B.g) hA
            rw [hAg]
            rw [Bicategory.comp_whiskerRight]
            simp only [Bicategory.whiskerLeft_comp, Category.assoc]
            have hβtail :
                ((Bicategory.associator B.j B.y' B.g).inv ≫
                    (Bicategory.whiskerLeft B.j A.beta) ▷ B.g) ≫
                    ((strictAssocInv B.j A.a B.p ≫ A.alpha ▷ B.p) ▷ B.g ≫
                      (Bicategory.associator B.x' B.p B.g).hom ≫
                      B.x' ◁ B.phi ≫ strictAssocInv B.x' B.q B.f ≫
                      (Bicategory.associator B.x' B.q B.f).hom) =
                  (Bicategory.whiskerLeft B.j (A.beta ▷ B.g) ≫
                    (Bicategory.associator B.j (A.a ≫ B.p) B.g).inv) ≫
                    ((strictAssocInv B.j A.a B.p ≫ A.alpha ▷ B.p) ▷ B.g ≫
                      (Bicategory.associator B.x' B.p B.g).hom ≫
                      B.x' ◁ B.phi ≫ strictAssocInv B.x' B.q B.f ≫
                      (Bicategory.associator B.x' B.q B.f).hom) := by
              calc
                _ = ((Bicategory.associator B.j B.y' B.g).inv ≫
                    (Bicategory.whiskerLeft B.j A.beta) ▷ B.g) ≫
                    ((strictAssocInv B.j A.a B.p ≫ A.alpha ▷ B.p) ▷ B.g ≫
                      (Bicategory.associator B.x' B.p B.g).hom ≫
                      B.x' ◁ B.phi ≫ strictAssocInv B.x' B.q B.f ≫
                      (Bicategory.associator B.x' B.q B.f).hom) := by
                        simp only [Category.assoc]
                _ = (Bicategory.whiskerLeft B.j (A.beta ▷ B.g) ≫
                    (Bicategory.associator B.j (A.a ≫ B.p) B.g).inv) ≫
                    ((strictAssocInv B.j A.a B.p ≫ A.alpha ▷ B.p) ▷ B.g ≫
                      (Bicategory.associator B.x' B.p B.g).hom ≫
                      B.x' ◁ B.phi ≫ strictAssocInv B.x' B.q B.f ≫
                      (Bicategory.associator B.x' B.q B.f).hom) := by
                        rw [hβassoc]
            calc
              _ = (Bicategory.whiskerLeft B.j (A.beta ▷ B.g) ≫
                    (Bicategory.associator B.j (A.a ≫ B.p) B.g).inv) ≫
                    ((strictAssocInv B.j A.a B.p ≫ A.alpha ▷ B.p) ▷ B.g ≫
                      (Bicategory.associator B.x' B.p B.g).hom ≫
                      B.x' ◁ B.phi ≫ strictAssocInv B.x' B.q B.f ≫
                      (Bicategory.associator B.x' B.q B.f).hom) := by
                        simpa only [Category.assoc] using hβtail
              _ = _ := by
                letI : IsIso (Bicategory.whiskerLeft B.j (A.beta ▷ B.g)) := by
                  infer_instance
                simp only [Category.assoc]
                apply (cancel_epi
                  (Bicategory.whiskerLeft B.j (A.beta ▷ B.g))).2
                simp only [Category.assoc]
                have hXq : strictAssocInv B.x' B.q B.f =
                    (Bicategory.associator B.x' B.q B.f).inv := by
                  simpa [strictAssocInv] using congrArg Iso.inv
                    (Bicategory.Strict.associator_eqToIso B.x' B.q B.f) |>.symm
                have hJp : strictAssocInv B.j A.a B.p =
                    (Bicategory.associator B.j A.a B.p).inv := by
                  simpa [strictAssocInv] using congrArg Iso.inv
                    (Bicategory.Strict.associator_eqToIso B.j A.a B.p) |>.symm
                rw [hXq, hJp]
                simp only [← Category.assoc]
                letI : IsIso (Bicategory.associator B.x' B.q B.f).hom := by
                  infer_instance
                rw [cancel_mono (Bicategory.associator B.x' B.q B.f).hom]
                simp only [Bicategory.whiskerLeft_comp,
                  Bicategory.comp_whiskerRight, Category.assoc]
                rw [Bicategory.associator_naturality_left_assoc A.alpha B.p B.g]
                rw [← Bicategory.whisker_exchange_assoc]
                rw [Bicategory.whiskerRight_comp]
                simp only [Category.assoc, Iso.hom_inv_id_assoc]
                simp only [Category.assoc, Iso.hom_inv_id]
                letI : IsIso (Bicategory.whiskerRight
                    (Bicategory.whiskerRight A.alpha B.q) B.f) := by
                  infer_instance
                simp only [← Category.assoc]
                simp only [Category.comp_id]
                rw [cancel_mono
                  (Bicategory.whiskerRight
                    (Bicategory.whiskerRight A.alpha B.q) B.f)]
                simp only [Category.assoc]
                rw [Bicategory.pentagon_inv_inv_hom_hom_inv_assoc B.j A.a B.p B.g]
                rw [← Bicategory.associator_inv_naturality_right_assoc]
                rw [Bicategory.pentagon_inv] }
    map := fun {A A'} H => by
      change DottedArrow (BaseChangeData.leftSquare B) at A A'
      change DottedArrow.Hom A A' at H
      dsimp [BaseChangeData.leftSquare] at A A' H ⊢
      exact
        { hom := Bicategory.whiskerRight H.hom B.q
          alpha_naturality := by
            dsimp
            have hA : strictAssocInv B.j A.a B.q =
                (Bicategory.associator B.j A.a B.q).inv := by
              simpa [strictAssocInv] using congrArg Iso.inv
                (Bicategory.Strict.associator_eqToIso B.j A.a B.q) |>.symm
            have hA' : strictAssocInv B.j A'.a B.q =
                (Bicategory.associator B.j A'.a B.q).inv := by
              simpa [strictAssocInv] using congrArg Iso.inv
                (Bicategory.Strict.associator_eqToIso B.j A'.a B.q) |>.symm
            rw [hA']
            rw [Bicategory.whisker_assoc_symm]
            simp only [Category.assoc, Iso.hom_inv_id_assoc]
            rw [← Bicategory.comp_whiskerRight, H.alpha_naturality]
            rw [hA]
          beta_naturality := by
            dsimp
            have hA : strictAssocInv A.a B.q B.f =
                (Bicategory.associator A.a B.q B.f).inv := by
              simpa [strictAssocInv] using congrArg Iso.inv
                (Bicategory.Strict.associator_eqToIso A.a B.q B.f) |>.symm
            have hA' : strictAssocInv A'.a B.q B.f =
                (Bicategory.associator A'.a B.q B.f).inv := by
              simpa [strictAssocInv] using congrArg Iso.inv
                (Bicategory.Strict.associator_eqToIso A'.a B.q B.f) |>.symm
            simp only [Category.assoc]
            rw [hA, hA']
            rw [Bicategory.whiskerRight_comp_symm]
            simp only [Category.assoc, Iso.inv_hom_id_assoc]
            rw [← Category.assoc (Bicategory.whiskerLeft A.a B.phi)
              (Bicategory.whiskerRight H.hom (B.q ≫ B.f))
              (Bicategory.associator A'.a B.q B.f).inv]
            rw [Bicategory.whisker_exchange H.hom B.phi]
            have hApg : strictAssocHom A.a B.p B.g =
                (Bicategory.associator A.a B.p B.g).hom := by
              simpa [strictAssocHom] using congrArg Iso.hom
                (Bicategory.Strict.associator_eqToIso A.a B.p B.g) |>.symm
            have hApg' : strictAssocHom A'.a B.p B.g =
                (Bicategory.associator A'.a B.p B.g).hom := by
              simpa [strictAssocHom] using congrArg Iso.hom
                (Bicategory.Strict.associator_eqToIso A'.a B.p B.g) |>.symm
            have hnat :
                strictAssocHom A.a B.p B.g ≫
                    Bicategory.whiskerRight H.hom (B.p ≫ B.g) ≫
                    Bicategory.whiskerLeft A'.a B.phi =
                  (Bicategory.whiskerRight H.hom B.p) ▷ B.g ≫
                    strictAssocHom A'.a B.p B.g ≫
                    Bicategory.whiskerLeft A'.a B.phi := by
              rw [hApg, hApg']
              rw [← Bicategory.associator_naturality_left_assoc]
            calc
              _ = A.beta ▷ B.g ≫
                  (strictAssocHom A.a B.p B.g ≫
                    Bicategory.whiskerRight H.hom (B.p ≫ B.g) ≫
                    Bicategory.whiskerLeft A'.a B.phi) ≫
                    (Bicategory.associator A'.a B.q B.f).inv := by
                      simp only [Category.assoc]
              _ = A.beta ▷ B.g ≫
                  ((Bicategory.whiskerRight H.hom B.p) ▷ B.g ≫
                    strictAssocHom A'.a B.p B.g ≫
                    Bicategory.whiskerLeft A'.a B.phi) ≫
                    (Bicategory.associator A'.a B.q B.f).inv := by
                      rw [hnat]
              _ = (A.beta ≫ Bicategory.whiskerRight H.hom B.p) ▷ B.g ≫
                  (strictAssocHom A'.a B.p B.g ≫
                    Bicategory.whiskerLeft A'.a B.phi) ≫
                    (Bicategory.associator A'.a B.q B.f).inv := by
                      rw [Bicategory.comp_whiskerRight]
                      simp only [Category.assoc]
              _ = A'.beta ▷ B.g ≫
                  (strictAssocHom A'.a B.p B.g ≫
                    Bicategory.whiskerLeft A'.a B.phi) ≫
                    (Bicategory.associator A'.a B.q B.f).inv := by
                      rw [H.beta_naturality]
              _ = _ := by simp }
    map_id := by
      intro A
      change DottedArrow (BaseChangeData.leftSquare B) at A
      dsimp [BaseChangeData.leftSquare, BaseChangeData.outerSquare] at A ⊢
      apply DottedArrow.Hom.ext
      change (𝟙 A.a) ▷ B.q = 𝟙 (A.a ≫ B.q)
      simp
    map_comp := by
      intro A A' A'' H K
      change DottedArrow (BaseChangeData.leftSquare B) at A A' A''
      change DottedArrow.Hom A A' at H
      change DottedArrow.Hom A' A'' at K
      dsimp [BaseChangeData.leftSquare, BaseChangeData.outerSquare] at A A' A'' H K ⊢
      apply DottedArrow.Hom.ext
      change (H.hom ≫ K.hom) ▷ B.q =
        (H.hom ▷ B.q) ≫ (K.hom ▷ B.q)
      rw [Bicategory.comp_whiskerRight] }
  let P : TwoCommutativeDiagram B.g B.f :=
    { vertex := B.objXp
      left := B.p
      right := B.q
      comparison := B.phi
      comparison_isIso := B.phi_isIso }
  have hP : TwoCommutativeDiagram.IsFinalTwoCommutativeDiagram hC P := by
    simpa [P, IsTwoCartesianSquare] using B.right_cartesian
  let outerDiagram :
      DottedArrowCategory (BaseChangeData.outerSquare B) →
        TwoCommutativeDiagram B.g B.f := fun A =>
    { vertex := B.objT
      left := B.y'
      right := A.a
      comparison := A.beta
      comparison_isIso := A.beta_isIso }
  let liftHom : ∀ A : DottedArrowCategory (BaseChangeData.outerSquare B),
      outerDiagram A ⟶₂ P := fun A =>
    Classical.choice ((hP (outerDiagram A)).1)
  let sourceDiagram : TwoCommutativeDiagram B.g B.f :=
    { vertex := B.objS
      left := B.j ≫ B.y'
      right := B.x' ≫ B.q
      comparison := strictAssocHom B.j B.y' B.g ≫ B.gamma
      comparison_isIso := by infer_instance }
  let sourceToOuter : ∀ A : DottedArrowCategory (BaseChangeData.outerSquare B),
      sourceDiagram ⟶₂ outerDiagram A := fun A =>
    { vertex := B.j
      left := 𝟙 (B.j ≫ B.y')
      right := inv A.alpha
      commutes := by
        dsimp [sourceDiagram, outerDiagram]
        have hA := A.commutes
        dsimp [BaseChangeData.outerSquare] at hA
        rw [hA]
        simp only [Category.assoc]
        rw [← Bicategory.comp_whiskerRight]
        simp [Category.assoc] }
  let canonical : sourceDiagram ⟶₂ P :=
    { vertex := B.x'
      left := B.gamma'
      right := 𝟙 (B.x' ≫ B.q)
      commutes := by
        dsimp [sourceDiagram, P, BaseChangeData.gamma]
        simp [strictAssocHom, strictAssocInv] }
  let liftToSource : ∀ A : DottedArrowCategory (BaseChangeData.outerSquare B),
      sourceDiagram ⟶₂ P := fun A =>
    { vertex := B.j ≫ (liftHom A).vertex
      left := B.j ◁ (liftHom A).left ≫
        strictAssocInv B.j (liftHom A).vertex B.p
      right := inv A.alpha ≫ B.j ◁ (liftHom A).right ≫
        strictAssocInv B.j (liftHom A).vertex B.q
      commutes := by
        have hcomp :=
          (TwoCommutativeDiagram.Hom.comp (sourceToOuter A) (liftHom A)).commutes
        simpa [sourceToOuter, outerDiagram, P, sourceDiagram,
          TwoCommutativeDiagram.Hom.comp,
          Category.assoc, Category.id_comp] using hcomp }
  let comparisonHom : ∀ A : DottedArrowCategory (BaseChangeData.outerSquare B),
      TwoCommutativeDiagram.TwoHom (liftToSource A) canonical := fun A =>
    Classical.choose ((hP sourceDiagram).2 (liftToSource A) canonical)
  let inverseObj : DottedArrowCategory (BaseChangeData.outerSquare B) →
      DottedArrowCategory (BaseChangeData.leftSquare B) := fun A => by
    let h₀ := liftHom A
    let η₀ := comparisonHom A
    let _ : IsGroupoid (B.objS ⟶ B.objXp) := hC B.objS B.objXp
    let _ : IsGroupoid (B.objT ⟶ B.objYp) := hC B.objT B.objYp
    dsimp [BaseChangeData.leftSquare]
    exact
      { a := h₀.vertex
        alpha := η₀.vertex
        beta := h₀.left
        alpha_isIso := by
          letI := hC B.objS B.objXp
          infer_instance
        beta_isIso := by
          letI := hC B.objT B.objYp
          infer_instance
        commutes := by
          dsimp [h₀, η₀]
          have hη := (comparisonHom A).left
          dsimp [comparisonHom, liftToSource, sourceToOuter, canonical, P,
            outerDiagram,
            TwoCommutativeDiagram.Hom.comp] at hη
          simp [Category.assoc] at hη
          simpa [P, Bicategory.id_whiskerRight,
            Bicategory.Strict.rightUnitor_eqToIso, Category.id_comp,
            Category.assoc] using hη.symm }
  sorry

/-! ## Composition -/

/-- The data of the composable solid diagram in the composition lemma. -/
structure CompositionData {C : Type u} [Bicategory.{w, v} C]
    [Bicategory.Strict C] where
  objS : C
  objX : C
  objY : C
  objZ : C
  objT : C
  j : objS ⟶ objT
  x : objS ⟶ objX
  f : objX ⟶ objY
  g : objY ⟶ objZ
  z : objT ⟶ objZ
  gamma : j ≫ z ⟶ (x ≫ f) ≫ g
  gamma_isIso : IsIso gamma

attribute [instance] CompositionData.gamma_isIso

namespace CompositionData

/-- The outer rectangle in the composition lemma. -/
abbrev outerSquare {C : Type u} [Bicategory.{w, v} C]
    [Bicategory.Strict C] (Q : CompositionData (C := C)) : DottedArrowSquare C where
  objS := Q.objS
  objX := Q.objX
  objT := Q.objT
  objY := Q.objZ
  j := Q.j
  x := Q.x
  f := Q.f ≫ Q.g
  y := Q.z
  gamma := Q.gamma ≫ strictAssocHom Q.x Q.f Q.g
  gamma_isIso := by
    apply IsIso.comp_isIso'
    · exact Q.gamma_isIso
    · dsimp [strictAssocHom]
      infer_instance

/-- The solid square used for the category `D'` in the composition lemma. -/
abbrev innerSquare {C : Type u} [Bicategory.{w, v} C]
    [Bicategory.Strict C] (Q : CompositionData (C := C)) : DottedArrowSquare C where
  objS := Q.objS
  objX := Q.objY
  objT := Q.objT
  objY := Q.objZ
  j := Q.j
  x := Q.x ≫ Q.f
  f := Q.g
  y := Q.z
  gamma := Q.gamma
  gamma_isIso := Q.gamma_isIso

end CompositionData

/-- An object of the auxiliary category `D''` in the composition lemma. -/
structure CompositionAuxiliaryObject {C : Type u} [Bicategory.{w, v} C]
    [Bicategory.Strict C] (Q : CompositionData (C := C)) where
  dotted : DottedArrow (CompositionData.outerSquare Q)
  b : Q.objT ⟶ Q.objY
  eta : b ⟶ dotted.a ≫ Q.f
  eta_isIso : IsIso eta

attribute [instance] CompositionAuxiliaryObject.eta_isIso

namespace CompositionAuxiliaryObject

/-- A morphism in `D''`, consisting of the two arrows and the compatibility
identity from the source. -/
structure Hom {C : Type u} [Bicategory.{w, v} C]
    [Bicategory.Strict C] {Q : CompositionData (C := C)}
    (A A' : CompositionAuxiliaryObject Q) where
  theta₁ : DottedArrow.Hom A.dotted A'.dotted
  theta₂ : A.b ⟶ A'.b
  commutes : theta₂ ≫ A'.eta = A.eta ≫
    Bicategory.whiskerRight theta₁.hom Q.f

@[ext]
lemma Hom.ext {C : Type u} [Bicategory.{w, v} C]
    [Bicategory.Strict C] {Q : CompositionData (C := C)}
    {A A' : CompositionAuxiliaryObject Q} {h k : Hom A A'}
    (h₁ : h.theta₁ = k.theta₁) (h₂ : h.theta₂ = k.theta₂) : h = k := by
  cases h
  cases k
  cases h₁
  cases h₂
  rfl

def Hom.id {C : Type u} [Bicategory.{w, v} C]
    [Bicategory.Strict C] {Q : CompositionData (C := C)}
    (A : CompositionAuxiliaryObject Q) : Hom A A where
  theta₁ := DottedArrow.Hom.id A.dotted
  theta₂ := 𝟙 A.b
  commutes := by
    rw [DottedArrow.Hom.id, Bicategory.id_whiskerRight,
      Category.comp_id, Category.id_comp]

def Hom.comp {C : Type u} [Bicategory.{w, v} C]
    [Bicategory.Strict C] {Q : CompositionData (C := C)}
    {A A' A'' : CompositionAuxiliaryObject Q}
    (h : Hom A A') (k : Hom A' A'') : Hom A A'' where
  theta₁ := DottedArrow.Hom.comp h.theta₁ k.theta₁
  theta₂ := h.theta₂ ≫ k.theta₂
  commutes := by
    dsimp [DottedArrow.Hom.comp, CompositionData.outerSquare]
    calc
      (h.theta₂ ≫ k.theta₂) ≫ A''.eta =
          h.theta₂ ≫ (k.theta₂ ≫ A''.eta) := Category.assoc _ _ _
      _ = h.theta₂ ≫ (A'.eta ≫ Bicategory.whiskerRight k.theta₁.hom Q.f) :=
        congrArg (fun t => h.theta₂ ≫ t) k.commutes
      _ = (h.theta₂ ≫ A'.eta) ≫ Bicategory.whiskerRight k.theta₁.hom Q.f :=
        (Category.assoc _ _ _).symm
      _ = (A.eta ≫ Bicategory.whiskerRight h.theta₁.hom Q.f) ≫
          Bicategory.whiskerRight k.theta₁.hom Q.f :=
        congrArg (fun t => t ≫ Bicategory.whiskerRight k.theta₁.hom Q.f)
          h.commutes
      _ = A.eta ≫ (Bicategory.whiskerRight h.theta₁.hom Q.f ≫
          Bicategory.whiskerRight k.theta₁.hom Q.f) := Category.assoc _ _ _
      _ = A.eta ≫ Bicategory.whiskerRight (h.theta₁.hom ≫ k.theta₁.hom) Q.f := by
        rw [Bicategory.comp_whiskerRight]

instance category {C : Type u} [Bicategory.{w, v} C]
    [Bicategory.Strict C] (Q : CompositionData (C := C)) :
    Category (CompositionAuxiliaryObject Q) where
  Hom A A' := Hom A A'
  id A := Hom.id A
  comp h k := Hom.comp h k
  id_comp := by
    intro A A' h
    apply Hom.ext
    · apply DottedArrow.Hom.ext
      change (𝟙 A.dotted.a) ≫ h.theta₁.hom = h.theta₁.hom
      simp
    · simp [Hom.comp, Hom.id, DottedArrow.Hom.comp]
  comp_id := by
    intro A A' h
    apply Hom.ext
    · apply DottedArrow.Hom.ext
      change h.theta₁.hom ≫ (𝟙 A'.dotted.a) = h.theta₁.hom
      simp
    · simp [Hom.comp, Hom.id, DottedArrow.Hom.comp]
  assoc := by
    intro A A' A'' A''' h k l
    apply Hom.ext
    · apply DottedArrow.Hom.ext
      simp [Hom.comp, DottedArrow.Hom.comp, Category.assoc]
    · simp [Hom.comp, DottedArrow.Hom.comp]

end CompositionAuxiliaryObject

/-- The category called `D''` in the source proof. -/
abbrev CompositionAuxiliaryCategory {C : Type u} [Bicategory.{w, v} C]
    [Bicategory.Strict C] (Q : CompositionData (C := C)) := CompositionAuxiliaryObject Q

/- The object and morphism calculations used by the projection to `D'`.  The
coherence identities are named interfaces so that the actual functor below
has a concrete body while the proposition proofs remain part of the proof
stage. -/
theorem compositionAuxiliary_inner_commutes
    {C : Type u} [Bicategory.{w, v} C] [Bicategory.Strict C]
    {Q : CompositionData (C := C)} (A : CompositionAuxiliaryObject Q) :
    Q.gamma =
      (Bicategory.whiskerLeft Q.j
        (A.dotted.beta ≫ strictAssocInv A.dotted.a Q.f Q.g ≫
          Bicategory.whiskerRight (inv A.eta) Q.g)) ≫
        strictAssocInv Q.j A.b Q.g ≫
    Bicategory.whiskerRight
      (Bicategory.whiskerLeft Q.j A.eta ≫
            strictAssocInv Q.j A.dotted.a Q.f ≫
            Bicategory.whiskerRight A.dotted.alpha Q.f) Q.g := by
  let hX : strictAssocHom Q.x Q.f Q.g =
      (Bicategory.associator Q.x Q.f Q.g).hom := by
    simpa [strictAssocHom] using congrArg Iso.hom
      (Bicategory.Strict.associator_eqToIso Q.x Q.f Q.g) |>.symm
  let hA : strictAssocInv A.dotted.a Q.f Q.g =
      (Bicategory.associator A.dotted.a Q.f Q.g).inv := by
    simpa [strictAssocInv] using congrArg Iso.inv
      (Bicategory.Strict.associator_eqToIso A.dotted.a Q.f Q.g) |>.symm
  let hJb : strictAssocInv Q.j A.b Q.g =
      (Bicategory.associator Q.j A.b Q.g).inv := by
    simpa [strictAssocInv] using congrArg Iso.inv
      (Bicategory.Strict.associator_eqToIso Q.j A.b Q.g) |>.symm
  let hJa : strictAssocInv Q.j A.dotted.a Q.f =
      (Bicategory.associator Q.j A.dotted.a Q.f).inv := by
    simpa [strictAssocInv] using congrArg Iso.inv
      (Bicategory.Strict.associator_eqToIso Q.j A.dotted.a Q.f) |>.symm
  let hJafg : strictAssocInv Q.j A.dotted.a (Q.f ≫ Q.g) =
      (Bicategory.associator Q.j A.dotted.a (Q.f ≫ Q.g)).inv := by
    simpa [strictAssocInv] using congrArg Iso.inv
      (Bicategory.Strict.associator_eqToIso Q.j A.dotted.a (Q.f ≫ Q.g)) |>.symm
  letI : IsIso (strictAssocHom Q.x Q.f Q.g) := by
    dsimp [strictAssocHom]
    infer_instance
  apply (cancel_mono (strictAssocHom Q.x Q.f Q.g)).1
  have hcomm := A.dotted.commutes
  dsimp [CompositionData.outerSquare] at hcomm
  calc
    Q.gamma ≫ strictAssocHom Q.x Q.f Q.g =
        Q.j ◁ A.dotted.beta ≫
          strictAssocInv Q.j A.dotted.a (Q.f ≫ Q.g) ≫
          A.dotted.alpha ▷ (Q.f ≫ Q.g) := hcomm
    _ =
        (Q.j ◁ (A.dotted.beta ≫ strictAssocInv A.dotted.a Q.f Q.g ≫
          Bicategory.whiskerRight (inv A.eta) Q.g) ≫
          strictAssocInv Q.j A.b Q.g ≫
          (Q.j ◁ A.eta ≫ strictAssocInv Q.j A.dotted.a Q.f ≫
            Bicategory.whiskerRight A.dotted.alpha Q.f) ▷ Q.g) ≫
          strictAssocHom Q.x Q.f Q.g := by
      rw [hX, hA, hJb, hJa, hJafg]
      simp only [Category.assoc]
      rw [Bicategory.whiskerLeft_comp]
      letI : IsIso A.dotted.beta := A.dotted.beta_isIso
      letI : IsIso (Bicategory.whiskerLeft Q.j A.dotted.beta) := by
        infer_instance
      simp only [Category.assoc]
      apply (cancel_epi (Bicategory.whiskerLeft Q.j A.dotted.beta)).2
      simp only [Bicategory.whiskerLeft_comp, Bicategory.comp_whiskerRight,
        Category.assoc]
      rw [Bicategory.associator_naturality_left]
      letI : IsIso A.dotted.alpha := A.dotted.alpha_isIso
      simp only [← Category.assoc]
      rw [cancel_mono
        (Bicategory.whiskerRight A.dotted.alpha (Q.f ≫ Q.g))]
      simp only [Bicategory.associator_inv_naturality_middle, Category.assoc]
      rw [← Bicategory.comp_whiskerRight_assoc]
      rw [← Bicategory.whiskerLeft_comp]
      simp only [IsIso.inv_hom_id, Bicategory.whiskerLeft_id,
        Bicategory.id_whiskerRight, Category.id_comp]
      rw [Bicategory.pentagon_inv_assoc]
      simp

/-- The dotted arrow in `D'` associated to an object of `D''`. -/
noncomputable def compositionAuxiliaryInnerDotted
    {C : Type u} [Bicategory.{w, v} C] [Bicategory.Strict C]
    {Q : CompositionData (C := C)} (A : CompositionAuxiliaryObject Q) :
    DottedArrow (CompositionData.innerSquare Q) := by
  letI : IsIso A.dotted.alpha := A.dotted.alpha_isIso
  letI : IsIso A.dotted.beta := A.dotted.beta_isIso
  letI : IsIso A.eta := A.eta_isIso
  exact
    { a := A.b
      alpha :=
        Bicategory.whiskerLeft Q.j A.eta ≫
          strictAssocInv Q.j A.dotted.a Q.f ≫
          Bicategory.whiskerRight A.dotted.alpha Q.f
      beta :=
        A.dotted.beta ≫ strictAssocInv A.dotted.a Q.f Q.g ≫
          Bicategory.whiskerRight (inv A.eta) Q.g
      alpha_isIso := by
        apply IsIso.comp_isIso'
        · infer_instance
        · apply IsIso.comp_isIso'
          · dsimp [strictAssocInv]
            infer_instance
          · infer_instance
      beta_isIso := by
        apply IsIso.comp_isIso'
        · infer_instance
        · apply IsIso.comp_isIso'
          · dsimp [strictAssocInv]
            infer_instance
          · infer_instance
      commutes := compositionAuxiliary_inner_commutes A }

theorem compositionAuxiliary_inner_map_alpha
    {C : Type u} [Bicategory.{w, v} C] [Bicategory.Strict C]
    {Q : CompositionData (C := C)} {A A' : CompositionAuxiliaryObject Q}
    (H : CompositionAuxiliaryObject.Hom A A') :
    Bicategory.whiskerLeft Q.j H.theta₂ ≫
        (compositionAuxiliaryInnerDotted A').alpha =
      (compositionAuxiliaryInnerDotted A).alpha := by
  dsimp [compositionAuxiliaryInnerDotted]
  rw [← Category.assoc, ← Bicategory.whiskerLeft_comp, H.commutes]
  have hA : strictAssocInv Q.j A.dotted.a Q.f =
      (Bicategory.associator Q.j A.dotted.a Q.f).inv := by
    simpa [strictAssocInv] using congrArg Iso.inv
      (Bicategory.Strict.associator_eqToIso Q.j A.dotted.a Q.f) |>.symm
  have hA' : strictAssocInv Q.j A'.dotted.a Q.f =
      (Bicategory.associator Q.j A'.dotted.a Q.f).inv := by
    simpa [strictAssocInv] using congrArg Iso.inv
      (Bicategory.Strict.associator_eqToIso Q.j A'.dotted.a Q.f) |>.symm
  rw [Bicategory.whiskerLeft_comp, hA, hA']
  simp only [Category.assoc]
  rw [Bicategory.whisker_assoc_symm Q.j H.theta₁.hom Q.f]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  rw [← Bicategory.comp_whiskerRight, H.theta₁.alpha_naturality]

theorem compositionAuxiliary_inner_map_beta
    {C : Type u} [Bicategory.{w, v} C] [Bicategory.Strict C]
    {Q : CompositionData (C := C)} {A A' : CompositionAuxiliaryObject Q}
    (H : CompositionAuxiliaryObject.Hom A A') :
    (compositionAuxiliaryInnerDotted A).beta ≫
        Bicategory.whiskerRight H.theta₂ Q.g =
      (compositionAuxiliaryInnerDotted A').beta := by
  dsimp [compositionAuxiliaryInnerDotted]
  have hη : inv A.eta ≫ H.theta₂ =
      Bicategory.whiskerRight H.theta₁.hom Q.f ≫ inv A'.eta := by
    apply (cancel_mono A'.eta).1
    simp only [Category.assoc]
    rw [H.commutes]
    simp
  have hA : strictAssocInv A.dotted.a Q.f Q.g =
      (Bicategory.associator A.dotted.a Q.f Q.g).inv := by
    simpa [strictAssocInv] using congrArg Iso.inv
      (Bicategory.Strict.associator_eqToIso A.dotted.a Q.f Q.g) |>.symm
  have hA' : strictAssocInv A'.dotted.a Q.f Q.g =
      (Bicategory.associator A'.dotted.a Q.f Q.g).inv := by
    simpa [strictAssocInv] using congrArg Iso.inv
      (Bicategory.Strict.associator_eqToIso A'.dotted.a Q.f Q.g) |>.symm
  simp only [Category.assoc]
  rw [← Bicategory.comp_whiskerRight, hη, Bicategory.comp_whiskerRight,
    hA, hA']
  rw [← Bicategory.associator_inv_naturality_left_assoc]
  rw [← Category.assoc, H.theta₁.beta_naturality]

/-- The morphism of inner dotted arrows induced by a morphism in `D''`. -/
noncomputable def compositionAuxiliaryInnerMap
    {C : Type u} [Bicategory.{w, v} C] [Bicategory.Strict C]
    {Q : CompositionData (C := C)} {A A' : CompositionAuxiliaryObject Q}
    (H : CompositionAuxiliaryObject.Hom A A') :
    DottedArrow.Hom (compositionAuxiliaryInnerDotted A)
      (compositionAuxiliaryInnerDotted A') where
  hom := H.theta₂
  alpha_naturality := compositionAuxiliary_inner_map_alpha H
  beta_naturality := compositionAuxiliary_inner_map_beta H

/-- The functor `D'' ⟶ D'` from the source proof. -/
noncomputable def compositionAuxiliaryProjection
    {C : Type u} [Bicategory.{w, v} C] [Bicategory.Strict C]
    (Q : CompositionData (C := C)) :
    CompositionAuxiliaryCategory Q ⥤ DottedArrowCategory (CompositionData.innerSquare Q) where
  obj := compositionAuxiliaryInnerDotted
  map := @compositionAuxiliaryInnerMap C _ _ Q
  map_id := by
    intro A
    apply DottedArrow.Hom.ext
    change (𝟙 A.b) = 𝟙 A.b
    rfl
  map_comp := by
    intro A A' A'' H K
    apply DottedArrow.Hom.ext
    change H.theta₂ ≫ K.theta₂ = H.theta₂ ≫ K.theta₂
    rfl

/-- The intermediate solid square whose dotted-arrow category describes a
fibre of the projection. -/
def compositionFibreSquare
    {C : Type u} [Bicategory.{w, v} C] [Bicategory.Strict C]
    {Q : CompositionData (C := C)} (P : DottedArrow (CompositionData.innerSquare Q)) :
    DottedArrowSquare C where
  objS := Q.objS
  objX := Q.objX
  objT := Q.objT
  objY := Q.objY
  j := Q.j
  x := Q.x
  f := Q.f
  y := P.a
  gamma := P.alpha
  gamma_isIso := P.alpha_isIso

/-- The auxiliary category is equivalent to the outer dotted-arrow category. -/
theorem dottedArrow_composition_equivalence
    {C : Type u} [Bicategory.{w, v} C] [Bicategory.Strict C]
    (Q : CompositionData (C := C)) :
    Nonempty
      (DottedArrowCategory (CompositionData.outerSquare Q) ≌
        CompositionAuxiliaryCategory Q) := by
  let forward : DottedArrowCategory (CompositionData.outerSquare Q) ⥤
      CompositionAuxiliaryCategory Q := {
    obj := fun A =>
      { dotted := A
        b := A.a ≫ Q.f
        eta := 𝟙 (A.a ≫ Q.f)
        eta_isIso := inferInstance }
    map := fun {A A'} H =>
      { theta₁ := H
        theta₂ := Bicategory.whiskerRight H.hom Q.f
        commutes := by simp }
    map_id := by
      intro A
      apply CompositionAuxiliaryObject.Hom.ext
      · apply DottedArrow.Hom.ext
        change (𝟙 A.a) = 𝟙 A.a
        simp
      · change (𝟙 A.a) ▷ Q.f = 𝟙 (A.a ≫ Q.f)
        simp
    map_comp := by
      intro A A' A'' H K
      apply CompositionAuxiliaryObject.Hom.ext
      · apply DottedArrow.Hom.ext
        rfl
      · change (H.hom ≫ K.hom) ▷ Q.f =
          (H.hom ▷ Q.f) ≫ (K.hom ▷ Q.f)
        rw [Bicategory.comp_whiskerRight]
    }
  let inverse : CompositionAuxiliaryCategory Q ⥤
      DottedArrowCategory (CompositionData.outerSquare Q) := {
    obj := fun A => A.dotted
    map := fun {A A'} H => H.theta₁
    map_id := by
      intro A
      apply DottedArrow.Hom.ext
      rfl
    map_comp := by
      intro A A' A'' H K
      apply DottedArrow.Hom.ext
      rfl
    }
  let unitIso : 𝟭 (DottedArrowCategory (CompositionData.outerSquare Q)) ≅
      forward ⋙ inverse :=
    NatIso.ofComponents (fun A => Iso.refl A) (by
      intro A A' H
      apply DottedArrow.Hom.ext
      dsimp [Functor.comp, forward, inverse, DottedArrow.Hom.comp,
        DottedArrow.Hom.id]
      simp)
  let counitIso : inverse ⋙ forward ≅
      𝟭 (CompositionAuxiliaryCategory Q) :=
    NatIso.ofComponents (fun A =>
      { hom :=
          { theta₁ := DottedArrow.Hom.id A.dotted
            theta₂ := inv A.eta
            commutes := by
              simp [Functor.comp, forward, inverse, DottedArrow.Hom.id] }
        inv :=
          { theta₁ := DottedArrow.Hom.id A.dotted
            theta₂ := A.eta
            commutes := by
              simp [Functor.comp, forward, inverse, DottedArrow.Hom.id] }
        hom_inv_id := by
          dsimp [Functor.comp, forward, inverse,
            CompositionAuxiliaryObject.Hom.comp, DottedArrow.Hom.comp,
            DottedArrow.Hom.id]
          apply CompositionAuxiliaryObject.Hom.ext
          · apply DottedArrow.Hom.ext
            change (𝟙 A.dotted.a ≫ 𝟙 A.dotted.a) = 𝟙 A.dotted.a
            simp
          · change inv A.eta ≫ A.eta = 𝟙 (A.dotted.a ≫ Q.f)
            simp
        inv_hom_id := by
          dsimp [Functor.comp, forward, inverse,
            CompositionAuxiliaryObject.Hom.comp, DottedArrow.Hom.comp,
            DottedArrow.Hom.id]
          apply CompositionAuxiliaryObject.Hom.ext
          · apply DottedArrow.Hom.ext
            change (𝟙 A.dotted.a ≫ 𝟙 A.dotted.a) = 𝟙 A.dotted.a
            simp
          · change A.eta ≫ inv A.eta = 𝟙 A.b
            simp }) (by
      intro A A' H
      apply CompositionAuxiliaryObject.Hom.ext
      · apply DottedArrow.Hom.ext
        dsimp [Functor.comp, forward, inverse, DottedArrow.Hom.comp,
          DottedArrow.Hom.id]
        change H.theta₁.hom ≫ 𝟙 A'.dotted.a =
          𝟙 A.dotted.a ≫ H.theta₁.hom
        simp
      · dsimp [Functor.comp, forward, inverse,
          CompositionAuxiliaryObject.Hom.comp]
        have hη : inv A.eta ≫ H.theta₂ =
            Bicategory.whiskerRight H.theta₁.hom Q.f ≫ inv A'.eta := by
          apply (cancel_mono A'.eta).1
          simp only [Category.assoc]
          rw [H.commutes]
          simp
        exact hη.symm)
  exact ⟨Equivalence.mk'' forward inverse unitIso counitIso (by
    intro A
    apply CompositionAuxiliaryObject.Hom.ext
    · apply DottedArrow.Hom.ext
      dsimp [unitIso, counitIso, Functor.comp, forward, inverse,
        CompositionAuxiliaryObject.Hom.comp, DottedArrow.Hom.comp,
        DottedArrow.Hom.id]
      change (𝟙 A.a ≫ 𝟙 A.a) = 𝟙 A.a
      simp
    · dsimp [unitIso, counitIso, Functor.comp, forward, inverse,
        CompositionAuxiliaryObject.Hom.comp, DottedArrow.Hom.comp,
        DottedArrow.Hom.id]
      change 𝟙 (A.a ≫ Q.f) ≫ (𝟙 A.a ▷ Q.f) = 𝟙 (A.a ≫ Q.f)
      simp)⟩

/-- The projection in the composition lemma is fibred in groupoids. -/
theorem dottedArrow_composition_projection_isFibredInGroupoids
    {C : Type u} [Bicategory.{w, v} C] [Bicategory.Strict C]
    (hC : Bicategory.IsLocallyGroupoid C) (Q : CompositionData (C := C)) :
    (compositionAuxiliaryProjection Q).IsFibredInGroupoids := by
  letI : IsGroupoid (DottedArrowCategory (CompositionData.innerSquare Q)) :=
    dottedArrowCategory_isGroupoid hC _
  letI : IsGroupoid (DottedArrowCategory (CompositionData.outerSquare Q)) :=
    dottedArrowCategory_isGroupoid hC _
  constructor
  · intro V U f A hA
    subst U
    letI : IsIso f.hom := (hC Q.objT Q.objY).all_isIso f.hom
    let f' : V.a ⟶ A.b := f.hom
    let B : CompositionAuxiliaryObject Q :=
      { dotted := A.dotted
        b := V.a
        eta := f' ≫ A.eta
        eta_isIso := by infer_instance }
    have hV : compositionAuxiliaryInnerDotted B = V := by
      apply dottedArrow_ext_fields
      · rfl
      · apply heq_of_eq
        have hfa := f.alpha_naturality
        change Q.j ◁ f' ≫
            (Q.j ◁ A.eta ≫ strictAssocInv Q.j A.dotted.a Q.f ≫
              Bicategory.whiskerRight A.dotted.alpha Q.f) = V.alpha at hfa
        calc
          Q.j ◁ (f' ≫ A.eta) ≫ strictAssocInv Q.j A.dotted.a Q.f ≫
              Bicategory.whiskerRight A.dotted.alpha Q.f =
            Q.j ◁ f' ≫ Q.j ◁ A.eta ≫ strictAssocInv Q.j A.dotted.a Q.f ≫
              Bicategory.whiskerRight A.dotted.alpha Q.f := by
                simp only [Bicategory.whiskerLeft_comp, Category.assoc]
          _ = V.alpha := by simpa [Category.assoc] using hfa
      · apply heq_of_eq
        apply (cancel_mono (Bicategory.whiskerRight f' Q.g)).1
        dsimp [compositionAuxiliaryInnerDotted, B]
        simp only [Category.assoc]
        have hinv :
            Bicategory.whiskerRight (inv (f' ≫ A.eta)) Q.g ≫
                Bicategory.whiskerRight f' Q.g =
              Bicategory.whiskerRight (inv A.eta) Q.g := by
          rw [IsIso.inv_comp, ← Bicategory.comp_whiskerRight]
          simp
        rw [hinv]
        have hfb := f.beta_naturality.symm
        change A.dotted.beta ≫ strictAssocInv A.dotted.a Q.f Q.g ≫
            Bicategory.whiskerRight (inv A.eta) Q.g =
              V.beta ≫ Bicategory.whiskerRight f' Q.g at hfb
        simpa [compositionAuxiliaryProjection, compositionAuxiliaryInnerDotted] using hfb
    let H : CompositionAuxiliaryObject.Hom B A :=
      { theta₁ := DottedArrow.Hom.id A.dotted
        theta₂ := f'
        commutes := by
          dsimp [B]
          simp [DottedArrow.Hom.id] }
    have hH : (compositionAuxiliaryProjection Q).IsHomLift f H := by
      apply CategoryTheory.IsHomLift.of_fac'
        (compositionAuxiliaryProjection Q) f H hV rfl
      apply DottedArrow.Hom.ext
      dsimp [compositionAuxiliaryProjection, compositionAuxiliaryInnerMap,
        DottedArrow.category, CategoryStruct.comp, DottedArrow.Hom.comp]
      rw [dottedArrow_eqToHom_hom]
      have hV' :
          congrArg (fun X : DottedArrow (CompositionData.innerSquare Q) => X.a) hV =
            (rfl : B.b = V.a) := Subsingleton.elim _ _
      rw [hV']
      change f' = 𝟙 _ ≫ f.hom ≫ 𝟙 _
      simp
      rfl
    exact ⟨B, H, hH⟩
  · intro A A' A'' φ ψ f hcomp
    letI : IsIso φ.theta₁ := by
      exact IsGroupoid.all_isIso
        (self := dottedArrowCategory_isGroupoid hC (CompositionData.outerSquare Q))
        φ.theta₁
    letI : IsIso φ.theta₂ := (hC Q.objT Q.objY).all_isIso φ.theta₂
    let e : A'.dotted ≅ A.dotted := asIso φ.theta₁
    letI : IsIso φ.theta₁.hom := (hC Q.objT Q.objX).all_isIso φ.theta₁.hom
    let f' : A''.b ⟶ A'.b := f.hom
    have hbase : f' ≫ φ.theta₂ = ψ.theta₂ := by
      have h := congrArg (fun k => k.hom) hcomp
      change f' ≫ φ.theta₂ = ψ.theta₂ at h
      exact h
    let χ : CompositionAuxiliaryObject.Hom A'' A' :=
      { theta₁ := DottedArrow.Hom.comp ψ.theta₁ e.inv
        theta₂ := f'
        commutes := by
          apply (cancel_mono (Bicategory.whiskerRight φ.theta₁.hom Q.f)).1
          simp only [Category.assoc]
          rw [← φ.commutes]
          rw [← Category.assoc, hbase, ψ.commutes]
          rw [dottedArrow_comp_hom, Bicategory.comp_whiskerRight]
          simp only [Category.assoc]
          apply (cancel_epi A''.eta).2
          rw [← Bicategory.comp_whiskerRight]
          have he : e.inv.hom ≫ φ.theta₁.hom = 𝟙 A.dotted.a := by
            change e.inv.hom ≫ e.hom.hom = 𝟙 _
            exact congrArg (fun k => k.hom) e.inv_hom_id
          rw [he]
          simp }
    have hχ : (compositionAuxiliaryProjection Q).IsHomLift f χ := by
      apply CategoryTheory.IsHomLift.of_fac'
        (compositionAuxiliaryProjection Q) f χ rfl rfl
      apply DottedArrow.Hom.ext
      change f' = 𝟙 _ ≫ f' ≫ 𝟙 _
      simp
    have hχcomp : χ ≫ φ = ψ := by
      apply CompositionAuxiliaryObject.Hom.ext
      · apply DottedArrow.Hom.ext
        change ((ψ.theta₁.hom ≫ e.inv.hom) ≫ φ.theta₁.hom) = ψ.theta₁.hom
        simp only [Category.assoc]
        have he : e.inv.hom ≫ φ.theta₁.hom = 𝟙 A.dotted.a := by
          change e.inv.hom ≫ e.hom.hom = 𝟙 _
          exact congrArg (fun k => k.hom) e.inv_hom_id
        rw [he]
        simp
      · dsimp [χ, CompositionAuxiliaryObject.Hom.comp]
        exact hbase
    refine ⟨χ, ⟨hχ, hχcomp⟩, ?_⟩
    rintro χ' ⟨_, hχ'comp⟩
    apply CompositionAuxiliaryObject.Hom.ext
    · apply DottedArrow.Hom.ext
      apply (cancel_mono φ.theta₁.hom).1
      have h₁ := congrArg (fun k => k.theta₁.hom) hχ'comp
      have h₂ := congrArg (fun k => k.theta₁.hom) hχcomp
      change χ'.theta₁.hom ≫ φ.theta₁.hom =
        χ.theta₁.hom ≫ φ.theta₁.hom
      change χ'.theta₁.hom ≫ φ.theta₁.hom = ψ.theta₁.hom at h₁
      change χ.theta₁.hom ≫ φ.theta₁.hom = ψ.theta₁.hom at h₂
      exact h₁.trans h₂.symm
    · apply (cancel_mono φ.theta₂).1
      have h₁ := congrArg (fun k => k.theta₂) hχ'comp
      have h₂ := congrArg (fun k => k.theta₂) hχcomp
      change χ'.theta₂ ≫ φ.theta₂ = χ.theta₂ ≫ φ.theta₂
      change χ'.theta₂ ≫ φ.theta₂ = ψ.theta₂ at h₁
      change χ.theta₂ ≫ φ.theta₂ = ψ.theta₂ at h₂
      exact h₁.trans h₂.symm

/-- Each fibre of the composition projection is isomorphic to a category of
dotted arrows for the intermediate solid square. -/
theorem dottedArrow_composition_projection_fibre_equivalence
    {C : Type u} [Bicategory.{w, v} C] [Bicategory.Strict C]
    (Q : CompositionData (C := C)) (P : DottedArrow (CompositionData.innerSquare Q)) :
    Nonempty
      (Functor.Fiber (compositionAuxiliaryProjection Q) P ≌
        DottedArrowCategory (compositionFibreSquare P)) := by
  classical
  let Df : DottedArrowSquare C := {
    objS := Q.objS
    objX := Q.objX
    objT := Q.objT
    objY := Q.objY
    j := Q.j
    x := Q.x
    f := Q.f
    y := P.a
    gamma := P.alpha
    gamma_isIso := P.alpha_isIso }
  let hcoh :
      ∀ V : DottedArrow Df,
        strictAssocInv Q.j P.a Q.g ≫
            (Q.j ◁ V.beta) ▷ Q.g ≫
              strictAssocInv Q.j V.a Q.f ▷ Q.g ≫
                strictAssocHom (Q.j ≫ V.a) Q.f Q.g =
          Q.j ◁ (V.beta ▷ Q.g ≫ strictAssocHom V.a Q.f Q.g) ≫
            strictAssocInv Q.j V.a (Q.f ≫ Q.g) := fun V => by
    let hJb : strictAssocInv Q.j P.a Q.g =
        (Bicategory.associator Q.j P.a Q.g).inv := by
      simpa [strictAssocInv] using congrArg Iso.inv
        (Bicategory.Strict.associator_eqToIso Q.j P.a Q.g) |>.symm
    let hJa : strictAssocInv Q.j V.a Q.f =
        (Bicategory.associator Q.j V.a Q.f).inv := by
      simpa [strictAssocInv] using congrArg Iso.inv
        (Bicategory.Strict.associator_eqToIso Q.j V.a Q.f) |>.symm
    let hJafg : strictAssocInv Q.j V.a (Q.f ≫ Q.g) =
        (Bicategory.associator Q.j V.a (Q.f ≫ Q.g)).inv := by
      simpa [strictAssocInv] using congrArg Iso.inv
        (Bicategory.Strict.associator_eqToIso Q.j V.a (Q.f ≫ Q.g)) |>.symm
    let hA : strictAssocHom V.a Q.f Q.g =
        (Bicategory.associator V.a Q.f Q.g).hom := by
      simpa [strictAssocHom] using congrArg Iso.hom
        (Bicategory.Strict.associator_eqToIso V.a Q.f Q.g) |>.symm
    let hA' : strictAssocHom (Q.j ≫ V.a) Q.f Q.g =
        (Bicategory.associator (Q.j ≫ V.a) Q.f Q.g).hom := by
      simpa [strictAssocHom] using congrArg Iso.hom
        (Bicategory.Strict.associator_eqToIso (Q.j ≫ V.a) Q.f Q.g) |>.symm
    rw [hJb, hJa, hJafg, hA, hA']
    dsimp [Df]
    rw [Bicategory.whisker_assoc]
    simp only [Category.assoc]
    rw [Bicategory.pentagon_inv_inv_hom_hom_inv]
    simp
  let backObj :
      ∀ V : DottedArrow (compositionFibreSquare P),
        CompositionAuxiliaryObject Q := fun V => by
    letI : IsIso P.beta := P.beta_isIso
    letI : IsIso V.beta := V.beta_isIso
    letI : IsIso (Bicategory.whiskerRight V.beta Q.g) := by
      exact Bicategory.whiskerRight_isIso V.beta Q.g
    letI : IsIso (strictAssocHom V.a Q.f Q.g) := by
      dsimp [strictAssocHom]
      infer_instance
    let V' : DottedArrow Df := V
    letI : IsIso V'.beta := V'.beta_isIso
    let dotted : DottedArrow (CompositionData.outerSquare Q) := {
      a := V'.a
      alpha := V'.alpha
      beta :=
        P.beta ≫ Bicategory.whiskerRight V'.beta Q.g ≫
          strictAssocHom V'.a Q.f Q.g
      alpha_isIso := V'.alpha_isIso
      beta_isIso := by
        apply IsIso.comp_isIso' (f := P.beta)
        · exact P.beta_isIso
        · apply IsIso.comp_isIso' (f := Bicategory.whiskerRight V'.beta Q.g)
          · exact Bicategory.whiskerRight_isIso V'.beta Q.g
          · dsimp [strictAssocHom]
            infer_instance
      commutes := by
        dsimp [CompositionData.outerSquare]
        have hP := P.commutes
        change Q.gamma =
          (Q.j ◁ P.beta) ≫ strictAssocInv Q.j P.a Q.g ≫
            (P.alpha ▷ Q.g) at hP
        have hV := V'.commutes
        change P.alpha =
          (Q.j ◁ V'.beta) ≫ strictAssocInv Q.j V'.a Q.f ≫
            (V'.alpha ▷ Q.f) at hV
        rw [hP, hV]
        simp only [Category.assoc, Bicategory.comp_whiskerRight]
        dsimp [Df]
        let hX : strictAssocHom Q.x Q.f Q.g =
            (Bicategory.associator Q.x Q.f Q.g).hom := by
            simpa [strictAssocHom] using congrArg Iso.hom
              (Bicategory.Strict.associator_eqToIso Q.x Q.f Q.g) |>.symm
        rw [hX]
        rw [Bicategory.associator_naturality_left]
        let hA' : strictAssocHom (Q.j ≫ V'.a) Q.f Q.g =
            (Bicategory.associator (Q.j ≫ V'.a) Q.f Q.g).hom := by
          simpa [strictAssocHom] using congrArg Iso.hom
            (Bicategory.Strict.associator_eqToIso (Q.j ≫ V'.a) Q.f Q.g) |>.symm
        rw [← hA']
        let hcoh' := hcoh V'
        dsimp [Df] at hcoh'
        have hstep := congrArg
          (fun k => Q.j ◁ P.beta ≫ k ≫ V'.alpha ▷ (Q.f ≫ Q.g)) hcoh'
        simpa [Category.assoc, Bicategory.whiskerLeft_comp] using hstep
      }
    exact {
      dotted := dotted
      b := P.a
      eta := V'.beta
      eta_isIso := V'.beta_isIso }
  have hback (V : DottedArrow (compositionFibreSquare P)) :
      (compositionAuxiliaryProjection Q).obj (backObj V) = P := by
    letI : IsIso P.beta := P.beta_isIso
    letI : IsIso V.beta := V.beta_isIso
    letI : IsIso (V.beta ▷ Q.g) :=
      Bicategory.whiskerRight_isIso V.beta Q.g
    dsimp [compositionAuxiliaryProjection, compositionAuxiliaryInnerDotted,
      backObj]
    apply dottedArrow_ext_fields
    · rfl
    · have h := V.commutes
      change HEq
        (Q.j ◁ V.beta ≫ strictAssocInv Q.j V.a Q.f ≫ V.alpha ▷ Q.f)
        P.alpha
      exact heq_of_eq h.symm
    · dsimp [strictAssocHom, strictAssocInv]
      simp [Category.assoc]
      rw [← Bicategory.inv_whiskerRight]
      simp
  let backMap :
      ∀ {V W : DottedArrow (compositionFibreSquare P)},
        DottedArrow.Hom V W →
          CompositionAuxiliaryObject.Hom (backObj V) (backObj W) :=
    fun {V W} H => by
      let V' : DottedArrow Df := V
      let W' : DottedArrow Df := W
      let H' : DottedArrow.Hom V' W' := H
      letI : IsIso P.beta := P.beta_isIso
      letI : IsIso V.beta := V.beta_isIso
      letI : IsIso W.beta := W.beta_isIso
      letI : IsIso (Bicategory.whiskerRight V.beta Q.g) :=
        Bicategory.whiskerRight_isIso V.beta Q.g
      letI : IsIso (Bicategory.whiskerRight W.beta Q.g) :=
        Bicategory.whiskerRight_isIso W.beta Q.g
      exact {
        theta₁ := {
          hom := H'.hom
          alpha_naturality := by
            dsimp [backObj]
            exact H'.alpha_naturality
          beta_naturality := by
            dsimp [backObj]
            dsimp [Df] at V' W' H' ⊢
            change
              (P.beta ≫ (V'.beta ▷ Q.g) ≫
                  strictAssocHom V'.a Q.f Q.g) ≫
                    H'.hom ▷ (Q.f ≫ Q.g) =
                P.beta ≫ (W'.beta ▷ Q.g) ≫
                  strictAssocHom W'.a Q.f Q.g
            let hA : strictAssocHom V'.a Q.f Q.g =
                (Bicategory.associator V'.a Q.f Q.g).hom := by
              simpa [strictAssocHom] using congrArg Iso.hom
                (Bicategory.Strict.associator_eqToIso V'.a Q.f Q.g) |>.symm
            let hA' : strictAssocHom W'.a Q.f Q.g =
                (Bicategory.associator W'.a Q.f Q.g).hom := by
              simpa [strictAssocHom] using congrArg Iso.hom
                (Bicategory.Strict.associator_eqToIso W'.a Q.f Q.g) |>.symm
            have hnat :
                (Bicategory.associator V'.a Q.f Q.g).hom ≫
                    H'.hom ▷ (Q.f ≫ Q.g) =
                  (H'.hom ▷ Q.f) ▷ Q.g ≫
                    (Bicategory.associator W'.a Q.f Q.g).hom := by
              rw [← Bicategory.associator_naturality_left]
            rw [hA, hA']
            calc
              (P.beta ≫ V'.beta ▷ Q.g ≫
                  (Bicategory.associator V'.a Q.f Q.g).hom) ≫
                    H'.hom ▷ (Q.f ≫ Q.g) =
                  P.beta ≫ V'.beta ▷ Q.g ≫
                    ((Bicategory.associator V'.a Q.f Q.g).hom ≫
                      H'.hom ▷ (Q.f ≫ Q.g)) := by
                simp only [Category.assoc]
              _ = P.beta ≫ V'.beta ▷ Q.g ≫
                    ((H'.hom ▷ Q.f) ▷ Q.g ≫
                      (Bicategory.associator W'.a Q.f Q.g).hom) := by
                rw [hnat]
              _ = P.beta ≫ (V'.beta ≫ H'.hom ▷ Q.f) ▷ Q.g ≫
                    (Bicategory.associator W'.a Q.f Q.g).hom := by
                simp only [Bicategory.comp_whiskerRight, Category.assoc]
              _ = P.beta ≫ W'.beta ▷ Q.g ≫
                    (Bicategory.associator W'.a Q.f Q.g).hom := by
                rw [H'.beta_naturality]
        }
        theta₂ := 𝟙 P.a
        commutes := by
          dsimp [backObj]
          simpa using H'.beta_naturality.symm }
  let back : DottedArrowCategory (compositionFibreSquare P) ⥤
      Functor.Fiber (compositionAuxiliaryProjection Q) P := {
    obj := fun V => ⟨backObj V, hback V⟩
    map := fun {V W} H =>
      ⟨backMap H, by
        apply CategoryTheory.IsHomLift.of_fac'
          (compositionAuxiliaryProjection Q) (𝟙 P)
          (backMap H) (hback V) (hback W)
        apply DottedArrow.Hom.ext
        dsimp [compositionAuxiliaryProjection, compositionAuxiliaryInnerMap,
          backMap]
        dsimp [DottedArrow.category, CategoryStruct.comp, DottedArrow.Hom.comp]
        change 𝟙 P.a =
          (eqToHom (hback V)).hom ≫ 𝟙 P.a ≫
            (eqToHom (hback W).symm).hom
        have hVeq :
            (eqToHom (hback V) :
              (compositionAuxiliaryProjection Q).obj (backObj V) ⟶ P).hom =
                eqToHom (congrArg
                  (fun X : DottedArrow (CompositionData.innerSquare Q) => X.a)
                  (hback V)) := dottedArrow_eqToHom_hom (hback V)
        have hWeq :
            (eqToHom (hback W).symm :
              P ⟶ (compositionAuxiliaryProjection Q).obj (backObj W)).hom =
                eqToHom (congrArg
                  (fun X : DottedArrow (CompositionData.innerSquare Q) => X.a)
                  (hback W).symm) := dottedArrow_eqToHom_hom (hback W).symm
        have hV' :
            congrArg (fun X : DottedArrow (CompositionData.innerSquare Q) => X.a)
                (hback V) = (rfl :
                  ((compositionAuxiliaryProjection Q).obj (backObj V)).a = P.a) :=
              Subsingleton.elim _ _
        have hW' :
            congrArg (fun X : DottedArrow (CompositionData.innerSquare Q) => X.a)
                (hback W).symm = (rfl :
                  P.a = ((compositionAuxiliaryProjection Q).obj (backObj W)).a) :=
              Subsingleton.elim _ _
        rw [hVeq, hWeq, hV', hW']
        change 𝟙 P.a = 𝟙 P.a ≫ 𝟙 P.a ≫ 𝟙 P.a
        simp⟩
    map_id := by
      intro V
      let V' : DottedArrow Df := V
      apply Functor.Fiber.hom_ext
      change backMap (𝟙 V) =
        CompositionAuxiliaryObject.Hom.id (backObj V)
      apply CompositionAuxiliaryObject.Hom.ext
      · apply DottedArrow.Hom.ext
        change (DottedArrow.Hom.id V').hom = 𝟙 V'.a
        rfl
      · dsimp [backMap, DottedArrow.Hom.id, CompositionAuxiliaryObject.Hom.id]
    map_comp := by
      intro V W X H K
      apply Functor.Fiber.hom_ext
      change backMap (H ≫ K) =
        CompositionAuxiliaryObject.Hom.comp (backMap H) (backMap K)
      apply CompositionAuxiliaryObject.Hom.ext
      · apply DottedArrow.Hom.ext
        dsimp [backMap, DottedArrow.Hom.comp,
          CompositionAuxiliaryObject.Hom.comp]
        rfl
      · dsimp [backMap, DottedArrow.Hom.comp,
          CompositionAuxiliaryObject.Hom.comp]
        exact (Category.id_comp _).symm }
  let hbackFaithful : back.Faithful := {
    map_injective := by
      intro V W H K h
      apply DottedArrow.Hom.ext
      have h' := congrArg
        (fun L : back.obj V ⟶ back.obj W => L.1.theta₁.hom) h
      exact h' }
  let hbackFull : back.Full := {
    map_surjective := by
      intro V W φ
      let _ : (compositionAuxiliaryProjection Q).IsHomLift (𝟙 P) φ.1 := φ.2
      have hfac := CategoryTheory.IsHomLift.fac'
          (compositionAuxiliaryProjection Q) (𝟙 P) φ.1
      have hd : CategoryTheory.IsHomLift.domain_eq
          (compositionAuxiliaryProjection Q) (𝟙 P) φ.1 = hback V :=
        Subsingleton.elim _ _
      have hc : CategoryTheory.IsHomLift.codomain_eq
          (compositionAuxiliaryProjection Q) (𝟙 P) φ.1 = hback W :=
        Subsingleton.elim _ _
      rw [hd, hc] at hfac
      have hfac' := congrArg (fun k => k.hom) hfac
      change φ.1.theta₂ =
        (eqToHom (hback V)).hom ≫ 𝟙 P.a ≫
          (eqToHom (hback W).symm).hom at hfac'
      have hVhom :
          (eqToHom (hback V) :
            (compositionAuxiliaryProjection Q).obj (backObj V) ⟶ P).hom =
              𝟙 P.a := by
        rw [dottedArrow_eqToHom_hom]
        have hV' :
            congrArg (fun X : DottedArrow (CompositionData.innerSquare Q) => X.a)
                (hback V) = (rfl :
                  ((compositionAuxiliaryProjection Q).obj (backObj V)).a = P.a) :=
              Subsingleton.elim _ _
        rw [hV']
        rfl
      have hWhom :
          (eqToHom (hback W).symm :
            P ⟶ (compositionAuxiliaryProjection Q).obj (backObj W)).hom =
              𝟙 P.a := by
        rw [dottedArrow_eqToHom_hom]
        have hW' :
            congrArg (fun X : DottedArrow (CompositionData.innerSquare Q) => X.a)
                (hback W).symm = (rfl :
                  P.a = ((compositionAuxiliaryProjection Q).obj (backObj W)).a) :=
              Subsingleton.elim _ _
        rw [hW']
        rfl
      rw [hVhom, hWhom] at hfac'
      have htheta2 : φ.1.theta₂ = 𝟙 P.a := by
        calc
          φ.1.theta₂ = 𝟙 P.a ≫ 𝟙 P.a ≫ 𝟙 P.a := hfac'
          _ = 𝟙 P.a := by simp
      let H : DottedArrow.Hom V W := {
        hom := φ.1.theta₁.hom
        alpha_naturality := φ.1.theta₁.alpha_naturality
        beta_naturality := by
          have hcomm := φ.1.commutes
          change V.beta ≫ φ.1.theta₁.hom ▷ Q.f = W.beta
          change φ.1.theta₂ ≫ W.beta =
            V.beta ≫ φ.1.theta₁.hom ▷ Q.f at hcomm
          rw [htheta2] at hcomm
          exact hcomm.symm.trans (Category.id_comp _) }
      refine ⟨H, ?_⟩
      apply Functor.Fiber.hom_ext
      change backMap H = φ.1
      apply CompositionAuxiliaryObject.Hom.ext
      · apply DottedArrow.Hom.ext
        rfl
      · have hfac := CategoryTheory.IsHomLift.fac'
          (compositionAuxiliaryProjection Q) (𝟙 P) φ.1
        have hfac' := congrArg (fun k => k.hom) hfac
        change φ.1.theta₂ =
            (eqToHom (hback V)).hom ≫ 𝟙 P.a ≫
            (eqToHom (hback W).symm).hom at hfac'
        dsimp [backMap, H]
        exact htheta2.symm }
  let hbackEssSurj : back.EssSurj := {
    mem_essImage := by
      intro A
      rcases A with ⟨A, hA⟩
      cases hA
      let V : DottedArrow
          (compositionFibreSquare ((compositionAuxiliaryProjection Q).obj A)) := {
        a := A.dotted.a
        alpha := A.dotted.alpha
        beta := A.eta
        alpha_isIso := A.dotted.alpha_isIso
        beta_isIso := A.eta_isIso
        commutes := by
          dsimp [compositionFibreSquare, compositionAuxiliaryInnerDotted]
          rfl }
      have hB : (backObj V).b = A.b := by
        dsimp [backObj, V, compositionAuxiliaryProjection,
          compositionAuxiliaryInnerDotted]
      let H : CompositionAuxiliaryObject.Hom (backObj V) A := {
        theta₁ := {
          hom := 𝟙 A.dotted.a
          alpha_naturality := by
            dsimp [backObj, V]
            simp
          beta_naturality := by
            dsimp [backObj, V, compositionAuxiliaryProjection,
              compositionAuxiliaryInnerDotted]
            change
              ((A.dotted.beta ≫ strictAssocInv A.dotted.a Q.f Q.g ≫
                  Bicategory.whiskerRight (inv A.eta) Q.g) ≫
                Bicategory.whiskerRight A.eta Q.g ≫
                  strictAssocHom A.dotted.a Q.f Q.g) ≫
                Bicategory.whiskerRight (𝟙 A.dotted.a) (Q.f ≫ Q.g) =
              A.dotted.beta
            let hA : strictAssocInv A.dotted.a Q.f Q.g =
                (Bicategory.associator A.dotted.a Q.f Q.g).inv := by
              simpa [strictAssocInv] using congrArg Iso.inv
                (Bicategory.Strict.associator_eqToIso A.dotted.a Q.f Q.g) |>.symm
            let hA' : strictAssocHom A.dotted.a Q.f Q.g =
                (Bicategory.associator A.dotted.a Q.f Q.g).hom := by
              simpa [strictAssocHom] using congrArg Iso.hom
                (Bicategory.Strict.associator_eqToIso A.dotted.a Q.f Q.g) |>.symm
            rw [hA, hA']
            simp only [Category.assoc]
            rw [← Bicategory.comp_whiskerRight_assoc]
            have hη : inv A.eta ≫ A.eta =
                𝟙 (A.dotted.a ≫ Q.f) := by simp
            rw [hη]
            simp }
        theta₂ := eqToHom hB
        commutes := by
          dsimp [backObj, V]
          change eqToHom hB ≫ A.eta = A.eta ≫
            (𝟙 A.dotted.a ▷ Q.f)
          rw [Bicategory.id_whiskerRight]
          rw [Category.comp_id]
          cases hB
          change 𝟙 A.b ≫ A.eta = A.eta
          simp }
      let hH : back.obj V ⟶ ⟨A, rfl⟩ :=
        ⟨H, by
          apply CategoryTheory.IsHomLift.of_fac'
            (compositionAuxiliaryProjection Q)
            (𝟙 ((compositionAuxiliaryProjection Q).obj A))
            H (hback V) rfl
          apply DottedArrow.Hom.ext
          dsimp [compositionAuxiliaryProjection, compositionAuxiliaryInnerMap,
            H, DottedArrow.category, CategoryStruct.comp, DottedArrow.Hom.comp]
          change (eqToHom hB : (backObj V).b ⟶ A.b) =
            (eqToHom (hback V) :
              (compositionAuxiliaryProjection Q).obj (backObj V) ⟶
                (compositionAuxiliaryProjection Q).obj A).hom ≫
              𝟙 A.b ≫
            (eqToHom (rfl :
              (compositionAuxiliaryProjection Q).obj A =
                (compositionAuxiliaryProjection Q).obj A) :
              (compositionAuxiliaryProjection Q).obj A ⟶
                (compositionAuxiliaryProjection Q).obj A).hom
          have hVeq :
              (eqToHom (hback V) :
                (compositionAuxiliaryProjection Q).obj (backObj V) ⟶
                  (compositionAuxiliaryProjection Q).obj A).hom =
                eqToHom (congrArg
                  (fun X : DottedArrow (CompositionData.innerSquare Q) => X.a)
                  (hback V)) := dottedArrow_eqToHom_hom (hback V)
          have hV' :
              congrArg (fun X : DottedArrow (CompositionData.innerSquare Q) => X.a)
                  (hback V) = (rfl :
                    ((compositionAuxiliaryProjection Q).obj (backObj V)).a =
                      ((compositionAuxiliaryProjection Q).obj A).a) :=
            Subsingleton.elim _ _
          have hVhom0 :
              (eqToHom (hback V) :
                (compositionAuxiliaryProjection Q).obj (backObj V) ⟶
                  (compositionAuxiliaryProjection Q).obj A).hom =
                𝟙 ((compositionAuxiliaryProjection Q).obj A).a := by
            rw [hVeq, hV']
            rfl
          have hB0 : (eqToHom hB : (backObj V).b ⟶ A.b) =
              𝟙 A.b := by
            cases hB
            rfl
          have hId :
              (eqToHom (rfl :
                (compositionAuxiliaryProjection Q).obj A =
                  (compositionAuxiliaryProjection Q).obj A) :
                (compositionAuxiliaryProjection Q).obj A ⟶
                  (compositionAuxiliaryProjection Q).obj A).hom =
                𝟙 ((compositionAuxiliaryProjection Q).obj A).a := by
            rw [dottedArrow_eqToHom_hom]
            rfl
          rw [hB0, hVhom0, hId]
          dsimp [compositionAuxiliaryProjection, compositionAuxiliaryInnerDotted,
            backObj, V]
          simpa only [Category.comp_id] using
            (Category.comp_id (𝟙 A.b)).symm⟩
      letI : IsIso H.theta₁.hom := by
        dsimp [H]
        infer_instance
      let e : (backObj V).dotted.a ≅ A.dotted.a := asIso H.theta₁.hom
      have hHhom : H.theta₁.hom = 𝟙 A.dotted.a := by rfl
      have he : e.inv = 𝟙 A.dotted.a := by
        apply (cancel_mono H.theta₁.hom).1
        change e.inv ≫ e.hom = 𝟙 A.dotted.a ≫ H.theta₁.hom
        rw [e.inv_hom_id, hHhom]
        simp
      let Hinv : CompositionAuxiliaryObject.Hom A (backObj V) := {
        theta₁ := {
          hom := e.inv
          alpha_naturality := by
            rw [← H.theta₁.alpha_naturality]
            rw [← Category.assoc, ← Bicategory.whiskerLeft_comp]
            rw [hHhom, he]
            simp only [Category.comp_id, Category.id_comp]
          beta_naturality := by
            rw [← H.theta₁.beta_naturality]
            rw [Category.assoc, ← Bicategory.comp_whiskerRight]
            simp [e] }
        theta₂ := eqToHom hB.symm
        commutes := by
          apply (cancel_mono
            (Bicategory.whiskerRight H.theta₁.hom Q.f)).1
          simp only [Category.assoc]
          calc
            eqToHom hB.symm ≫ (backObj V).eta ≫
                Bicategory.whiskerRight H.theta₁.hom Q.f =
              eqToHom hB.symm ≫ H.theta₂ ≫ A.eta := by
                rw [H.commutes]
            _ = A.eta ≫ Bicategory.whiskerRight e.inv Q.f ≫
                Bicategory.whiskerRight H.theta₁.hom Q.f := by
              simp [H, e, hB, hHhom, he]
              have hi : CategoryTheory.inv (𝟙 A.dotted.a) =
                  𝟙 A.dotted.a := by simp
              rw [hi, Bicategory.id_whiskerRight]
              simp }
      let hHinv : ⟨A, rfl⟩ ⟶ back.obj V :=
        ⟨Hinv, by
          apply CategoryTheory.IsHomLift.of_fac'
            (compositionAuxiliaryProjection Q)
            (𝟙 ((compositionAuxiliaryProjection Q).obj A))
            Hinv
            (rfl : (compositionAuxiliaryProjection Q).obj A =
              (compositionAuxiliaryProjection Q).obj A)
            (hback V)
          apply DottedArrow.Hom.ext
          dsimp [compositionAuxiliaryProjection, compositionAuxiliaryInnerMap,
            Hinv, DottedArrow.category, CategoryStruct.comp, DottedArrow.Hom.comp]
          change (eqToHom hB.symm : A.b ⟶ (backObj V).b) =
            (eqToHom (rfl :
              (compositionAuxiliaryProjection Q).obj A =
                (compositionAuxiliaryProjection Q).obj A) :
              (compositionAuxiliaryProjection Q).obj A ⟶
                (compositionAuxiliaryProjection Q).obj A).hom ≫
              𝟙 ((compositionAuxiliaryProjection Q).obj A).a ≫
            (eqToHom (hback V).symm :
              (compositionAuxiliaryProjection Q).obj A ⟶
                (compositionAuxiliaryProjection Q).obj (backObj V)).hom
          have hVeq :
              (eqToHom (hback V).symm :
                (compositionAuxiliaryProjection Q).obj A ⟶
                  (compositionAuxiliaryProjection Q).obj (backObj V)).hom =
                eqToHom (congrArg
                  (fun X : DottedArrow (CompositionData.innerSquare Q) => X.a)
                  (hback V).symm) := dottedArrow_eqToHom_hom (hback V).symm
          have hV' :
              congrArg (fun X : DottedArrow (CompositionData.innerSquare Q) => X.a)
                  (hback V).symm = (rfl :
                    ((compositionAuxiliaryProjection Q).obj A).a =
                      ((compositionAuxiliaryProjection Q).obj (backObj V)).a) :=
            Subsingleton.elim _ _
          have hVhom0 :
              (eqToHom (hback V).symm :
                (compositionAuxiliaryProjection Q).obj A ⟶
                  (compositionAuxiliaryProjection Q).obj (backObj V)).hom =
                𝟙 ((compositionAuxiliaryProjection Q).obj A).a := by
            rw [hVeq, hV']
            rfl
          have hB0 : (eqToHom hB.symm : A.b ⟶ (backObj V).b) =
              𝟙 A.b := by
            cases hB
            rfl
          have hId :
              (eqToHom (rfl :
                (compositionAuxiliaryProjection Q).obj A =
                  (compositionAuxiliaryProjection Q).obj A) :
                (compositionAuxiliaryProjection Q).obj A ⟶
                  (compositionAuxiliaryProjection Q).obj A).hom =
                𝟙 ((compositionAuxiliaryProjection Q).obj A).a := by
            rw [dottedArrow_eqToHom_hom]
            rfl
          rw [hB0, hId, hVhom0]
          dsimp [compositionAuxiliaryProjection, compositionAuxiliaryInnerDotted,
            backObj, V]
          simpa only [Category.comp_id] using
            (Category.comp_id (𝟙 A.b)).symm⟩
      let e : back.obj V ≅ ⟨A, rfl⟩ := {
        hom := hH
        inv := hHinv
        hom_inv_id := by
          apply Functor.Fiber.hom_ext
          change hH.1 ≫ hHinv.1 = 𝟙 (back.obj V).1
          apply CompositionAuxiliaryObject.Hom.ext
          · apply DottedArrow.Hom.ext
            change H.theta₁.hom ≫ Hinv.theta₁.hom =
              𝟙 (backObj V).dotted.a
            dsimp [H, Hinv]
            change e.hom ≫ e.inv = 𝟙 (backObj V).dotted.a
            exact e.hom_inv_id
          · change H.theta₂ ≫ Hinv.theta₂ = 𝟙 (backObj V).b
            dsimp [H, Hinv]
            rw [eqToHom_trans]
            exact eqToHom_refl _ _
        inv_hom_id := by
          apply Functor.Fiber.hom_ext
          change hHinv.1 ≫ hH.1 = 𝟙 (⟨A, rfl⟩ :
            Functor.Fiber (compositionAuxiliaryProjection Q)
              ((compositionAuxiliaryProjection Q).obj A)).1
          apply CompositionAuxiliaryObject.Hom.ext
          · apply DottedArrow.Hom.ext
            change Hinv.theta₁.hom ≫ H.theta₁.hom =
              𝟙 A.dotted.a
            dsimp [H, Hinv]
            change e.inv ≫ e.hom = 𝟙 A.dotted.a
            exact e.inv_hom_id
          · change Hinv.theta₂ ≫ H.theta₂ = 𝟙 A.b
            dsimp [H, Hinv]
            rw [eqToHom_trans]
            exact eqToHom_refl _ _ }
      exact ⟨V, ⟨e⟩⟩ }
  let hbackEquivalence : back.IsEquivalence :=
    { faithful := hbackFaithful
      full := hbackFull
      essSurj := hbackEssSurj }
  exact ⟨(@Functor.asEquivalence _ _ _ _ back hbackEquivalence).symm⟩

end Formalization.Books.Categories.Unit44
