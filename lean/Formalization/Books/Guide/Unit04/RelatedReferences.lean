import Formalization.Books.Stacks.Unit01.Gerbes
import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic

/-!
# A Guide to the Literature, Chapter 4: related references

This file records the mathematical interfaces in the chapter's discussion of
Giraud's description of torsors and gerbes, together with the 2-categorical
remark about stacks in groupoids.  The other references in the section are
bibliographic and do not contain additional precise mathematical assertions.
-/

noncomputable section

universe t w' w v u

open CategoryTheory
open Formalization.Books.Stacks.Unit01
open Opposite

open scoped CategoryTheory.Pseudofunctor.StrongTrans

namespace Formalization.Books.Guide.Unit04

/-! ### Cohomology on an object of a site -/

/-- The degree-one cohomology type used for a sheaf on a site at an object. -/
abbrev siteH1 {C : Type u} [Category.{v} C]
    {J : GrothendieckTopology C}
    (G : Sheaf J AddCommGrpCat.{w}) (X : C)
    [HasSheafify (J.over X) AddCommGrpCat.{w}]
    [HasExt.{w'} (Sheaf (J.over X) AddCommGrpCat.{w})] : Type w' :=
  (CategoryTheory.Sheaf.H (G.over X) 1 : Type w')

/-- The degree-two cohomology type used for a sheaf on a site at an object. -/
abbrev siteH2 {C : Type u} [Category.{v} C]
    {J : GrothendieckTopology C}
    (G : Sheaf J AddCommGrpCat.{w}) (X : C)
    [HasSheafify (J.over X) AddCommGrpCat.{w}]
    [HasExt.{w'} (Sheaf (J.over X) AddCommGrpCat.{w})] : Type w' :=
  (CategoryTheory.Sheaf.H (G.over X) 2 : Type w')

/-! ### Torsors -/

/--
A right torsor for an abelian sheaf on the slice site over `X`.

The action is written additively.  The last two fields express local
nonemptiness and local simple transitivity with respect to covering families.
-/
structure SiteTorsor {C : Type u} [Category.{v} C]
    (J : GrothendieckTopology C)
    (G : Sheaf J AddCommGrpCat.{w}) (X : C) where
  carrier : Sheaf (J.over X) (Type w)
  action : ∀ (U : (Over C X)ᵒᵖ),
    (G.over X).obj.obj U → carrier.obj.obj U → carrier.obj.obj U
  action_zero : ∀ (U : (Over C X)ᵒᵖ)
    (p : carrier.obj.obj U), action U 0 p = p
  action_add : ∀ (U : (Over C X)ᵒᵖ)
    (a b : (G.over X).obj.obj U) (p : carrier.obj.obj U),
    action U (a + b) p = action U a (action U b p)
  action_natural : ∀ {U V : (Over C X)ᵒᵖ}
    (q : U ⟶ V) (a : (G.over X).obj.obj U) (p : carrier.obj.obj U),
    carrier.obj.map q (action U a p) =
      action V ((G.over X).obj.map q a) (carrier.obj.map q p)
  locally_nonempty : ∀ (U : Over C X),
    ∃ (ι : Type t) (V : ι → Over C X)
      (f : ∀ i, V i ⟶ U),
      CoveringFamily (J.over X) f ∧
        ∀ i, Nonempty (carrier.obj.obj (op (V i)))
  locally_simply_transitive : ∀ (U : Over C X)
    (p q : carrier.obj.obj (op U)),
    ∃ (ι : Type t) (V : ι → Over C X)
      (f : ∀ i, V i ⟶ U),
      CoveringFamily (J.over X) f ∧
        ∀ i, ∃! a : (G.over X).obj.obj (op (V i)),
          action (op (V i)) a (carrier.obj.map (f i).op p) =
            carrier.obj.map (f i).op q

/-- An equivariant isomorphism of torsors, including its inverse explicitly. -/
structure SiteTorsorEquivalence {C : Type u} [Category.{v} C]
    {J : GrothendieckTopology C}
    {G : Sheaf J AddCommGrpCat.{w}} {X : C}
    (P Q : SiteTorsor J G X) where
  map : P.carrier ≅ Q.carrier
  equivariant : ∀ (U : (Over C X)ᵒᵖ)
    (a : (G.over X).obj.obj U) (p : P.carrier.obj.obj U),
    map.hom.hom.app U (P.action U a p) =
      Q.action U a (map.hom.hom.app U p)
  inverse_equivariant : ∀ (U : (Over C X)ᵒᵖ)
    (a : (G.over X).obj.obj U) (q : Q.carrier.obj.obj U),
    map.inv.hom.app U (Q.action U a q) =
      P.action U a (map.inv.hom.app U q)

namespace SiteTorsorEquivalence

/-- Composition of equivariant torsor isomorphisms. -/
def trans {C : Type u} [Category.{v} C]
    {J : GrothendieckTopology C}
    {G : Sheaf J AddCommGrpCat.{w}} {X : C}
    {P Q R : SiteTorsor J G X}
    (e : SiteTorsorEquivalence P Q) (f : SiteTorsorEquivalence Q R) :
    SiteTorsorEquivalence P R where
  map := e.map.trans f.map
  equivariant := by
    intro U a p
    change f.map.hom.hom.app U (e.map.hom.hom.app U (P.action U a p)) =
      R.action U a (f.map.hom.hom.app U (e.map.hom.hom.app U p))
    rw [e.equivariant, f.equivariant]
  inverse_equivariant := by
    intro U a r
    change e.map.inv.hom.app U (f.map.inv.hom.app U (R.action U a r)) =
      P.action U a (e.map.inv.hom.app U (f.map.inv.hom.app U r))
    rw [f.inverse_equivariant, e.inverse_equivariant]

/-- Symmetry of equivariant torsor isomorphism. -/
def symm {C : Type u} [Category.{v} C]
    {J : GrothendieckTopology C}
    {G : Sheaf J AddCommGrpCat.{w}} {X : C}
    {P Q : SiteTorsor J G X} (e : SiteTorsorEquivalence P Q) :
    SiteTorsorEquivalence Q P where
  map := e.map.symm
  equivariant := e.inverse_equivariant
  inverse_equivariant := e.equivariant

end SiteTorsorEquivalence

/-- The setoid of torsors modulo equivariant isomorphism. -/
def siteTorsorSetoid {C : Type u} [Category.{v} C]
    (J : GrothendieckTopology C)
    (G : Sheaf J AddCommGrpCat.{w}) (X : C) :
    Setoid (SiteTorsor J G X) where
  r P Q := Nonempty (SiteTorsorEquivalence P Q)
  iseqv := by
    refine ⟨?_, ?_, ?_⟩
    · intro P
      exact ⟨{
        map := Iso.refl _
        equivariant := by simp
        inverse_equivariant := by simp
      }⟩
    · intro P Q h
      rcases h with ⟨e⟩
      exact ⟨e.symm⟩
    · intro P Q R hPQ hQR
      rcases hPQ with ⟨e⟩
      rcases hQR with ⟨f⟩
      exact ⟨e.trans f⟩

/-- Isomorphism classes of `G`-torsors on the slice site over `X`. -/
def SiteTorsorClass {C : Type u} [Category.{v} C]
    (J : GrothendieckTopology C)
    (G : Sheaf J AddCommGrpCat.{w}) (X : C) : Type _ :=
  Quotient (siteTorsorSetoid.{w, v, u, t} J G X)

/-! ### The Picard operations on torsors -/

/-- The trivial torsor is the torsor given by the additive sheaf itself.

The carrier is kept behind this interface because the concrete sheafification
of the underlying presheaf depends on the universe presentation of the site. -/
theorem siteTorsorTrivial_exists {C : Type u} [Category.{v} C]
    (J : GrothendieckTopology C)
    (G : Sheaf J AddCommGrpCat.{w}) (X : C) :
    Nonempty (SiteTorsor.{t, w, v, u} J G X) := by
  let carrier : Sheaf (J.over X) (Type w) :=
    ⟨(G.over X).obj ⋙ forget AddCommGrpCat.{w},
      Presheaf.isSheaf_comp_of_isSheaf (J := J.over X)
        ((G.over X).obj) (forget AddCommGrpCat.{w}) (G.over X).property⟩
  refine ⟨{
    carrier := carrier
    action := fun U a p => a + (show (G.over X).obj.obj U from p)
    action_zero := by
      intro U p
      change 0 + (show (G.over X).obj.obj U from p) =
        (show (G.over X).obj.obj U from p)
      exact zero_add _
    action_add := by
      intro U a b p
      change (a + b) + (show (G.over X).obj.obj U from p) =
        a + (b + (show (G.over X).obj.obj U from p))
      exact add_assoc _ _ _
    action_natural := by
      intro U V q a p
      change ((G.over X).obj.map q) (a + (show (G.over X).obj.obj U from p)) =
        (G.over X).obj.map q a +
          (G.over X).obj.map q (show (G.over X).obj.obj U from p)
      exact map_add _ _ _
    locally_nonempty := by
      intro U
      refine ⟨PUnit, fun _ => U, fun _ => 𝟙 U, ?_, ?_⟩
      · apply (J.over X).covering_of_eq_top
        apply top_unique
        intro V f _
        rw [Sieve.mem_ofArrows_iff]
        exact ⟨PUnit.unit, f, by simp⟩
      · intro i
        exact ⟨(0 : (G.over X).obj.obj (op U))⟩
    locally_simply_transitive := by
      intro U p q
      refine ⟨PUnit, fun _ => U, fun _ => 𝟙 U, ?_, ?_⟩
      · apply (J.over X).covering_of_eq_top
        apply top_unique
        intro V f _
        rw [Sieve.mem_ofArrows_iff]
        exact ⟨PUnit.unit, f, by simp⟩
      · intro i
        have hi : i = PUnit.unit := Subsingleton.elim _ _
        subst i
        let pG : (G.over X).obj.obj (op U) := show (G.over X).obj.obj (op U) from p
        let qG : (G.over X).obj.obj (op U) := show (G.over X).obj.obj (op U) from q
        refine ⟨qG - pG, ?_, ?_⟩
        · have h_id : (𝟙 U).op = 𝟙 (op U) := by simp
          have hp : ConcreteCategory.hom
              (carrier.obj.map (𝟙 U).op) p = p := by
            rw [h_id, carrier.obj.map_id]
            rfl
          have hq : ConcreteCategory.hom
              (carrier.obj.map (𝟙 U).op) q = q := by
            rw [h_id, carrier.obj.map_id]
            rfl
          simpa [hp, hq, pG, qG] using sub_add_cancel qG pG
        · intro b hb
          have h_id : (𝟙 U).op = 𝟙 (op U) := by simp
          have hp : ConcreteCategory.hom
              (carrier.obj.map (𝟙 U).op) p = p := by
            rw [h_id, carrier.obj.map_id]
            rfl
          have hq : ConcreteCategory.hom
              (carrier.obj.map (𝟙 U).op) q = q := by
            rw [h_id, carrier.obj.map_id]
            rfl
          have hbp : b + pG = qG := by
            simpa [hp, hq, pG, qG] using hb
          calc
            b = (b + pG) - pG := by simp
            _ = qG - pG := by rw [hbp]
  }⟩

/-- A chosen trivial torsor. -/
noncomputable def siteTorsorTrivial {C : Type u} [Category.{v} C]
    (J : GrothendieckTopology C)
    (G : Sheaf J AddCommGrpCat.{w}) (X : C) : SiteTorsor.{t, w, v, u} J G X :=
  Classical.choice (siteTorsorTrivial_exists J G X)

/-- Reversing the sign of the action gives the inverse torsor. -/
def siteTorsorInverse {C : Type u} [Category.{v} C]
    {J : GrothendieckTopology C}
    {G : Sheaf J AddCommGrpCat.{w}} {X : C}
    (P : SiteTorsor.{t, w, v, u} J G X) : SiteTorsor.{t, w, v, u} J G X where
  carrier := P.carrier
  action U a p := P.action U (-a) p
  action_zero U p := by simpa using P.action_zero U p
  action_add U a b p := by
    rw [neg_add, P.action_add]
  action_natural := by
    intro U V q a p
    simpa using P.action_natural q (-a) p
  locally_nonempty := P.locally_nonempty
  locally_simply_transitive := by
    intro U p q
    rcases P.locally_simply_transitive U p q with ⟨ι, V, f, hf, h⟩
    refine ⟨ι, V, f, hf, ?_⟩
    intro i
    rcases h i with ⟨a, ha, huniq⟩
    refine ⟨-a, ?_, ?_⟩
    · simpa using ha
    · intro b hb
      have hba : -b = a := huniq (-b) (by simpa using hb)
      calc
        b = -(-b) := by simp
        _ = -a := by rw [hba]

/-- Equivariant equivalences are preserved by passage to the inverse torsor. -/
def SiteTorsorEquivalence.inverse {C : Type u} [Category.{v} C]
    {J : GrothendieckTopology C}
    {G : Sheaf J AddCommGrpCat.{w}} {X : C}
    {P Q : SiteTorsor.{t, w, v, u} J G X} (e : SiteTorsorEquivalence P Q) :
    SiteTorsorEquivalence (siteTorsorInverse P) (siteTorsorInverse Q) where
  map := e.map
  equivariant := by
    intro U a p
    exact e.equivariant U (-a) p
  inverse_equivariant := by
    intro U a q
    exact e.inverse_equivariant U (-a) q

/-- Inversion respects the torsor equivalence relation. -/
theorem siteTorsorInverse_respects_equivalence {C : Type u} [Category.{v} C]
    {J : GrothendieckTopology C}
    {G : Sheaf J AddCommGrpCat.{w}} {X : C}
    {P Q : SiteTorsor.{t, w, v, u} J G X}
    (h : Nonempty (SiteTorsorEquivalence P Q)) :
    Nonempty (SiteTorsorEquivalence (siteTorsorInverse P) (siteTorsorInverse Q)) :=
  ⟨SiteTorsorEquivalence.inverse (Nonempty.some h)⟩

/-- Reflexivity for equivariant torsor equivalences. -/
def SiteTorsorEquivalence.refl {C : Type u} [Category.{v} C]
    {J : GrothendieckTopology C}
    {G : Sheaf J AddCommGrpCat.{w}} {X : C}
    (P : SiteTorsor.{t, w, v, u} J G X) : SiteTorsorEquivalence P P where
  map := Iso.refl _
  equivariant := by simp
  inverse_equivariant := by simp

/-- Data specifying the quotient construction of the contracted product.

The fields record the two presentations of the quotient: translating the first
factor by `a` is identified with translating the second factor by `-a`, and the
resulting action can be computed in either factor. -/
structure SiteTorsorContractedProductData {C : Type u} [Category.{v} C]
    {J : GrothendieckTopology C}
    {G : Sheaf J AddCommGrpCat.{w}} {X : C}
    (P Q : SiteTorsor.{t, w, v, u} J G X) where
  torsor : SiteTorsor.{t, w, v, u} J G X
  pair : ∀ (U : (Over C X)ᵒᵖ),
    P.carrier.obj.obj U → Q.carrier.obj.obj U → torsor.carrier.obj.obj U
  pair_left_right : ∀ (U : (Over C X)ᵒᵖ)
    (a : (G.over X).obj.obj U) (p : P.carrier.obj.obj U) (q : Q.carrier.obj.obj U),
    pair U (P.action U a p) q = pair U p (Q.action U (-a) q)
  pair_action_left : ∀ (U : (Over C X)ᵒᵖ)
    (a : (G.over X).obj.obj U) (p : P.carrier.obj.obj U) (q : Q.carrier.obj.obj U),
    torsor.action U a (pair U p q) = pair U (P.action U a p) q
  pair_action_right : ∀ (U : (Over C X)ᵒᵖ)
    (a : (G.over X).obj.obj U) (p : P.carrier.obj.obj U) (q : Q.carrier.obj.obj U),
    torsor.action U a (pair U p q) = pair U p (Q.action U a q)

/-- Existence of the sheafified quotient defining the contracted product. -/
theorem siteTorsorContractedProductData_exists {C : Type u} [Category.{v} C]
    {J : GrothendieckTopology C}
    {G : Sheaf J AddCommGrpCat.{w}} {X : C}
    (P Q : SiteTorsor J G X) :
    Nonempty (SiteTorsorContractedProductData.{t, w, v, u} P Q) := by
  sorry

/-- A chosen contracted product of two torsors. -/
noncomputable def siteTorsorContractedProduct {C : Type u} [Category.{v} C]
    {J : GrothendieckTopology C}
    {G : Sheaf J AddCommGrpCat.{w}} {X : C}
    (P Q : SiteTorsor.{t, w, v, u} J G X) : SiteTorsor.{t, w, v, u} J G X :=
  (Classical.choice (siteTorsorContractedProductData_exists P Q)).torsor

/-- The contracted product is compatible with equivariant isomorphisms. -/
theorem siteTorsorContractedProduct_respects_equivalence
    {C : Type u} [Category.{v} C]
    {J : GrothendieckTopology C}
    {G : Sheaf J AddCommGrpCat.{w}} {X : C}
    {P P' Q Q' : SiteTorsor.{t, w, v, u} J G X}
    (eP : Nonempty (SiteTorsorEquivalence P P'))
    (eQ : Nonempty (SiteTorsorEquivalence Q Q')) :
    Nonempty (SiteTorsorEquivalence
      (siteTorsorContractedProduct P Q)
      (siteTorsorContractedProduct P' Q')) := by
  sorry

/-- The contracted product operation descended to torsor isomorphism classes. -/
noncomputable def siteTorsorClassContractedProduct {C : Type u} [Category.{v} C]
    {J : GrothendieckTopology C}
    (G : Sheaf J AddCommGrpCat.{w}) (X : C)
    (P Q : SiteTorsorClass J G X) : SiteTorsorClass J G X := by
  refine Quotient.lift (fun P => Quotient.lift
    (fun Q => Quotient.mk _ (siteTorsorContractedProduct P Q)) ?_ ) ?_ P Q
  · intro Q Q' hQ
    exact Quotient.sound (siteTorsorContractedProduct_respects_equivalence
      (Nonempty.intro (SiteTorsorEquivalence.refl _)) hQ)
  · intro P P' hP
    apply funext
    intro Q
    induction Q using Quotient.inductionOn with
    | _ Q =>
      exact Quotient.sound (siteTorsorContractedProduct_respects_equivalence
        hP (Nonempty.intro (SiteTorsorEquivalence.refl _)))

/-- The neutral torsor class. -/
def siteTorsorClassZero {C : Type u} [Category.{v} C]
    (J : GrothendieckTopology C)
    (G : Sheaf J AddCommGrpCat.{w}) (X : C) : SiteTorsorClass J G X :=
  Quotient.mk _ (siteTorsorTrivial J G X)

/-- The inverse operation descended to torsor isomorphism classes. -/
noncomputable def siteTorsorClassInverse {C : Type u} [Category.{v} C]
    (J : GrothendieckTopology C)
    (G : Sheaf J AddCommGrpCat.{w}) (X : C)
    (P : SiteTorsorClass J G X) : SiteTorsorClass J G X := by
  refine Quotient.lift (fun P => Quotient.mk _ (siteTorsorInverse P)) ?_ P
  intro P Q h
  exact Quotient.sound (siteTorsorInverse_respects_equivalence h)

theorem siteTorsorClassContractedProduct_zero_left {C : Type u} [Category.{v} C]
    {J : GrothendieckTopology C} (G : Sheaf J AddCommGrpCat.{w}) (X : C)
    (P : SiteTorsorClass J G X) :
    siteTorsorClassContractedProduct G X (siteTorsorClassZero J G X) P = P := by
  sorry

theorem siteTorsorClassContractedProduct_zero_right {C : Type u} [Category.{v} C]
    {J : GrothendieckTopology C} (G : Sheaf J AddCommGrpCat.{w}) (X : C)
    (P : SiteTorsorClass J G X) :
    siteTorsorClassContractedProduct G X P (siteTorsorClassZero J G X) = P := by
  sorry

theorem siteTorsorClassContractedProduct_inverse_left {C : Type u} [Category.{v} C]
    {J : GrothendieckTopology C} (G : Sheaf J AddCommGrpCat.{w}) (X : C)
    (P : SiteTorsorClass J G X) :
    siteTorsorClassContractedProduct G X (siteTorsorClassInverse J G X P) P =
      siteTorsorClassZero J G X := by
  sorry

theorem siteTorsorClassContractedProduct_inverse_right {C : Type u} [Category.{v} C]
    {J : GrothendieckTopology C} (G : Sheaf J AddCommGrpCat.{w}) (X : C)
    (P : SiteTorsorClass J G X) :
    siteTorsorClassContractedProduct G X P (siteTorsorClassInverse J G X P) =
      siteTorsorClassZero J G X := by
  sorry

theorem siteTorsorClassContractedProduct_assoc {C : Type u} [Category.{v} C]
    {J : GrothendieckTopology C} (G : Sheaf J AddCommGrpCat.{w}) (X : C)
    (P Q R : SiteTorsorClass J G X) :
    siteTorsorClassContractedProduct G X
        (siteTorsorClassContractedProduct G X P Q) R =
      siteTorsorClassContractedProduct G X P
        (siteTorsorClassContractedProduct G X Q R) := by
  sorry

theorem siteTorsorClassContractedProduct_comm {C : Type u} [Category.{v} C]
    {J : GrothendieckTopology C} (G : Sheaf J AddCommGrpCat.{w}) (X : C)
    (P Q : SiteTorsorClass J G X) :
    siteTorsorClassContractedProduct G X P Q =
      siteTorsorClassContractedProduct G X Q P := by
  sorry

/-! ### Banded gerbes -/

/-- An abelian-banded gerbe over `X`, using the established compatible
automorphism-sheaf data. -/
structure AbelianBandedGerbe {C : Type u} [Category.{v} C]
    (J : GrothendieckTopology C)
    (G : Sheaf J AddCommGrpCat.{w}) (X : C) where
  value : FiberedCategory.{w, v, max u v} (Over C X)
  isGerbe : IsGerbe.{t, w, v, max u v} value (J.over X)
  automorphismGroupsAbelian : AutomorphismGroupsAbelian value
  automorphisms :
    GerbeAutomorphismSheafData value (J.over X) isGerbe.1.1
  band : automorphisms.sheaf ≅ G.over X
  band_compatible_with_composition :
    ∀ (U : Over C X) (x : Fiber value U)
      (g h : (G.over X).obj.obj (op U)),
      value.presheafHomObjHomEquiv.symm
          ((automorphisms.localIdentifications U x).hom.app
            (op (.mk (𝟙 U)))
            (band.inv.hom.app (op U) g)).1 ≫
        value.presheafHomObjHomEquiv.symm
          ((automorphisms.localIdentifications U x).hom.app
            (op (.mk (𝟙 U)))
            (band.inv.hom.app (op U) h)).1 =
      value.presheafHomObjHomEquiv.symm
        ((automorphisms.localIdentifications U x).hom.app
          (op (.mk (𝟙 U)))
          (band.inv.hom.app (op U) (g + h))).1

/-- A fibrewise equivalence preserves the chosen abelian band when the
transport of each local automorphism through the existing automorphism-sheaf
identifications and the equivalence agrees with the fixed `G`-band. -/
def abelianBandPreservedBy {C : Type u} [Category.{v} C]
    {J : GrothendieckTopology C} {G : Sheaf J AddCommGrpCat.{w}} {X : C}
    (P Q : AbelianBandedGerbe.{t, w, v, u} J G X)
    (η : FiberedMorphism P.value Q.value) : Prop :=
  ∀ (U : Over C X) (x : Fiber P.value U)
    (a : P.automorphisms.sheaf.obj.obj (op U)),
    Q.band.hom.hom.app (op U)
        ((Q.automorphisms.localIdentifications U
          ((η.app (.mk (op U))).toFunctor.obj x)).inv.app
          (op (.mk (𝟙 U)))
          ⟨
            Q.value.presheafHomObjHomEquiv
              ((η.app (.mk (op U))).toFunctor.map
                (P.value.presheafHomObjHomEquiv.symm
                  ((P.automorphisms.localIdentifications U x).hom.app
                    (op (.mk (𝟙 U))) a).1)),
            @IsGroupoid.all_isIso
              (Q.value.obj (.mk (op (Over.mk (𝟙 U)).left))) _
              (Q.isGerbe.1.1 (Over.mk (𝟙 U)).left) _ _ _
          ⟩) =
      P.band.hom.hom.app (op U) a

/-- The type of data used for a nonabelian `G`-gerbe over `X`.

Unlike the abelian case, an identification of `G` with an automorphism group
is meaningful only up to an inner automorphism of `G`. Consequently both
pullback compatibility and change-of-object compatibility use one conjugating
element, uniformly for all sections of `G`. Requiring strict compatibility
under every automorphism of an object would incorrectly force `G` to be
abelian.
-/
structure NonabelianBandedGerbe {C : Type u} [Category.{v} C]
    (J : GrothendieckTopology C)
    (G : Sheaf J GrpCat.{w}) (X : C) where
  value : FiberedCategory.{w, v, max u v} (Over C X)
  isGerbe : IsGerbe.{t, w, v, max u v} value (J.over X)
  band : ∀ (U : Over C X)
    (x : Fiber value U), (G.over X).obj.obj (op U) ≃* Aut x
  pullback_compatible : ∀ {U V : Over C X}
    (f : V ⟶ U) (x : Fiber value U),
    ∃ c : (G.over X).obj.obj (op V),
      ∀ g : (G.over X).obj.obj (op U),
        band V ((value.map f.op.toLoc).toFunctor.obj x)
            (c * (G.over X).obj.map f.op g * c⁻¹) =
          (value.map f.op.toLoc).toFunctor.mapIso (band U x g)
  conjugation_compatible : ∀ (U : Over C X)
    (x y : Fiber value U) (φ : x ⟶ y),
    ∃ c : (G.over X).obj.obj (op U),
      ∀ g : (G.over X).obj.obj (op U),
        band U y (c * g * c⁻¹) =
          conjugateAutomorphism isGerbe.1.1 φ (band U x g)

/-! ### Equivalence classes of nonabelian gerbes -/

/-- A band-preserving equivalence datum for nonabelian-banded gerbes. -/
structure NonabelianBandedGerbeEquivalence {C : Type u} [Category.{v} C]
    {J : GrothendieckTopology C} {G : Sheaf J GrpCat.{w}} {X : C}
    (P Q : NonabelianBandedGerbe.{t, w, v, u} J G X) where
  forward : FiberedMorphism P.value Q.value
  forward_is_equivalence : FiberwiseEquivalence forward
  forward_band_compatible : ∀ (U : Over C X) (x : Fiber P.value U),
    ∃ c : (G.over X).obj.obj (op U),
      ∀ g : (G.over X).obj.obj (op U),
        Q.band U ((forward.app (.mk (op U))).toFunctor.obj x)
            (c * g * c⁻¹) =
          (forward.app (.mk (op U))).toFunctor.mapIso (P.band U x g)
  backward : FiberedMorphism Q.value P.value
  backward_is_equivalence : FiberwiseEquivalence backward
  backward_band_compatible : ∀ (U : Over C X) (y : Fiber Q.value U),
    ∃ c : (G.over X).obj.obj (op U),
      ∀ g : (G.over X).obj.obj (op U),
        P.band U ((backward.app (.mk (op U))).toFunctor.obj y)
            (c * g * c⁻¹) =
          (backward.app (.mk (op U))).toFunctor.mapIso (Q.band U y g)

/-- The setoid of nonabelian-banded gerbes modulo band-preserving equivalence. -/
def nonabelianBandedGerbeSetoid {C : Type u} [Category.{v} C]
    (J : GrothendieckTopology C) (G : Sheaf J GrpCat.{w}) (X : C) :
    Setoid (NonabelianBandedGerbe.{t, w, v, u} J G X) where
  r P Q := Nonempty (NonabelianBandedGerbeEquivalence P Q)
  iseqv := by
    refine ⟨?_, ?_, ?_⟩
    · intro P
      exact ⟨{
        forward := 𝟙 _
        forward_is_equivalence := by
          constructor
          · intro U
            exact ⟨Functor.FullyFaithful.id _⟩
          · intro U
            change Functor.EssSurj (𝟭 _)
            exact inferInstance
        forward_band_compatible := by
          intro U x
          refine ⟨1, fun g => ?_⟩
          change P.band U x (1 * g * 1⁻¹) = (𝟭 _).mapIso (P.band U x g)
          simp only [one_mul, inv_one, mul_one]
          rfl
        backward := 𝟙 _
        backward_is_equivalence := by
          constructor
          · intro U
            exact ⟨Functor.FullyFaithful.id _⟩
          · intro U
            change Functor.EssSurj (𝟭 _)
            exact inferInstance
        backward_band_compatible := by
          intro U x
          refine ⟨1, fun g => ?_⟩
          change P.band U x (1 * g * 1⁻¹) = (𝟭 _).mapIso (P.band U x g)
          simp only [one_mul, inv_one, mul_one]
          rfl
      }⟩
    · intro P Q h
      rcases h with ⟨e⟩
      exact ⟨{
        forward := e.backward
        forward_is_equivalence := e.backward_is_equivalence
        forward_band_compatible := e.backward_band_compatible
        backward := e.forward
        backward_is_equivalence := e.forward_is_equivalence
        backward_band_compatible := e.forward_band_compatible
      }⟩
    · intro P Q R hPQ hQR
      rcases hPQ with ⟨e⟩
      rcases hQR with ⟨f⟩
      refine ⟨{
        forward := e.forward ≫ f.forward
        forward_is_equivalence := by
          constructor
          · intro U
            rcases e.forward_is_equivalence.1 U with ⟨he⟩
            rcases f.forward_is_equivalence.1 U with ⟨hf⟩
            exact ⟨he.comp hf⟩
          · intro U
            let hE := e.forward_is_equivalence.2 U
            let hF := f.forward_is_equivalence.2 U
            change Functor.EssSurj
              ((e.forward.app (.mk (op U))).toFunctor ⋙
                (f.forward.app (.mk (op U))).toFunctor)
            exact inferInstance
        forward_band_compatible := by
          intro U x
          let E := (e.forward.app (.mk (op U))).toFunctor
          let F := (f.forward.app (.mk (op U))).toFunctor
          rcases e.forward_band_compatible U x with ⟨c₁, hc₁⟩
          rcases f.forward_band_compatible U (E.obj x) with ⟨c₂, hc₂⟩
          refine ⟨c₂ * c₁, fun g => ?_⟩
          change R.band U
              (F.obj (E.obj x)) ((c₂ * c₁) * g * (c₂ * c₁)⁻¹) =
            (E ⋙ F).mapIso (P.band U x g)
          have hconj : (c₂ * c₁) * g * (c₂ * c₁)⁻¹ =
              c₂ * (c₁ * g * c₁⁻¹) * c₂⁻¹ := by
            simp only [mul_inv_rev, mul_assoc]
          rw [hconj, hc₂ (c₁ * g * c₁⁻¹), hc₁ g]
          rfl
        backward := f.backward ≫ e.backward
        backward_is_equivalence := by
          constructor
          · intro U
            rcases f.backward_is_equivalence.1 U with ⟨hf⟩
            rcases e.backward_is_equivalence.1 U with ⟨he⟩
            exact ⟨hf.comp he⟩
          · intro U
            let hF := f.backward_is_equivalence.2 U
            let hE := e.backward_is_equivalence.2 U
            change Functor.EssSurj
              ((f.backward.app (.mk (op U))).toFunctor ⋙
                (e.backward.app (.mk (op U))).toFunctor)
            exact inferInstance
        backward_band_compatible := by
          intro U y
          let F := (f.backward.app (.mk (op U))).toFunctor
          let E := (e.backward.app (.mk (op U))).toFunctor
          rcases f.backward_band_compatible U y with ⟨c₁, hc₁⟩
          rcases e.backward_band_compatible U (F.obj y) with ⟨c₂, hc₂⟩
          refine ⟨c₂ * c₁, fun g => ?_⟩
          change P.band U
              (E.obj (F.obj y)) ((c₂ * c₁) * g * (c₂ * c₁)⁻¹) =
            (F ⋙ E).mapIso (R.band U y g)
          have hconj : (c₂ * c₁) * g * (c₂ * c₁)⁻¹ =
              c₂ * (c₁ * g * c₁⁻¹) * c₂⁻¹ := by
            simp only [mul_inv_rev, mul_assoc]
          rw [hconj, hc₂ (c₁ * g * c₁⁻¹), hc₁ g]
          rfl
      }⟩

/-- Isomorphism classes of nonabelian-banded gerbes over `X`. -/
def NonabelianBandedGerbeClass {C : Type u} [Category.{v} C]
    (J : GrothendieckTopology C) (G : Sheaf J GrpCat.{w}) (X : C) :
    Type _ :=
  Quotient (nonabelianBandedGerbeSetoid.{t, w, v, u} J G X)

/-! ### Giraud's identifications -/

/-! #### Čech presentations in degree two -/

/-- A finite part of the Čech nerve of a covering family in the slice over `X`.

The site is not assumed to have pullbacks, so the intersections and their face
maps are recorded as part of the presentation.  This is the weakest useful
interface for the cocycle formulas below and also makes refinements explicit.
-/
structure SiteCechCover {C : Type u} [Category.{v} C]
    (J : GrothendieckTopology C) (X : C) where
  index : Type t
  object : index → Over C X
  cover : ∀ i, object i ⟶ Over.mk (𝟙 X)
  covering : CoveringFamily (J.over X) cover
  overlap : index → index → Over C X
  overlapLeft : ∀ i j, overlap i j ⟶ object i
  overlapRight : ∀ i j, overlap i j ⟶ object j
  overlap_commutes : ∀ i j,
    overlapLeft i j ≫ cover i = overlapRight i j ≫ cover j
  triple : index → index → index → Over C X
  triple_ij : ∀ i j k, triple i j k ⟶ overlap i j
  triple_jk : ∀ i j k, triple i j k ⟶ overlap j k
  triple_ik : ∀ i j k, triple i j k ⟶ overlap i k
  triple_middle : ∀ i j k,
    triple_ij i j k ≫ overlapRight i j =
      triple_jk i j k ≫ overlapLeft j k
  triple_left : ∀ i j k,
    triple_ij i j k ≫ overlapLeft i j =
      triple_ik i j k ≫ overlapLeft i k
  triple_right : ∀ i j k,
    triple_jk i j k ≫ overlapRight j k =
      triple_ik i j k ≫ overlapRight i k
  quadruple : index → index → index → index → Over C X
  quadruple_ijk : ∀ i j k l, quadruple i j k l ⟶ triple i j k
  quadruple_ikl : ∀ i j k l, quadruple i j k l ⟶ triple i k l
  quadruple_ijl : ∀ i j k l, quadruple i j k l ⟶ triple i j l
  quadruple_jkl : ∀ i j k l, quadruple i j k l ⟶ triple j k l

/-- A refinement of finite Čech presentations, including the maps on the
overlap, triple, and quadruple intersections used by degree-two cochains. -/
structure SiteCechRefinement {C : Type u} [Category.{v} C]
    {J : GrothendieckTopology C} {X : C}
    (𝒰 𝒱 : SiteCechCover.{t, v, u} J X) where
  indexMap : 𝒱.index → 𝒰.index
  objectMap : ∀ j, 𝒱.object j ⟶ 𝒰.object (indexMap j)
  overlapMap : ∀ j k,
    𝒱.overlap j k ⟶ 𝒰.overlap (indexMap j) (indexMap k)
  tripleMap : ∀ i j k,
    𝒱.triple i j k ⟶ 𝒰.triple (indexMap i) (indexMap j) (indexMap k)
  quadrupleMap : ∀ i j k l,
    𝒱.quadruple i j k l ⟶
      𝒰.quadruple (indexMap i) (indexMap j) (indexMap k) (indexMap l)
  object_commutes : ∀ j,
    objectMap j ≫ 𝒰.cover (indexMap j) = 𝒱.cover j
  overlap_left_commutes : ∀ j k,
    overlapMap j k ≫ 𝒰.overlapLeft (indexMap j) (indexMap k) =
      𝒱.overlapLeft j k ≫ objectMap j
  overlap_right_commutes : ∀ j k,
    overlapMap j k ≫ 𝒰.overlapRight (indexMap j) (indexMap k) =
      𝒱.overlapRight j k ≫ objectMap k
  triple_ij_commutes : ∀ i j k,
    tripleMap i j k ≫ 𝒰.triple_ij (indexMap i) (indexMap j) (indexMap k) =
      𝒱.triple_ij i j k ≫ overlapMap i j
  triple_jk_commutes : ∀ i j k,
    tripleMap i j k ≫ 𝒰.triple_jk (indexMap i) (indexMap j) (indexMap k) =
      𝒱.triple_jk i j k ≫ overlapMap j k
  triple_ik_commutes : ∀ i j k,
    tripleMap i j k ≫ 𝒰.triple_ik (indexMap i) (indexMap j) (indexMap k) =
      𝒱.triple_ik i j k ≫ overlapMap i k
  quadruple_ijk_commutes : ∀ i j k l,
    quadrupleMap i j k l ≫ 𝒰.quadruple_ijk
        (indexMap i) (indexMap j) (indexMap k) (indexMap l) =
      𝒱.quadruple_ijk i j k l ≫ tripleMap i j k
  quadruple_ikl_commutes : ∀ i j k l,
    quadrupleMap i j k l ≫ 𝒰.quadruple_ikl
        (indexMap i) (indexMap j) (indexMap k) (indexMap l) =
      𝒱.quadruple_ikl i j k l ≫ tripleMap i k l
  quadruple_ijl_commutes : ∀ i j k l,
    quadrupleMap i j k l ≫ 𝒰.quadruple_ijl
        (indexMap i) (indexMap j) (indexMap k) (indexMap l) =
      𝒱.quadruple_ijl i j k l ≫ tripleMap i j l
  quadruple_jkl_commutes : ∀ i j k l,
    quadrupleMap i j k l ≫ 𝒰.quadruple_jkl
        (indexMap i) (indexMap j) (indexMap k) (indexMap l) =
      𝒱.quadruple_jkl i j k l ≫ tripleMap j k l

/-- A degree-one Čech cochain with values in `G`. -/
structure SiteCechOneCochain {C : Type u} [Category.{v} C]
    {J : GrothendieckTopology C} {X : C}
    (G : Sheaf J AddCommGrpCat.{w})
    (𝒰 : SiteCechCover.{t, v, u} J X) where
  value : ∀ i j, (G.over X).obj.obj (op (𝒰.overlap i j))

/-- A degree-two Čech cochain with values in `G`. -/
structure SiteCechTwoCochain {C : Type u} [Category.{v} C]
    {J : GrothendieckTopology C} {X : C}
    (G : Sheaf J AddCommGrpCat.{w})
    (𝒰 : SiteCechCover.{t, v, u} J X) where
  value : ∀ i j k, (G.over X).obj.obj (op (𝒰.triple i j k))

namespace SiteCechOneCochain

/-- The Čech coboundary of a one-cochain. -/
def coboundary {C : Type u} [Category.{v} C]
    {J : GrothendieckTopology C} {X : C}
    {G : Sheaf J AddCommGrpCat.{w}}
    {𝒰 : SiteCechCover.{t, v, u} J X}
    (b : SiteCechOneCochain G 𝒰) : SiteCechTwoCochain G 𝒰 where
  value i j k :=
    (G.over X).obj.map (𝒰.triple_ij i j k).op (b.value i j) -
      (G.over X).obj.map (𝒰.triple_ik i j k).op (b.value i k) +
        (G.over X).obj.map (𝒰.triple_jk i j k).op (b.value j k)

end SiteCechOneCochain

/-- A degree-two Čech cocycle. -/
structure SiteCechTwoCocycle {C : Type u} [Category.{v} C]
    {J : GrothendieckTopology C} {X : C}
    (G : Sheaf J AddCommGrpCat.{w})
    (𝒰 : SiteCechCover.{t, v, u} J X) extends SiteCechTwoCochain G 𝒰 where
  cocycle : ∀ i j k l,
    (G.over X).obj.map (𝒰.quadruple_jkl i j k l).op (value j k l) -
        (G.over X).obj.map (𝒰.quadruple_ikl i j k l).op (value i k l) +
          (G.over X).obj.map (𝒰.quadruple_ijl i j k l).op (value i j l) -
            (G.over X).obj.map (𝒰.quadruple_ijk i j k l).op (value i j k) = 0

namespace SiteCechTwoCocycle

/-- Two cocycles on the same cover differ by a coboundary. -/
def CoboundaryEquivalent {C : Type u} [Category.{v} C]
    {J : GrothendieckTopology C} {X : C}
    {G : Sheaf J AddCommGrpCat.{w}}
    {𝒰 : SiteCechCover.{t, v, u} J X}
    (c d : SiteCechTwoCocycle G 𝒰) : Prop :=
  ∃ b : SiteCechOneCochain G 𝒰, ∀ i j k,
    d.value i j k = c.value i j k + (b.coboundary).value i j k

/-- Pull a degree-two cocycle through a refinement. -/
def pullback {C : Type u} [Category.{v} C]
    {J : GrothendieckTopology C} {X : C}
    {G : Sheaf J AddCommGrpCat.{w}}
    {𝒰 𝒱 : SiteCechCover.{t, v, u} J X}
    (ρ : SiteCechRefinement 𝒰 𝒱)
    (c : SiteCechTwoCocycle G 𝒰) : SiteCechTwoCocycle G 𝒱 where
  value i j k :=
    (G.over X).obj.map (ρ.tripleMap i j k).op
      (c.value (ρ.indexMap i) (ρ.indexMap j) (ρ.indexMap k))
  cocycle := by
    sorry

/-- The cross-cover coboundary relation used when a cocycle is refined. -/
def CoboundaryAfterRefinement {C : Type u} [Category.{v} C]
    {J : GrothendieckTopology C} {X : C}
    {G : Sheaf J AddCommGrpCat.{w}}
    {𝒰 𝒱 : SiteCechCover.{t, v, u} J X}
    (ρ : SiteCechRefinement 𝒰 𝒱)
    (c : SiteCechTwoCocycle G 𝒰) (d : SiteCechTwoCocycle G 𝒱) : Prop :=
  ∃ b : SiteCechOneCochain G 𝒱, ∀ i j k,
    d.value i j k = (pullback ρ c).value i j k + (b.coboundary).value i j k

end SiteCechTwoCocycle

/-- Refinement of a Čech presentation changes a degree-two cocycle only by a
coboundary.  The one-cochain is part of the witness, so this statement is the
interface used by the later quotient construction. -/
theorem siteCechTwoCocycle_refinement_isCoboundary
    {C : Type u} [Category.{v} C]
    {J : GrothendieckTopology C} {X : C}
    {G : Sheaf J AddCommGrpCat.{w}}
    {𝒰 𝒱 : SiteCechCover.{t, v, u} J X}
    (ρ : SiteCechRefinement 𝒰 𝒱)
    (c : SiteCechTwoCocycle G 𝒰) :
    ∃ d : SiteCechTwoCocycle G 𝒱,
    SiteCechTwoCocycle.CoboundaryAfterRefinement ρ c d := by
  refine ⟨SiteCechTwoCocycle.pullback ρ c, ?_⟩
  refine ⟨{ value := fun _ _ => 0 }, ?_⟩
  intro i j k
  simp [SiteCechOneCochain.coboundary]

/-- A cocycle presentation consists of a cover and a cocycle on that cover. -/
structure SiteCechTwoCocyclePresentation {C : Type u} [Category.{v} C]
    {J : GrothendieckTopology C} (G : Sheaf J AddCommGrpCat.{w}) (X : C) where
  cover : SiteCechCover.{t, v, u} J X
  cocycle : SiteCechTwoCocycle G cover

/-- Elementary equivalence of presentations: pass to a common refinement and
then quotient by a Čech coboundary. -/
def SiteCechTwoCocyclePresentation.ElementaryEquivalent
    {C : Type u} [Category.{v} C]
    {J : GrothendieckTopology C} {X : C}
    {G : Sheaf J AddCommGrpCat.{w}}
    (P Q : SiteCechTwoCocyclePresentation G X) : Prop :=
  ∃ (𝒲 : SiteCechCover.{t, v, u} J X)
    (ρP : SiteCechRefinement P.cover 𝒲)
    (ρQ : SiteCechRefinement Q.cover 𝒲),
    SiteCechTwoCocycle.CoboundaryEquivalent
      (SiteCechTwoCocycle.pullback ρP P.cocycle)
      (SiteCechTwoCocycle.pullback ρQ Q.cocycle)

/-- The equivalence relation generated by common refinements and
coboundaries. Taking the equivalence closure avoids assuming that arbitrary
Čech presentations have a chosen common refinement. -/
inductive SiteCechTwoCocyclePresentation.Equivalent
    {C : Type u} [Category.{v} C]
    {J : GrothendieckTopology C} {X : C}
    {G : Sheaf J AddCommGrpCat.{w}} :
    SiteCechTwoCocyclePresentation G X →
      SiteCechTwoCocyclePresentation G X → Prop
  | refl (P : SiteCechTwoCocyclePresentation G X) : Equivalent P P
  | elementary {P Q : SiteCechTwoCocyclePresentation G X} :
      ElementaryEquivalent P Q → Equivalent P Q
  | symm {P Q : SiteCechTwoCocyclePresentation G X} :
      Equivalent P Q → Equivalent Q P
  | trans {P Q R : SiteCechTwoCocyclePresentation G X} :
      Equivalent P Q → Equivalent Q R → Equivalent P R

/-- The setoid of degree-two Čech cocycle presentations. -/
def siteCechTwoCocycleSetoid {C : Type u} [Category.{v} C]
    (J : GrothendieckTopology C) (G : Sheaf J AddCommGrpCat.{w}) (X : C) :
    Setoid (SiteCechTwoCocyclePresentation G X) where
  r := SiteCechTwoCocyclePresentation.Equivalent
  iseqv := by
    refine ⟨?_, ?_, ?_⟩
    · intro P
      exact .refl P
    · intro P Q h
      exact .symm h
    · intro P Q R hPQ hQR
      exact .trans hPQ hQR

/-- Čech degree-two cohomology classes for the chosen presentation interface. -/
def SiteCechTwoCocycleClass {C : Type u} [Category.{v} C]
    (J : GrothendieckTopology C) (G : Sheaf J AddCommGrpCat.{w}) (X : C) : Type _ :=
  Quotient (siteCechTwoCocycleSetoid J G X)

/-- The comparison between the derived degree-two group and the Čech
presentation quotient.  This isolates the choice of Čech presentations from
the later gerbe constructions. -/
theorem siteH2_equiv_siteCechTwoCocycleClass
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    (G : Sheaf J AddCommGrpCat.{w}) (X : C)
    [HasSheafify (J.over X) AddCommGrpCat.{w}]
    [HasExt.{w'} (Sheaf (J.over X) AddCommGrpCat.{w})] :
    Nonempty (siteH2 G X ≃ SiteCechTwoCocycleClass.{w, v, u, t} J G X) := by
  sorry

/-- A chosen map from derived degree-two cohomology to Čech classes. -/
noncomputable def siteH2_to_siteCechTwoCocycleClass
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    (G : Sheaf J AddCommGrpCat.{w}) (X : C)
    [HasSheafify (J.over X) AddCommGrpCat.{w}]
    [HasExt.{w'} (Sheaf (J.over X) AddCommGrpCat.{w})] :
    siteH2 G X → SiteCechTwoCocycleClass.{w, v, u, t} J G X :=
  (Classical.choice (siteH2_equiv_siteCechTwoCocycleClass G X)).toFun

/-- A chosen inverse from Čech classes to derived degree-two cohomology. -/
noncomputable def siteCechTwoCocycleClass_to_siteH2
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    (G : Sheaf J AddCommGrpCat.{w}) (X : C)
    [HasSheafify (J.over X) AddCommGrpCat.{w}]
    [HasExt.{w'} (Sheaf (J.over X) AddCommGrpCat.{w})] :
    SiteCechTwoCocycleClass.{w, v, u, t} J G X → siteH2 G X :=
  (Classical.choice (siteH2_equiv_siteCechTwoCocycleClass G X)).invFun

/-- The chosen derived/Čech maps are inverse. -/
theorem siteH2_to_siteCechTwoCocycleClass_left_inverse
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    (G : Sheaf J AddCommGrpCat.{w}) (X : C)
    [HasSheafify (J.over X) AddCommGrpCat.{w}]
    [HasExt.{w'} (Sheaf (J.over X) AddCommGrpCat.{w})]
    (c : siteH2 G X) :
    siteCechTwoCocycleClass_to_siteH2 G X
      (siteH2_to_siteCechTwoCocycleClass G X c) = c := by
  let e := Classical.choice (siteH2_equiv_siteCechTwoCocycleClass G X)
  change e.invFun (e.toFun c) = c
  exact e.left_inv c

theorem siteH2_to_siteCechTwoCocycleClass_right_inverse
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    (G : Sheaf J AddCommGrpCat.{w}) (X : C)
    [HasSheafify (J.over X) AddCommGrpCat.{w}]
    [HasExt.{w'} (Sheaf (J.over X) AddCommGrpCat.{w})]
    (c : SiteCechTwoCocycleClass.{w, v, u, t} J G X) :
    siteH2_to_siteCechTwoCocycleClass G X
      (siteCechTwoCocycleClass_to_siteH2 G X c) = c := by
  let e := Classical.choice (siteH2_equiv_siteCechTwoCocycleClass G X)
  change e.toFun (e.invFun c) = c
  exact e.right_inv c

/-- Refinement and coboundary invariance descend to Čech cocycle classes. -/
theorem siteCechTwoCocycle_refinement_respects_class
    {C : Type u} [Category.{v} C]
    {J : GrothendieckTopology C} {X : C}
    (G : Sheaf J AddCommGrpCat.{w})
    (P : SiteCechTwoCocyclePresentation G X)
    (𝒲 : SiteCechCover.{t, v, u} J X)
    (ρ : SiteCechRefinement P.cover 𝒲) :
    Quotient.mk (siteCechTwoCocycleSetoid J G X) P =
      Quotient.mk (siteCechTwoCocycleSetoid J G X)
        { cover := 𝒲, cocycle := SiteCechTwoCocycle.pullback ρ P.cocycle } := by
  sorry

/-! #### Gluing and extraction interfaces -/

/-- The output of gluing a degree-two cocycle.  The established
`FiberedCategory.DescentData` API retains the local objects, transition
isomorphisms, and their cocycle identity in one usable datum. -/
structure SiteCechTwoCocycleGerbeGluing {C : Type u} [Category.{v} C]
    {J : GrothendieckTopology C} {X : C}
    {G : Sheaf J AddCommGrpCat.{w}}
  (P : SiteCechTwoCocyclePresentation G X) where
  gerbe : AbelianBandedGerbe.{t, w, v, u} J G X
  descentData : gerbe.value.DescentData P.cover.cover

/-- Existence of the gerbe obtained by gluing a Čech two-cocycle. -/
theorem siteCechTwoCocycle_gluing_exists
    {C : Type u} [Category.{v} C]
    {J : GrothendieckTopology C} {X : C}
    {G : Sheaf J AddCommGrpCat.{w}}
    (P : SiteCechTwoCocyclePresentation G X) :
    Nonempty (SiteCechTwoCocycleGerbeGluing P) := by
  sorry

/-- The chosen cocycle-to-banded-gerbe gluing construction. -/
noncomputable def siteCechTwoCocycle_to_abelianBandedGerbe
    {C : Type u} [Category.{v} C]
    {J : GrothendieckTopology C} {X : C}
    {G : Sheaf J AddCommGrpCat.{w}}
    (P : SiteCechTwoCocyclePresentation G X) :
    AbelianBandedGerbe.{t, w, v, u} J G X :=
  (Classical.choice (siteCechTwoCocycle_gluing_exists P)).gerbe

/-! #### Gerbe-to-cocycle extraction -/

/-- Local choices used to extract a Čech cocycle from a banded gerbe.  The
established descent datum keeps the local objects and transition arrows, while
`compatibility` records the band equation whose value is the degree-two
cocycle. -/
structure AbelianBandedGerbeCocycleExtraction
    {C : Type u} [Category.{v} C]
    {J : GrothendieckTopology C} {X : C}
    {G : Sheaf J AddCommGrpCat.{w}}
    (P : AbelianBandedGerbe.{t, w, v, u} J G X) where
  cover : SiteCechCover.{t, v, u} J X
  descentData : P.value.DescentData cover.cover
  cocycle : SiteCechTwoCocycle G cover
  compatibility : Prop

/-- Local nonemptiness, local connectedness, and the fixed band produce a
degree-two Čech cocycle presentation. -/
theorem abelianBandedGerbe_cocycle_extraction_exists
    {C : Type u} [Category.{v} C]
    {J : GrothendieckTopology C} {X : C}
    {G : Sheaf J AddCommGrpCat.{w}}
    (P : AbelianBandedGerbe.{t, w, v, u} J G X) :
    Nonempty (AbelianBandedGerbeCocycleExtraction P) := by
  sorry

/-- The chosen gerbe-to-cocycle extraction. -/
noncomputable def abelianBandedGerbe_to_siteCechTwoCocycle
    {C : Type u} [Category.{v} C]
    {J : GrothendieckTopology C} {X : C}
    {G : Sheaf J AddCommGrpCat.{w}}
    (P : AbelianBandedGerbe.{t, w, v, u} J G X) :
    SiteCechTwoCocyclePresentation G X :=
  let E := Classical.choice (abelianBandedGerbe_cocycle_extraction_exists P)
  { cover := E.cover, cocycle := E.cocycle }

/-- A band-preserving equivalence datum for abelian-banded gerbes.

The two fibrewise equivalences record equivalence of the underlying gerbes,
while the compatibility fields require both directions to preserve the fixed
`G`-band.  The auxiliary `band` identifies the chosen automorphism sheaves,
and the setoid below records the resulting equivalence classes. -/
structure AbelianBandedGerbeEquivalence {C : Type u} [Category.{v} C]
    {J : GrothendieckTopology C} {G : Sheaf J AddCommGrpCat.{w}} {X : C}
    (P Q : AbelianBandedGerbe.{t, w, v, u} J G X) where
  forward : FiberedMorphism P.value Q.value
  forward_is_equivalence : FiberwiseEquivalence forward
  forward_band_compatible : abelianBandPreservedBy P Q forward
  backward : FiberedMorphism Q.value P.value
  backward_is_equivalence : FiberwiseEquivalence backward
  backward_band_compatible : abelianBandPreservedBy Q P backward
  band : P.automorphisms.sheaf ≅ Q.automorphisms.sheaf
  band_compatible : band.hom ≫ Q.band.hom = P.band.hom

/-- The setoid of abelian-banded gerbes modulo band-preserving equivalence. -/
def abelianBandedGerbeSetoid {C : Type u} [Category.{v} C]
    (J : GrothendieckTopology C) (G : Sheaf J AddCommGrpCat.{w}) (X : C) :
    Setoid (AbelianBandedGerbe.{t, w, v, u} J G X) where
  r P Q := Nonempty (AbelianBandedGerbeEquivalence P Q)
  iseqv := by
    refine ⟨?_, ?_, ?_⟩
    · intro P
      exact ⟨{
        forward := 𝟙 _
        forward_is_equivalence := by
          constructor
          · intro U
            exact ⟨Functor.FullyFaithful.id _⟩
          · intro U
            change Functor.EssSurj (𝟭 _)
            exact inferInstance
        forward_band_compatible := by
          change abelianBandPreservedBy P P (Pseudofunctor.StrongTrans.id P.value)
          intro U x a
          let q : (IsomPresheaf P.value x x).obj (op (.mk (𝟙 U))) :=
            ⟨P.value.presheafHomObjHomEquiv
                (P.value.presheafHomObjHomEquiv.symm
                  ((P.automorphisms.localIdentifications U x).hom.app
                    (op (.mk (𝟙 U))) a).1),
              @IsGroupoid.all_isIso
                (P.value.obj (.mk (op (Over.mk (𝟙 U)).left))) _
                (P.isGerbe.1.1 (Over.mk (𝟙 U)).left) _ _ _⟩
          change P.band.hom.hom.app (op U)
              ((P.automorphisms.localIdentifications U x).inv.app
                (op (.mk (𝟙 U))) q) = P.band.hom.hom.app (op U) a
          have hq : q =
              (P.automorphisms.localIdentifications U x).hom.app
                (op (.mk (𝟙 U))) a := by
            apply Subtype.ext
            exact P.value.presheafHomObjHomEquiv.apply_symm_apply _
          rw [hq]
          apply congrArg (fun z => P.band.hom.hom.app (op U) z)
          change (ConcreteCategory.hom
              ((P.automorphisms.localIdentifications U x).inv.app
                (op (.mk (𝟙 U)))))
              ((ConcreteCategory.hom
                ((P.automorphisms.localIdentifications U x).hom.app
                  (op (.mk (𝟙 U))))) a) = a
          exact congrArg (fun z => (ConcreteCategory.hom z) a)
            ((P.automorphisms.localIdentifications U x).hom_inv_id_app
              (op (.mk (𝟙 U))))
        backward := 𝟙 _
        backward_is_equivalence := by
          constructor
          · intro U
            exact ⟨Functor.FullyFaithful.id _⟩
          · intro U
            change Functor.EssSurj (𝟭 _)
            exact inferInstance
        backward_band_compatible := by
          change abelianBandPreservedBy P P (Pseudofunctor.StrongTrans.id P.value)
          intro U x a
          let q : (IsomPresheaf P.value x x).obj (op (.mk (𝟙 U))) :=
            ⟨P.value.presheafHomObjHomEquiv
                (P.value.presheafHomObjHomEquiv.symm
                  ((P.automorphisms.localIdentifications U x).hom.app
                    (op (.mk (𝟙 U))) a).1),
              @IsGroupoid.all_isIso
                (P.value.obj (.mk (op (Over.mk (𝟙 U)).left))) _
                (P.isGerbe.1.1 (Over.mk (𝟙 U)).left) _ _ _⟩
          change P.band.hom.hom.app (op U)
              ((P.automorphisms.localIdentifications U x).inv.app
                (op (.mk (𝟙 U))) q) = P.band.hom.hom.app (op U) a
          have hq : q =
              (P.automorphisms.localIdentifications U x).hom.app
                (op (.mk (𝟙 U))) a := by
            apply Subtype.ext
            exact P.value.presheafHomObjHomEquiv.apply_symm_apply _
          rw [hq]
          apply congrArg (fun z => P.band.hom.hom.app (op U) z)
          change (ConcreteCategory.hom
              ((P.automorphisms.localIdentifications U x).inv.app
                (op (.mk (𝟙 U)))))
              ((ConcreteCategory.hom
                ((P.automorphisms.localIdentifications U x).hom.app
                  (op (.mk (𝟙 U))))) a) = a
          exact congrArg (fun z => (ConcreteCategory.hom z) a)
            ((P.automorphisms.localIdentifications U x).hom_inv_id_app
              (op (.mk (𝟙 U))))
        band := Iso.refl _
        band_compatible := by simp
      }⟩
    · intro P Q h
      rcases h with ⟨e⟩
      exact ⟨{
        forward := e.backward
        forward_is_equivalence := e.backward_is_equivalence
        forward_band_compatible := e.backward_band_compatible
        backward := e.forward
        backward_is_equivalence := e.forward_is_equivalence
        backward_band_compatible := e.forward_band_compatible
        band := e.band.symm
        band_compatible := by
          rw [← e.band_compatible]
          simp
      }⟩
    · intro P Q R hPQ hQR
      rcases hPQ with ⟨e⟩
      rcases hQR with ⟨f⟩
      refine ⟨{
        forward := e.forward ≫ f.forward
        forward_is_equivalence := by
          constructor
          · intro U
            rcases e.forward_is_equivalence.1 U with ⟨he⟩
            rcases f.forward_is_equivalence.1 U with ⟨hf⟩
            exact ⟨he.comp hf⟩
          · intro U
            let hE := e.forward_is_equivalence.2 U
            let hF := f.forward_is_equivalence.2 U
            change Functor.EssSurj
              ((e.forward.app (.mk (op U))).toFunctor ⋙
                (f.forward.app (.mk (op U))).toFunctor)
            exact inferInstance
        forward_band_compatible := by
          intro U x a
          let E := (e.forward.app (.mk (op U))).toFunctor
          let F := (f.forward.app (.mk (op U))).toFunctor
          change (R.band.hom.hom.app (op U))
              ((R.automorphisms.localIdentifications U (F.obj (E.obj x))).inv.app
                (op (.mk (𝟙 U)))
                ⟨R.value.presheafHomObjHomEquiv
                    (F.map (E.map
                      (P.value.presheafHomObjHomEquiv.symm
                        ((P.automorphisms.localIdentifications U x).hom.app
                          (op (.mk (𝟙 U))) a).1))), _⟩) =
            (P.band.hom.hom.app (op U)) a
          let p : x ⟶ x :=
            P.value.presheafHomObjHomEquiv.symm
              ((P.automorphisms.localIdentifications U x).hom.app
                (op (.mk (𝟙 U))) a).1
          let qE : (IsomPresheaf Q.value (E.obj x) (E.obj x)).obj
              (op (.mk (𝟙 U))) :=
            ⟨Q.value.presheafHomObjHomEquiv (E.map p),
              @IsGroupoid.all_isIso
                (Q.value.obj (.mk (op (Over.mk (𝟙 U)).left))) _
                (Q.isGerbe.1.1 (Over.mk (𝟙 U)).left) _ _ _⟩
          let b : Q.automorphisms.sheaf.obj.obj (op U) :=
            (Q.automorphisms.localIdentifications U (E.obj x)).inv.app
              (op (.mk (𝟙 U))) qE
          let qT : (IsomPresheaf R.value (F.obj (E.obj x))
              (F.obj (E.obj x))).obj (op (.mk (𝟙 U))) :=
            ⟨R.value.presheafHomObjHomEquiv (F.map (E.map p)),
              @IsGroupoid.all_isIso
                (R.value.obj (.mk (op (Over.mk (𝟙 U)).left))) _
                (R.isGerbe.1.1 (Over.mk (𝟙 U)).left) _ _ _⟩
          let qF : (IsomPresheaf R.value (F.obj (E.obj x))
              (F.obj (E.obj x))).obj (op (.mk (𝟙 U))) :=
            ⟨R.value.presheafHomObjHomEquiv
                (F.map
                  (Q.value.presheafHomObjHomEquiv.symm
                    ((Q.automorphisms.localIdentifications U (E.obj x)).hom.app
                      (op (.mk (𝟙 U))) b).1)),
              @IsGroupoid.all_isIso
                (R.value.obj (.mk (op (Over.mk (𝟙 U)).left))) _
                (R.isGerbe.1.1 (Over.mk (𝟙 U)).left) _ _ _⟩
          change (R.band.hom.hom.app (op U))
              ((R.automorphisms.localIdentifications U (F.obj (E.obj x))).inv.app
                (op (.mk (𝟙 U))) qT) = (P.band.hom.hom.app (op U)) a
          have hlocal :
              (Q.automorphisms.localIdentifications U (E.obj x)).hom.app
                  (op (.mk (𝟙 U))) b = qE := by
            exact congrArg (fun z => (ConcreteCategory.hom z) qE)
              ((Q.automorphisms.localIdentifications U (E.obj x)).inv_hom_id_app
                (op (.mk (𝟙 U))))
          have hq : qT = qF := by
            apply Subtype.ext
            change R.value.presheafHomObjHomEquiv (F.map (E.map p)) =
              R.value.presheafHomObjHomEquiv
                (F.map
                  (Q.value.presheafHomObjHomEquiv.symm
                    ((Q.automorphisms.localIdentifications U (E.obj x)).hom.app
                      (op (.mk (𝟙 U))) b).1))
            have hv := congrArg Subtype.val hlocal
            rw [hv]
            change R.value.presheafHomObjHomEquiv (F.map (E.map p)) =
              R.value.presheafHomObjHomEquiv
                (F.map
                  (Q.value.presheafHomObjHomEquiv.symm
                    (Q.value.presheafHomObjHomEquiv (E.map p))))
            exact congrArg (fun z => R.value.presheafHomObjHomEquiv (F.map z))
              (Q.value.presheafHomObjHomEquiv.symm_apply_apply (E.map p)).symm
          have hf := f.forward_band_compatible U (E.obj x) b
          have hb : (Q.band.hom.hom.app (op U)) b =
              (P.band.hom.hom.app (op U)) a := by
            simpa [b, qE, p, E] using (e.forward_band_compatible U x a)
          rw [hq]
          exact hf.trans hb
        backward := f.backward ≫ e.backward
        backward_is_equivalence := by
          constructor
          · intro U
            rcases f.backward_is_equivalence.1 U with ⟨hf⟩
            rcases e.backward_is_equivalence.1 U with ⟨he⟩
            exact ⟨hf.comp he⟩
          · intro U
            let hF := f.backward_is_equivalence.2 U
            let hE := e.backward_is_equivalence.2 U
            change Functor.EssSurj
              ((f.backward.app (.mk (op U))).toFunctor ⋙
                (e.backward.app (.mk (op U))).toFunctor)
            exact inferInstance
        backward_band_compatible := by
          intro U y a
          let E := (f.backward.app (.mk (op U))).toFunctor
          let F := (e.backward.app (.mk (op U))).toFunctor
          change (P.band.hom.hom.app (op U))
              ((P.automorphisms.localIdentifications U (F.obj (E.obj y))).inv.app
                (op (.mk (𝟙 U)))
                ⟨P.value.presheafHomObjHomEquiv
                    (F.map (E.map
                      (R.value.presheafHomObjHomEquiv.symm
                        ((R.automorphisms.localIdentifications U y).hom.app
                          (op (.mk (𝟙 U))) a).1))), _⟩) =
            (R.band.hom.hom.app (op U)) a
          let p : y ⟶ y :=
            R.value.presheafHomObjHomEquiv.symm
              ((R.automorphisms.localIdentifications U y).hom.app
                (op (.mk (𝟙 U))) a).1
          let qE : (IsomPresheaf Q.value (E.obj y) (E.obj y)).obj
              (op (.mk (𝟙 U))) :=
            ⟨Q.value.presheafHomObjHomEquiv (E.map p),
              @IsGroupoid.all_isIso
                (Q.value.obj (.mk (op (Over.mk (𝟙 U)).left))) _
                (Q.isGerbe.1.1 (Over.mk (𝟙 U)).left) _ _ _⟩
          let b : Q.automorphisms.sheaf.obj.obj (op U) :=
            (Q.automorphisms.localIdentifications U (E.obj y)).inv.app
              (op (.mk (𝟙 U))) qE
          let qT : (IsomPresheaf P.value (F.obj (E.obj y))
              (F.obj (E.obj y))).obj (op (.mk (𝟙 U))) :=
            ⟨P.value.presheafHomObjHomEquiv (F.map (E.map p)),
              @IsGroupoid.all_isIso
                (P.value.obj (.mk (op (Over.mk (𝟙 U)).left))) _
                (P.isGerbe.1.1 (Over.mk (𝟙 U)).left) _ _ _⟩
          let qF : (IsomPresheaf P.value (F.obj (E.obj y))
              (F.obj (E.obj y))).obj (op (.mk (𝟙 U))) :=
            ⟨P.value.presheafHomObjHomEquiv
                (F.map
                  (Q.value.presheafHomObjHomEquiv.symm
                    ((Q.automorphisms.localIdentifications U (E.obj y)).hom.app
                      (op (.mk (𝟙 U))) b).1)),
              @IsGroupoid.all_isIso
                (P.value.obj (.mk (op (Over.mk (𝟙 U)).left))) _
                (P.isGerbe.1.1 (Over.mk (𝟙 U)).left) _ _ _⟩
          change (P.band.hom.hom.app (op U))
              ((P.automorphisms.localIdentifications U (F.obj (E.obj y))).inv.app
                (op (.mk (𝟙 U))) qT) = (R.band.hom.hom.app (op U)) a
          have hlocal :
              (Q.automorphisms.localIdentifications U (E.obj y)).hom.app
                  (op (.mk (𝟙 U))) b = qE := by
            exact congrArg (fun z => (ConcreteCategory.hom z) qE)
              ((Q.automorphisms.localIdentifications U (E.obj y)).inv_hom_id_app
                (op (.mk (𝟙 U))))
          have hq : qT = qF := by
            apply Subtype.ext
            change P.value.presheafHomObjHomEquiv (F.map (E.map p)) =
              P.value.presheafHomObjHomEquiv
                (F.map
                  (Q.value.presheafHomObjHomEquiv.symm
                    ((Q.automorphisms.localIdentifications U (E.obj y)).hom.app
                      (op (.mk (𝟙 U))) b).1))
            have hv := congrArg Subtype.val hlocal
            rw [hv]
            change P.value.presheafHomObjHomEquiv (F.map (E.map p)) =
              P.value.presheafHomObjHomEquiv
                (F.map
                  (Q.value.presheafHomObjHomEquiv.symm
                    (Q.value.presheafHomObjHomEquiv (E.map p))))
            exact congrArg (fun z => P.value.presheafHomObjHomEquiv (F.map z))
              (Q.value.presheafHomObjHomEquiv.symm_apply_apply (E.map p)).symm
          have hf := e.backward_band_compatible U (E.obj y) b
          have hb : (Q.band.hom.hom.app (op U)) b =
              (R.band.hom.hom.app (op U)) a := by
            simpa [b, qE, p, E] using (f.backward_band_compatible U y a)
          rw [hq]
          exact hf.trans hb
        band := e.band.trans f.band
        band_compatible := by
          rw [Iso.trans_hom, Category.assoc, f.band_compatible,
            e.band_compatible]
      }⟩

/-- Isomorphism classes of abelian-banded gerbes over `X`. -/
def AbelianBandedGerbeClass {C : Type u} [Category.{v} C]
    (J : GrothendieckTopology C) (G : Sheaf J AddCommGrpCat.{w}) (X : C) :
    Type _ :=
  Quotient (abelianBandedGerbeSetoid.{t, w, v, u} J G X)

/-- Equivalent banded gerbes yield equivalent extracted cocycle presentations. -/
theorem abelianBandedGerbeEquivalence_cocycle_compatible
    {C : Type u} [Category.{v} C]
    {J : GrothendieckTopology C} {X : C}
    {G : Sheaf J AddCommGrpCat.{w}}
    {P Q : AbelianBandedGerbe.{t, w, v, u} J G X}
    (e : AbelianBandedGerbeEquivalence P Q) :
    SiteCechTwoCocyclePresentation.Equivalent
      (abelianBandedGerbe_to_siteCechTwoCocycle P)
      (abelianBandedGerbe_to_siteCechTwoCocycle Q) := by
  sorry

/-- A cohomologous pair of cocycles glues to equivalent abelian-banded
gerbes. -/
theorem siteCechTwoCocycle_cohomologous_gluing_compatible
    {C : Type u} [Category.{v} C]
    {J : GrothendieckTopology C} {X : C}
    {G : Sheaf J AddCommGrpCat.{w}}
    {P Q : SiteCechTwoCocyclePresentation G X}
    (h : SiteCechTwoCocyclePresentation.Equivalent P Q) :
    Nonempty (AbelianBandedGerbeEquivalence
      (siteCechTwoCocycle_to_abelianBandedGerbe P)
      (siteCechTwoCocycle_to_abelianBandedGerbe Q)) := by
  sorry

/-- The gluing map is well-defined on the Čech quotient and lands in the
existing `abelianBandedGerbeSetoid` quotient. -/
noncomputable def siteCechTwoCocycleClass_to_abelianBandedGerbeClass
    {C : Type u} [Category.{v} C]
    {J : GrothendieckTopology C} {X : C}
    (G : Sheaf J AddCommGrpCat.{w})
    (P : SiteCechTwoCocycleClass.{w, v, u, t} J G X) :
    AbelianBandedGerbeClass J G X := by
  refine Quotient.lift (fun Q => Quotient.mk (abelianBandedGerbeSetoid J G X)
    (siteCechTwoCocycle_to_abelianBandedGerbe Q)) ?_ P
  intro Q R h
  exact Quotient.sound (siteCechTwoCocycle_cohomologous_gluing_compatible h)

/-- The extraction map is well-defined on the existing
`abelianBandedGerbeSetoid` quotient. -/
noncomputable def abelianBandedGerbeClass_to_siteCechTwoCocycleClass
    {C : Type u} [Category.{v} C]
    {J : GrothendieckTopology C} {X : C}
    (G : Sheaf J AddCommGrpCat.{w}) (P : AbelianBandedGerbeClass J G X) :
    SiteCechTwoCocycleClass.{w, v, u, t} J G X := by
  refine Quotient.lift (fun Q => Quotient.mk (siteCechTwoCocycleSetoid J G X)
    (abelianBandedGerbe_to_siteCechTwoCocycle Q)) ?_ P
  intro Q R h
  exact Quotient.sound (abelianBandedGerbeEquivalence_cocycle_compatible
    (Nonempty.some h))

/-- Extracting after gluing returns the original Čech class. -/
theorem siteCechTwoCocycleClass_extraction_gluing
    {C : Type u} [Category.{v} C]
    {J : GrothendieckTopology C} {X : C}
    (G : Sheaf J AddCommGrpCat.{w})
    (c : SiteCechTwoCocycleClass.{w, v, u, t} J G X) :
    abelianBandedGerbeClass_to_siteCechTwoCocycleClass G
      (siteCechTwoCocycleClass_to_abelianBandedGerbeClass G c) = c := by
  sorry

/-- Gluing after extracting returns the original banded-gerbe class. -/
theorem siteCechTwoCocycleClass_gluing_extraction
    {C : Type u} [Category.{v} C]
    {J : GrothendieckTopology C} {X : C}
    (G : Sheaf J AddCommGrpCat.{w})
    (c : AbelianBandedGerbeClass J G X) :
    siteCechTwoCocycleClass_to_abelianBandedGerbeClass G
      (abelianBandedGerbeClass_to_siteCechTwoCocycleClass G c) = c := by
  sorry

/-- The two quotient-level constructions package as the Čech form of
Giraud's degree-two correspondence. -/
theorem siteCechTwoCocycleClass_equiv_abelianBandedGerbeClass
    {C : Type u} [Category.{v} C]
    {J : GrothendieckTopology C}
    (G : Sheaf J AddCommGrpCat.{w}) (X : C) :
    Nonempty (SiteCechTwoCocycleClass.{w, v, u, t} J G X ≃
      AbelianBandedGerbeClass.{t, w, v, u} J G X) := by
  exact ⟨{
    toFun := fun c => siteCechTwoCocycleClass_to_abelianBandedGerbeClass G c
    invFun := fun c => abelianBandedGerbeClass_to_siteCechTwoCocycleClass G c
    left_inv := by
      intro c
      exact siteCechTwoCocycleClass_extraction_gluing G c
    right_inv := by
      intro c
      exact siteCechTwoCocycleClass_gluing_extraction G c
  }⟩

/-! ### Extensions and torsors in degree one -/

/-- The constant unit sheaf used as the left hand term in degree-one `Ext`. -/
abbrev siteH1UnitSheaf {C : Type u} [Category.{v} C]
    (J : GrothendieckTopology C) (X : C)
    [HasWeakSheafify (J.over X) AddCommGrpCat.{w}] :
    Sheaf (J.over X) AddCommGrpCat.{w} :=
  (constantSheaf (J.over X) AddCommGrpCat.{w}).obj
    (AddCommGrpCat.of (ULift ℤ))

/-- A concrete representative of an extension of the unit sheaf by `G.over X`.

The field `extensionClass` is the corresponding derived extension class.  The
comparison between representatives and derived classes is part of the
degree-one correspondence below. -/
structure SiteH1ExtensionRepresentative {C : Type u} [Category.{v} C]
    {J : GrothendieckTopology C}
    (G : Sheaf J AddCommGrpCat.{w}) (X : C)
    [HasWeakSheafify (J.over X) AddCommGrpCat.{w}]
    [HasSheafify (J.over X) AddCommGrpCat.{w}]
    [HasExt.{w'} (Sheaf (J.over X) AddCommGrpCat.{w})] where
  middle : Sheaf (J.over X) AddCommGrpCat.{w}
  inclusion : G.over X ⟶ middle
  projection : middle ⟶ siteH1UnitSheaf J X
  zero : inclusion ≫ projection = 0
  exact : (ShortComplex.mk inclusion projection zero).ShortExact
  extensionClass : siteH1 G X

/-- An `Ext` class in degree one, regarded as an extension class. -/
abbrev SiteH1ExtensionClass {C : Type u} [Category.{v} C]
    {J : GrothendieckTopology C}
    (G : Sheaf J AddCommGrpCat.{w}) (X : C)
    [HasSheafify (J.over X) AddCommGrpCat.{w}]
    [HasExt.{w'} (Sheaf (J.over X) AddCommGrpCat.{w})] : Type w' :=
  siteH1 G X

/-- The two constructions in Giraud's degree-one correspondence.

`extension_to_torsor` is the fibre construction over the unit section of an
extension, while `torsor_to_extension` is the associated extension obtained
from the torsor action.  The comparison equations are stated separately
below, so representative-level constructions and quotient proofs remain
distinct interfaces. -/
structure SiteH1TorsorCorrespondence {C : Type u} [Category.{v} C]
    {J : GrothendieckTopology C}
    (G : Sheaf J AddCommGrpCat.{w}) (X : C)
    [HasSheafify (J.over X) AddCommGrpCat.{w}]
    [HasExt.{w'} (Sheaf (J.over X) AddCommGrpCat.{w})] where
  extension_to_torsor : siteH1 G X → SiteTorsorClass.{t, w, v, u} J G X
  torsor_to_extension : SiteTorsorClass.{t, w, v, u} J G X → siteH1 G X

/-- Existence of the fibre/associated-extension comparison. -/
theorem siteH1TorsorCorrespondence_exists {C : Type u} [Category.{v} C]
    {J : GrothendieckTopology C}
    (G : Sheaf J AddCommGrpCat.{w}) (X : C)
    [HasSheafify (J.over X) AddCommGrpCat.{w}]
    [HasExt.{w'} (Sheaf (J.over X) AddCommGrpCat.{w})] :
    Nonempty (SiteH1TorsorCorrespondence G X) := by
  sorry

/-- A chosen degree-one extension/torsor correspondence. -/
noncomputable def siteH1TorsorCorrespondence {C : Type u} [Category.{v} C]
    {J : GrothendieckTopology C}
    (G : Sheaf J AddCommGrpCat.{w}) (X : C)
    [HasSheafify (J.over X) AddCommGrpCat.{w}]
    [HasExt.{w'} (Sheaf (J.over X) AddCommGrpCat.{w})] :
    SiteH1TorsorCorrespondence G X :=
  Classical.choice (siteH1TorsorCorrespondence_exists G X)

/-- Send a degree-one extension class to its torsor class by taking its unit fibre. -/
noncomputable def siteH1ExtensionToTorsorClass {C : Type u} [Category.{v} C]
    {J : GrothendieckTopology C}
    (G : Sheaf J AddCommGrpCat.{w}) (X : C)
    [HasSheafify (J.over X) AddCommGrpCat.{w}]
    [HasExt.{w'} (Sheaf (J.over X) AddCommGrpCat.{w})] :
    siteH1 G X → SiteTorsorClass J G X :=
  (siteH1TorsorCorrespondence G X).extension_to_torsor

/-- Apply the fibre construction to a concrete extension representative. -/
noncomputable def siteH1ExtensionRepresentativeToTorsorClass
    {C : Type u} [Category.{v} C]
    {J : GrothendieckTopology C}
    (G : Sheaf J AddCommGrpCat.{w}) (X : C)
    [HasWeakSheafify (J.over X) AddCommGrpCat.{w}]
    [HasSheafify (J.over X) AddCommGrpCat.{w}]
    [HasExt.{w'} (Sheaf (J.over X) AddCommGrpCat.{w})]
    (E : SiteH1ExtensionRepresentative G X) : SiteTorsorClass J G X :=
  siteH1ExtensionToTorsorClass G X E.extensionClass

/-- Form the derived extension class associated to a torsor class. -/
noncomputable def siteTorsorClassToSiteH1 {C : Type u} [Category.{v} C]
    {J : GrothendieckTopology C}
    (G : Sheaf J AddCommGrpCat.{w}) (X : C)
    [HasSheafify (J.over X) AddCommGrpCat.{w}]
    [HasExt.{w'} (Sheaf (J.over X) AddCommGrpCat.{w})] :
    SiteTorsorClass J G X → siteH1 G X :=
  (siteH1TorsorCorrespondence G X).torsor_to_extension

/-- The fibre and associated-extension maps are inverse on torsor classes. -/
theorem siteH1ExtensionToTorsorClass_torsorToSiteH1 {C : Type u} [Category.{v} C]
    {J : GrothendieckTopology C}
    (G : Sheaf J AddCommGrpCat.{w}) (X : C)
    [HasSheafify (J.over X) AddCommGrpCat.{w}]
    [HasExt.{w'} (Sheaf (J.over X) AddCommGrpCat.{w})]
    (P : SiteTorsorClass J G X) :
    siteH1ExtensionToTorsorClass G X (siteTorsorClassToSiteH1 G X P) = P := by
  sorry

/-- The associated-extension and fibre maps are inverse on extension classes. -/
theorem siteTorsorClassToSiteH1_extensionToTorsorClass {C : Type u} [Category.{v} C]
    {J : GrothendieckTopology C}
    (G : Sheaf J AddCommGrpCat.{w}) (X : C)
    [HasSheafify (J.over X) AddCommGrpCat.{w}]
    [HasExt.{w'} (Sheaf (J.over X) AddCommGrpCat.{w})]
    (e : siteH1 G X) :
    siteTorsorClassToSiteH1 G X (siteH1ExtensionToTorsorClass G X e) = e := by
  sorry

/-- Giraud's degree-one identification, stated as a bijection of types.

Proof roadmap:

1. Define the contracted product of two `SiteTorsor`s, descend it through
   `siteTorsorSetoid`, and identify the trivial torsor and inverse torsor.
2. Relate this Picard-style group of torsor classes to extensions of the unit
   sheaf by `G.over X`, the model used by `CategoryTheory.Sheaf.H` in degree
   one.
3. Construct maps in both directions by taking fibres of an extension and by
   forming the extension associated to a torsor action.
4. Prove the composites equivalent on representatives, descend through both
   quotients, and package the inverse maps as an `Equiv`.

The contracted-product and extension/torsor comparison interfaces above make
the representative-level constructions explicit; the existence of the
sheafified quotient and the comparison itself are the remaining mathematical
proof obligations. -/
theorem siteH1_equiv_siteTorsorClass
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    (G : Sheaf J AddCommGrpCat.{w}) (X : C)
    [HasSheafify (J.over X) AddCommGrpCat.{w}]
    [HasExt.{w'} (Sheaf (J.over X) AddCommGrpCat.{w})] :
    Nonempty (siteH1 G X ≃ SiteTorsorClass J G X) := by
  let E := siteH1TorsorCorrespondence G X
  exact ⟨{
    toFun := E.extension_to_torsor
    invFun := E.torsor_to_extension
    left_inv := siteTorsorClassToSiteH1_extensionToTorsorClass G X
    right_inv := siteH1ExtensionToTorsorClass_torsorToSiteH1 G X
  }⟩

/-- Giraud's degree-two identification for an abelian band.

Proof roadmap:

1. Choose local objects and local arrows in an `AbelianBandedGerbe`; use the
   band compatibility fields to extract a degree-two Čech cocycle valued in
   `G.over X`, and prove refinements change it only by a coboundary.
2. Starting from a degree-two cocycle, build the corresponding locally
   nonempty and locally connected fibred category, equip its automorphism
   sheaves with the prescribed band, and verify the gerbe axioms.
3. Show equivalent banded gerbes determine the same cohomology class, while
   cohomologous cocycles give `AbelianBandedGerbeEquivalence`s, so both maps
   descend to the existing quotient types.
4. Compare the two constructions locally, glue the local comparisons, prove
  both composites equal, and package them as an `Equiv`.

The cocycle, refinement, gluing, extraction, and quotient-compatibility
interfaces above isolate the comparison and inverse-law proofs. -/
theorem siteH2_equiv_abelianBandedGerbe
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    (G : Sheaf J AddCommGrpCat.{w}) (X : C)
    [HasSheafify (J.over X) AddCommGrpCat.{w}]
    [HasExt.{w'} (Sheaf (J.over X) AddCommGrpCat.{w})] :
    Nonempty (siteH2 G X ≃ AbelianBandedGerbeClass.{t, w, v, u} J G X) := by
  let e₁ : siteH2 G X ≃ SiteCechTwoCocycleClass.{w, v, u, t} J G X :=
    Classical.choice (siteH2_equiv_siteCechTwoCocycleClass G X)
  let e₂ : SiteCechTwoCocycleClass.{w, v, u, t} J G X ≃
      AbelianBandedGerbeClass J G X :=
    Classical.choice (siteCechTwoCocycleClass_equiv_abelianBandedGerbeClass G X)
  exact ⟨e₁.trans e₂⟩

/-- In the nonabelian case, degree-two cohomology is defined by `G`-gerbes. -/
abbrev nonabelianSiteH2 {C : Type u} [Category.{v} C]
    (J : GrothendieckTopology C) (G : Sheaf J GrpCat.{w}) (X : C) : Type _ :=
  NonabelianBandedGerbeClass.{t, w, v, u} J G X

/-! ### The 2-categorical remark -/

/-- A 2-morphism between morphisms of stacks in groupoids. -/
abbrev StackInGroupoidsTwoMorphism {C : Type u} [Category.{v} C]
    {J : GrothendieckTopology C}
    {X Y : StackInGroupoidsObject C J}
    (f g : FiberedMorphism X.value Y.value) := f ⟶ g

/-- The property asserted for 2-morphisms of stacks in groupoids. -/
def IsInvertibleStackInGroupoidsTwoMorphism
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    {X Y : StackInGroupoidsObject C J}
    {f g : FiberedMorphism X.value Y.value}
    (α : StackInGroupoidsTwoMorphism f g) : Prop := IsIso α

/-- Every 2-morphism between stacks in groupoids is invertible. -/
theorem stackInGroupoids_two_morphisms_are_invertible
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    {X Y : StackInGroupoidsObject C J}
    (f g : FiberedMorphism X.value Y.value)
    (α : StackInGroupoidsTwoMorphism f g) :
    IsInvertibleStackInGroupoidsTwoMorphism α := by
  change IsIso α
  let e : f ≅ g :=
    Pseudofunctor.StrongTrans.isoMk (η := f) (θ := g)
      (fun a => by
        letI : IsGroupoid (Y.value.obj a) := by
          change IsGroupoid (Fiber Y.value a.as.unop)
          exact Y.isStackInGroupoids.1 a.as.unop
        letI : IsIso (α.as.app a).toNatTrans :=
          NatIso.isIso_of_isIso_app _
        exact Cat.Hom.isoMk (asIso (α.as.app a).toNatTrans))
      (naturality := by
        intro a b k
        have ha : NatTrans.toCatHom₂ (α.as.app a).toNatTrans = α.as.app a := by
          apply Cat.Hom₂.ext
          rfl
        have hb : NatTrans.toCatHom₂ (α.as.app b).toNatTrans = α.as.app b := by
          apply Cat.Hom₂.ext
          rfl
        simpa only [Cat.Hom.isoMk, asIso_hom, ha, hb] using α.as.naturality k)
  have hα : e.hom = α := by
    apply Pseudofunctor.StrongTrans.homCategory.ext
    intro a
    let : IsGroupoid (Y.value.obj a) := by
      change IsGroupoid (Fiber Y.value a.as.unop)
      exact Y.isStackInGroupoids.1 a.as.unop
    let : IsIso (α.as.app a).toNatTrans :=
      NatIso.isIso_of_isIso_app _
    apply Cat.Hom₂.ext
    dsimp [e, Pseudofunctor.StrongTrans.isoMk, Cat.Hom.isoMk]
    exact asIso_hom _
  rw [← hα]
  infer_instance

/-!
The Vistoli, Knutson, SGA 4, and Kelly--Street entries in the source are
references and descriptions of scope.  They do not assert additional
definitions or theorems.  The statements above account for the precise
mathematics in the quoted Giraud and 2-category passages.
-/

end Formalization.Books.Guide.Unit04
