import Formalization.Books.Stacks.Unit01.Groupoids
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

/-! ### The gerbe interfaces needed below -/

/-
The stable earlier chapter exposes the groupoid and descent interfaces.  The
broader older gerbe file depends on an unresolved presheaf proof, so the two
elementary gerbe predicates needed by this source section are kept explicit
here.
-/

def GuideLocallyNonempty {C : Type u} [Category.{v} C]
    (F : FiberedCategory.{w, v, u} C) (J : GrothendieckTopology C) : Prop :=
  ∀ U : C, ∃ (ι : Type t) (X : ι → C) (f : ∀ i, X i ⟶ U),
    CoveringFamily J f ∧ ∀ i, Nonempty (Fiber F (X i))

def GuideLocallyIsomorphic {C : Type u} [Category.{v} C]
    (F : FiberedCategory.{w, v, u} C) (J : GrothendieckTopology C) : Prop :=
  ∀ (U : C) (x y : Fiber F U),
    ∃ (ι : Type t) (X : ι → C) (f : ∀ i, X i ⟶ U),
      CoveringFamily J f ∧
        ∀ i, Nonempty
          ((F.map (f i).op.toLoc).toFunctor.obj x ≅
            (F.map (f i).op.toLoc).toFunctor.obj y)

def GuideIsGerbe {C : Type u} [Category.{v} C]
    (F : FiberedCategory.{w, v, u} C) (J : GrothendieckTopology C) : Prop :=
  StackInGroupoids F J ∧
    GuideLocallyNonempty.{t, w, v, u} F J ∧
      GuideLocallyIsomorphic.{t, w, v, u} F J

def guideAutomorphismSheafPresheaf {C : Type u} [Category.{v} C]
    (J : GrothendieckTopology C) (A : Sheaf J AddCommGrpCat.{w}) (U : C) :
    (Over C U)ᵒᵖ ⥤ Type w :=
  (A.over U).obj ⋙ (forget AddCommGrpCat)

noncomputable def guideConjugateAutomorphism {C : Type u} [Category.{v} C]
    {F : FiberedCategory.{w, v, u} C} (hF : FiberwiseGroupoid F) {U : C}
    {x y : Fiber F U} (φ : x ⟶ y) (a : Aut x) : Aut y := by
  letI := hF U
  exact (asIso φ).symm.trans (a.trans (asIso φ))

theorem guide_conjugation_presheaf_map_exists {C : Type u} [Category.{v} C]
    {F : FiberedCategory.{w, v, u} C} (hF : FiberwiseGroupoid F) {U : C}
    {x y : Fiber F U} (φ : x ⟶ y) :
    Nonempty (IsomPresheaf F x x ⟶ IsomPresheaf F y y) := by
  refine ⟨{ app := fun T => ?_, naturality := ?_ }⟩
  · exact ↾(fun a =>
      letI := hF T.unop.left
      ⟨(guideConjugateAutomorphism hF
        ((F.map T.unop.hom.op.toLoc).toFunctor.map φ) (asIso a.1)).hom,
        by infer_instance⟩)
  · intro T₁ T₂ q
    ext a
    apply Subtype.ext
    let : IsGroupoid (Fiber F T₁.unop.left) := hF _
    let : IsGroupoid (Fiber F T₂.unop.left) := hF _
    let : IsIso a.1 := a.2
    let aq : (IsomPresheaf F x x).obj T₂ := (IsomPresheaf F x x).map q a
    let : IsIso aq.1 := aq.2
    change
      (guideConjugateAutomorphism hF
        ((F.map T₂.unop.hom.op.toLoc).toFunctor.map φ) (asIso aq.1)).hom =
        (Pseudofunctor.LocallyDiscreteOpToCat.pullHom
          (guideConjugateAutomorphism hF
            ((F.map T₁.unop.hom.op.toLoc).toFunctor.map φ) (asIso a.1)).hom
          q.unop.left T₂.unop.hom T₂.unop.hom)
    have hq : T₁.unop.hom.op.toLoc ≫ q.unop.left.op.toLoc =
        T₂.unop.hom.op.toLoc := by
      rw [← Quiver.Hom.comp_toLoc, ← op_comp, q.unop.w]
    have hφ :
        (F.map T₂.unop.hom.op.toLoc).toFunctor.map φ =
          Pseudofunctor.LocallyDiscreteOpToCat.pullHom
            ((F.map T₁.unop.hom.op.toLoc).toFunctor.map φ)
            q.unop.left T₂.unop.hom T₂.unop.hom := by
      simp [Pseudofunctor.LocallyDiscreteOpToCat.pullHom]
    rw [hφ]
    change
      inv (Pseudofunctor.LocallyDiscreteOpToCat.pullHom
        ((F.map T₁.unop.hom.op.toLoc).toFunctor.map φ)
        q.unop.left T₂.unop.hom T₂.unop.hom) ≫
        Pseudofunctor.LocallyDiscreteOpToCat.pullHom a.1
          q.unop.left T₂.unop.hom T₂.unop.hom ≫
        Pseudofunctor.LocallyDiscreteOpToCat.pullHom
          ((F.map T₁.unop.hom.op.toLoc).toFunctor.map φ)
          q.unop.left T₂.unop.hom T₂.unop.hom =
        Pseudofunctor.LocallyDiscreteOpToCat.pullHom
          (inv ((F.map T₁.unop.hom.op.toLoc).toFunctor.map φ) ≫
            a.1 ≫ (F.map T₁.unop.hom.op.toLoc).toFunctor.map φ)
          q.unop.left T₂.unop.hom T₂.unop.hom
    simp [Pseudofunctor.LocallyDiscreteOpToCat.pullHom, Functor.map_comp,
      Category.assoc]

noncomputable def guideConjugationPresheafMap {C : Type u} [Category.{v} C]
    {F : FiberedCategory.{w, v, u} C} (hF : FiberwiseGroupoid F) {U : C}
    {x y : Fiber F U} (φ : x ⟶ y) :
    IsomPresheaf F x x ⟶ IsomPresheaf F y y :=
  Classical.choice (guide_conjugation_presheaf_map_exists hF φ)

structure GuideGerbeAutomorphismSheafData {C : Type u} [Category.{v} C]
    (F : FiberedCategory.{w, v, u} C) (J : GrothendieckTopology C)
    (hF : FiberwiseGroupoid F) where
  sheaf : Sheaf J AddCommGrpCat.{w}
  localIdentifications : ∀ (U : C) (x : Fiber F U),
    guideAutomorphismSheafPresheaf J sheaf U ≅ IsomPresheaf F x x
  conjugationCompatible : ∀ (U : C) (x y : Fiber F U) (φ : x ⟶ y),
    (localIdentifications U x).hom ≫ guideConjugationPresheafMap hF φ =
      (localIdentifications U y).hom

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

/-! ### Banded gerbes -/

/-- An abelian-banded gerbe over `X`, using the compatible automorphism-sheaf data above. -/
structure AbelianBandedGerbe {C : Type u} [Category.{v} C]
    (J : GrothendieckTopology C)
    (G : Sheaf J AddCommGrpCat.{w}) (X : C) where
  value : FiberedCategory.{w, v, max u v} (Over C X)
  isGerbe : GuideIsGerbe.{t, w, v, max u v} value (J.over X)
  automorphisms :
    GuideGerbeAutomorphismSheafData value (J.over X) isGerbe.1.1
  band : automorphisms.sheaf ≅ G.over X

/-- The type of data used for a nonabelian `G`-gerbe over `X`.

Unlike the abelian case, the automorphism sheaves are only required to be
locally identified with the given group sheaf; conjugation compatibility is
part of the band data.
-/
structure NonabelianBandedGerbe {C : Type u} [Category.{v} C]
    (J : GrothendieckTopology C)
    (G : Sheaf J GrpCat.{w}) (X : C) where
  value : FiberedCategory.{w, v, max u v} (Over C X)
  isGerbe : GuideIsGerbe.{t, w, v, max u v} value (J.over X)
  band : ∀ (U : Over C X)
    (x : Fiber value U), (G.over X).obj.obj (op U) ≃* Aut x
  pullback_compatible : ∀ {U V : Over C X}
    (f : V ⟶ U) (x : Fiber value U) (g : (G.over X).obj.obj (op U)),
    band V ((value.map f.op.toLoc).toFunctor.obj x)
        ((G.over X).obj.map f.op g) =
      (value.map f.op.toLoc).toFunctor.mapIso (band U x g)
  conjugation_compatible : ∀ (U : Over C X)
    (x y : Fiber value U) (φ : x ⟶ y) (g : (G.over X).obj.obj (op U)),
    band U y g = guideConjugateAutomorphism isGerbe.1.1 φ (band U x g)

/-! ### Giraud's identifications -/

/-- Giraud's degree-one identification, stated as a bijection of types. -/
/- TODO(proof agents): first define contracted product/Baer sum for
`SiteTorsor`, show it respects `siteTorsorSetoid`, and construct the two
classification maps `siteH1 G X -> SiteTorsorClass J G X` and back.  Prove the
maps inverse on representatives before packaging the resulting `Equiv`. -/
theorem siteH1_equiv_siteTorsorClass
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    (G : Sheaf J AddCommGrpCat.{w}) (X : C)
    [HasSheafify (J.over X) AddCommGrpCat.{w}]
    [HasExt.{w'} (Sheaf (J.over X) AddCommGrpCat.{w})] :
    Nonempty (siteH1 G X ≃ SiteTorsorClass J G X) := by
  sorry

/-- Giraud's degree-two identification for an abelian band. -/
/- TODO(proof agents): `siteH2` classifies equivalence classes of banded
gerbes, not raw `AbelianBandedGerbe` structures.  Before proving this theorem,
define band-preserving gerbe equivalence, prove it is a setoid, and introduce
an `AbelianBandedGerbeClass` quotient; the target here should then be changed
to that quotient.  Construct the cocycle-to-gerbe and gerbe-to-cocycle maps and
prove them inverse only after this target correction. -/
theorem siteH2_equiv_abelianBandedGerbe
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    (G : Sheaf J AddCommGrpCat.{w}) (X : C)
    [HasSheafify (J.over X) AddCommGrpCat.{w}]
    [HasExt.{w'} (Sheaf (J.over X) AddCommGrpCat.{w})] :
    Nonempty (siteH2 G X ≃ AbelianBandedGerbe J G X) := by
  sorry

/-- In the nonabelian case, degree-two cohomology is defined by `G`-gerbes. -/
abbrev nonabelianSiteH2 {C : Type u} [Category.{v} C]
    (J : GrothendieckTopology C) (G : Sheaf J GrpCat.{w}) (X : C) : Type _ :=
  NonabelianBandedGerbe.{t, w, v, u} J G X

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
