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

Unlike the abelian case, the automorphism sheaves are only required to be
locally identified with the given group sheaf; conjugation compatibility is
part of the band data.
-/
structure NonabelianBandedGerbe {C : Type u} [Category.{v} C]
    (J : GrothendieckTopology C)
    (G : Sheaf J GrpCat.{w}) (X : C) where
  value : FiberedCategory.{w, v, max u v} (Over C X)
  isGerbe : IsGerbe.{t, w, v, max u v} value (J.over X)
  band : ∀ (U : Over C X)
    (x : Fiber value U), (G.over X).obj.obj (op U) ≃* Aut x
  pullback_compatible : ∀ {U V : Over C X}
    (f : V ⟶ U) (x : Fiber value U) (g : (G.over X).obj.obj (op U)),
    band V ((value.map f.op.toLoc).toFunctor.obj x)
        ((G.over X).obj.map f.op g) =
      (value.map f.op.toLoc).toFunctor.mapIso (band U x g)
  conjugation_compatible : ∀ (U : Over C X)
    (x y : Fiber value U) (φ : x ⟶ y) (g : (G.over X).obj.obj (op U)),
    band U y g = conjugateAutomorphism isGerbe.1.1 φ (band U x g)

/-! ### Equivalence classes of nonabelian gerbes -/

/-- A band-preserving equivalence datum for nonabelian-banded gerbes. -/
structure NonabelianBandedGerbeEquivalence {C : Type u} [Category.{v} C]
    {J : GrothendieckTopology C} {G : Sheaf J GrpCat.{w}} {X : C}
    (P Q : NonabelianBandedGerbe.{t, w, v, u} J G X) where
  forward : FiberedMorphism P.value Q.value
  forward_is_equivalence : FiberwiseEquivalence forward
  forward_band_compatible : ∀ (U : Over C X) (x : Fiber P.value U)
    (g : (G.over X).obj.obj (op U)),
    Q.band U ((forward.app (.mk (op U))).toFunctor.obj x) g =
      (forward.app (.mk (op U))).toFunctor.mapIso (P.band U x g)
  backward : FiberedMorphism Q.value P.value
  backward_is_equivalence : FiberwiseEquivalence backward
  backward_band_compatible : ∀ (U : Over C X) (y : Fiber Q.value U)
    (g : (G.over X).obj.obj (op U)),
    P.band U ((backward.app (.mk (op U))).toFunctor.obj y) g =
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
          intro U x g
          change P.band U x g = (𝟭 _).mapIso (P.band U x g)
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
          intro U x g
          change P.band U x g = (𝟭 _).mapIso (P.band U x g)
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
          intro U x g
          change R.band U
              ((f.forward.app (.mk (op U))).toFunctor.obj
                ((e.forward.app (.mk (op U))).toFunctor.obj x)) g =
            ((e.forward.app (.mk (op U))).toFunctor ⋙
              (f.forward.app (.mk (op U))).toFunctor).mapIso (P.band U x g)
          rw [f.forward_band_compatible, e.forward_band_compatible]
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
          intro U y g
          change P.band U
              ((e.backward.app (.mk (op U))).toFunctor.obj
                ((f.backward.app (.mk (op U))).toFunctor.obj y)) g =
            ((f.backward.app (.mk (op U))).toFunctor ⋙
              (e.backward.app (.mk (op U))).toFunctor).mapIso (R.band U y g)
          rw [e.backward_band_compatible, f.backward_band_compatible]
          rfl
      }⟩

/-- Isomorphism classes of nonabelian-banded gerbes over `X`. -/
def NonabelianBandedGerbeClass {C : Type u} [Category.{v} C]
    (J : GrothendieckTopology C) (G : Sheaf J GrpCat.{w}) (X : C) :
    Type _ :=
  Quotient (nonabelianBandedGerbeSetoid.{t, w, v, u} J G X)

/-! ### Giraud's identifications -/

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
          sorry
        backward := 𝟙 _
        backward_is_equivalence := by
          constructor
          · intro U
            exact ⟨Functor.FullyFaithful.id _⟩
          · intro U
            change Functor.EssSurj (𝟭 _)
            exact inferInstance
        backward_band_compatible := by
          sorry
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
          sorry
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
          sorry
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
/- TODO(proof agents): construct the cocycle-to-gerbe and gerbe-to-cocycle maps
and prove them inverse on `AbelianBandedGerbeClass` representatives. -/
theorem siteH2_equiv_abelianBandedGerbe
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    (G : Sheaf J AddCommGrpCat.{w}) (X : C)
    [HasSheafify (J.over X) AddCommGrpCat.{w}]
    [HasExt.{w'} (Sheaf (J.over X) AddCommGrpCat.{w})] :
    Nonempty (siteH2 G X ≃ AbelianBandedGerbeClass J G X) := by
  sorry

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
