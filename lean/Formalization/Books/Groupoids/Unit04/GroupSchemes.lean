import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.AlgebraicGeometry.Morphisms.Smooth

/-!
# Groupoid Schemes, Chapter 4: Group schemes

This file formalizes the section `Group schemes` of `books/groupoids.tex`.  The
abstract group and group-homomorphism notions used in the source are the
existing `Group` and `MonoidHom` APIs.  A group scheme is expressed by its
scheme over the base, its structural morphisms, and the group laws on every
functor-of-points set.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u v

namespace Formalization.Books.Groupoids.Unit04

/-- A scheme over a fixed base scheme. -/
structure SchemeOver (S : Scheme.{u}) where
  carrier : Scheme.{u}
  map : carrier ⟶ S

namespace SchemeOver

/-- The base change of a scheme over `S` along `S' ⟶ S`. -/
def baseChange {S S' : Scheme.{u}} (X : SchemeOver S) (f : S' ⟶ S) : SchemeOver S' where
  carrier := pullback X.map f
  map := pullback.snd X.map f

end SchemeOver

/-- The `T`-valued points of a scheme over `S`, for `T` also over `S`. -/
abbrev SchemeOver.Points {S : Scheme.{u}} (X T : SchemeOver S) : Type u :=
  {f : T.carrier ⟶ X.carrier // f ≫ X.map = T.map}

/-- The group laws for fixed operations on a type.

This is deliberately a proposition rather than a second algebraic hierarchy:
the operations below are induced by morphisms of schemes. -/
structure GroupLaws (α : Type u) (mul : α → α → α) (one : α) (inv : α → α) : Prop where
  mul_assoc : ∀ a b c, mul (mul a b) c = mul a (mul b c)
  one_mul : ∀ a, mul one a = a
  mul_one : ∀ a, mul a one = a
  mul_inv : ∀ a, mul a (inv a) = one
  inv_mul : ∀ a, mul (inv a) a = one

/-- Multiplication on points induced by a multiplication morphism over `S`. -/
def SchemeOver.pointMul {S : Scheme.{u}} {X : SchemeOver S}
    (m : pullback X.map X.map ⟶ X.carrier)
  (hm : m ≫ X.map = pullback.fst X.map X.map ≫ X.map)
  {T : SchemeOver S} (a b : SchemeOver.Points X T) : SchemeOver.Points X T :=
  ⟨pullback.lift a.1 b.1 (a.2.trans b.2.symm) ≫ m, by
    rw [Category.assoc, hm, ← Category.assoc, pullback.lift_fst, a.2]⟩

/-- The identity point induced by a unit morphism over `S`. -/
def SchemeOver.pointOne {S : Scheme.{u}} {X : SchemeOver S}
    (e : S ⟶ X.carrier) (he : e ≫ X.map = 𝟙 S)
    (T : SchemeOver S) : SchemeOver.Points X T :=
  ⟨T.map ≫ e, by rw [Category.assoc, he, Category.comp_id]⟩

/-- Inversion on points induced by an inverse morphism over `S`. -/
def SchemeOver.pointInv {S : Scheme.{u}} {X : SchemeOver S}
    (i : X.carrier ⟶ X.carrier) (hi : i ≫ X.map = X.map)
    {T : SchemeOver S} (a : SchemeOver.Points X T) : SchemeOver.Points X T :=
  ⟨a.1 ≫ i, by rw [Category.assoc, hi, a.2]⟩

/-- Group-scheme structure on a fixed scheme over `S`. -/
structure GroupSchemeStructure {S : Scheme.{u}} (X : SchemeOver S) where
  multiplication : pullback X.map X.map ⟶ X.carrier
  unit : S ⟶ X.carrier
  inverse : X.carrier ⟶ X.carrier
  multiplication_over :
    multiplication ≫ X.map = pullback.fst X.map X.map ≫ X.map
  unit_over : unit ≫ X.map = 𝟙 S
  inverse_over : inverse ≫ X.map = X.map
  point_laws : ∀ T : SchemeOver S,
    GroupLaws (SchemeOver.Points X T)
      (SchemeOver.pointMul multiplication multiplication_over)
      (SchemeOver.pointOne unit unit_over T)
      (SchemeOver.pointInv inverse inverse_over)

/-- A group scheme over `S`. -/
structure GroupScheme (S : Scheme.{u}) where
  carrier : SchemeOver S
  group : GroupSchemeStructure carrier

namespace GroupScheme

abbrev multiplication {S : Scheme.{u}} (G : GroupScheme S) :
    pullback G.carrier.map G.carrier.map ⟶ G.carrier.carrier :=
  G.group.multiplication

abbrev identity {S : Scheme.{u}} (G : GroupScheme S) : S ⟶ G.carrier.carrier :=
  G.group.unit

abbrev inverse {S : Scheme.{u}} (G : GroupScheme S) : G.carrier.carrier ⟶ G.carrier.carrier :=
  G.group.inverse

/-- A point of `G` over a test scheme `T/S`. -/
abbrev Points {S : Scheme.{u}} (G : GroupScheme S) (T : SchemeOver S) :=
  SchemeOver.Points G.carrier T

/-- Multiplication of `T/S`-valued points of a group scheme. -/
abbrev pointMul {S : Scheme.{u}} (G : GroupScheme S) {T : SchemeOver S} :
    Points G T → Points G T → Points G T :=
  SchemeOver.pointMul G.group.multiplication G.group.multiplication_over

/-- The identity `T/S`-valued point of a group scheme. -/
abbrev pointOne {S : Scheme.{u}} (G : GroupScheme S) (T : SchemeOver S) : Points G T :=
  SchemeOver.pointOne G.group.unit G.group.unit_over T

/-- Inversion of `T/S`-valued points of a group scheme. -/
abbrev pointInv {S : Scheme.{u}} (G : GroupScheme S) {T : SchemeOver S} :
    Points G T → Points G T :=
  SchemeOver.pointInv G.group.inverse G.group.inverse_over

/-- The identity morphism supplied by the group-scheme structure. -/
abbrev e {S : Scheme.{u}} (G : GroupScheme S) : S ⟶ G.carrier.carrier := G.identity

/-- The inverse morphism supplied by the group-scheme structure. -/
abbrev i {S : Scheme.{u}} (G : GroupScheme S) :
    G.carrier.carrier ⟶ G.carrier.carrier := G.inverse

end GroupScheme

/-- Mapping a point along a morphism of schemes over `S`. -/
def SchemeOver.mapPoint {S : Scheme.{u}} {X Y : SchemeOver S}
    (f : X.carrier ⟶ Y.carrier) (hf : f ≫ Y.map = X.map)
    {T : SchemeOver S} (a : SchemeOver.Points X T) : SchemeOver.Points Y T :=
  ⟨a.1 ≫ f, by rw [Category.assoc, hf, a.2]⟩

/-- A morphism of group schemes over a common base. -/
structure GroupSchemeHom {S : Scheme.{u}} (G H : GroupScheme S)
    (f : G.carrier.carrier ⟶ H.carrier.carrier) : Prop where
  over : f ≫ H.carrier.map = G.carrier.map
  map_mul : ∀ (T : SchemeOver S) (a b : GroupScheme.Points G T),
    SchemeOver.mapPoint f over (GroupScheme.pointMul G a b) =
      GroupScheme.pointMul H
        (SchemeOver.mapPoint f over a) (SchemeOver.mapPoint f over b)

namespace GroupSchemeHom

theorem map_one {S : Scheme.{u}} {G H : GroupScheme S}
    {f : G.carrier.carrier ⟶ H.carrier.carrier} (hf : GroupSchemeHom G H f)
    (T : SchemeOver S) :
    SchemeOver.mapPoint f hf.over (GroupScheme.pointOne G T) = GroupScheme.pointOne H T := by
  sorry

theorem map_inv {S : Scheme.{u}} {G H : GroupScheme S}
    {f : G.carrier.carrier ⟶ H.carrier.carrier} (hf : GroupSchemeHom G H f)
    {T : SchemeOver S} (a : GroupScheme.Points G T) :
    SchemeOver.mapPoint f hf.over (GroupScheme.pointInv G a) =
      GroupScheme.pointInv H (SchemeOver.mapPoint f hf.over a) := by
  sorry

end GroupSchemeHom

/-- The map on fiber products induced by a morphism over `S`. -/
def SchemeOver.productMap {S : Scheme.{u}} {X Y : SchemeOver S}
    (f : X.carrier ⟶ Y.carrier) (hf : f ≫ Y.map = X.map) :
    pullback X.map X.map ⟶ pullback Y.map Y.map :=
  pullback.lift (pullback.fst X.map X.map ≫ f) (pullback.snd X.map X.map ≫ f) (by
    simp only [Category.assoc, hf, pullback.condition])

namespace GroupSchemeHom

/-- A group-scheme homomorphism commutes with multiplication. -/
theorem map_multiplication {S : Scheme.{u}} {G H : GroupScheme S}
    {f : G.carrier.carrier ⟶ H.carrier.carrier} (hf : GroupSchemeHom G H f) :
    SchemeOver.productMap f hf.over ≫ H.multiplication = G.multiplication ≫ f := by
  sorry

/-- For a morphism over `S`, preserving multiplication is equivalent to the
commutative multiplication square in the source. -/
theorem iff_map_multiplication {S : Scheme.{u}} {G H : GroupScheme S}
    (f : G.carrier.carrier ⟶ H.carrier.carrier)
    (hf : f ≫ H.carrier.map = G.carrier.map) :
    GroupSchemeHom G H f ↔
      SchemeOver.productMap f hf ≫ H.multiplication = G.multiplication ≫ f := by
  sorry

end GroupSchemeHom

/-- Base change of a group scheme has the expected underlying scheme over the
new base.  The existence statement is the source's base-change lemma. -/
theorem baseChange_groupScheme {S S' : Scheme.{u}} (G : GroupScheme S) (f : S' ⟶ S) :
    Nonempty (GroupSchemeStructure (G.carrier.baseChange f)) := by
  sorry

/-- A chosen base change of a group scheme. -/
noncomputable def baseChange {S S' : Scheme.{u}} (G : GroupScheme S) (f : S' ⟶ S) :
    GroupScheme S' :=
  ⟨G.carrier.baseChange f, Classical.choice (baseChange_groupScheme G f)⟩

/-- A morphism factors through a given subscheme map. -/
def FactorsThrough {X Y Z : Scheme.{u}} (f : X ⟶ Y) (j : Z ⟶ Y) : Prop :=
  ∃ g : X ⟶ Z, g ≫ j = f

/-- The multiplication restricted to a scheme mapping to the carrier of `G`. -/
def restrictedMultiplication {S : Scheme.{u}} (G : GroupScheme S)
    (X : SchemeOver S) (j : X.carrier ⟶ G.carrier.carrier)
    (hj : j ≫ G.carrier.map = X.map) :
    pullback X.map X.map ⟶ G.carrier.carrier :=
  SchemeOver.productMap j hj ≫ G.multiplication

/-- The inverse restricted to a scheme mapping to the carrier of `G`. -/
def restrictedInverse {S : Scheme.{u}} (G : GroupScheme S)
    (X : SchemeOver S) (j : X.carrier ⟶ G.carrier.carrier) :
    X.carrier ⟶ G.carrier.carrier :=
  j ≫ G.inverse

/-- Closed subgroup schemes, using the source's alternative description by a
group scheme with a closed-immersion homomorphism into `G`. -/
def IsClosedSubgroupScheme {S : Scheme.{u}} (G : GroupScheme S)
    (X : SchemeOver S) (j : X.carrier ⟶ G.carrier.carrier) : Prop :=
  IsClosedImmersion j ∧ ∃ D : GroupSchemeStructure X,
    GroupSchemeHom ⟨X, D⟩ G j

/-- Open subgroup schemes, using the source's alternative description. -/
def IsOpenSubgroupScheme {S : Scheme.{u}} (G : GroupScheme S)
    (X : SchemeOver S) (j : X.carrier ⟶ G.carrier.carrier) : Prop :=
  IsOpenImmersion j ∧ ∃ D : GroupSchemeStructure X,
    GroupSchemeHom ⟨X, D⟩ G j

/-- A closed subgroup is equivalently a closed subscheme through which the
unit, restricted multiplication, and inverse factor. -/
theorem isClosedSubgroupScheme_iff {S : Scheme.{u}} (G : GroupScheme S)
    (X : SchemeOver S) (j : X.carrier ⟶ G.carrier.carrier)
    (hj : j ≫ G.carrier.map = X.map) :
    IsClosedSubgroupScheme G X j ↔
      IsClosedImmersion j ∧
        FactorsThrough G.identity j ∧
        FactorsThrough (restrictedMultiplication G X j hj) j ∧
        FactorsThrough (restrictedInverse G X j) j := by
  sorry

/-- The analogous characterization for open subgroup schemes. -/
theorem isOpenSubgroupScheme_iff {S : Scheme.{u}} (G : GroupScheme S)
    (X : SchemeOver S) (j : X.carrier ⟶ G.carrier.carrier)
    (hj : j ≫ G.carrier.map = X.map) :
    IsOpenSubgroupScheme G X j ↔
      IsOpenImmersion j ∧
        FactorsThrough G.identity j ∧
        FactorsThrough (restrictedMultiplication G X j hj) j ∧
        FactorsThrough (restrictedInverse G X j) j := by
  sorry

namespace GroupScheme

/-- Smooth, flat, and separated group schemes are defined by their structural
morphism, reusing Mathlib's canonical morphism properties. -/
abbrev IsSmooth {S : Scheme.{u}} (G : GroupScheme S) : Prop :=
  Smooth G.carrier.map

abbrev IsFlat {S : Scheme.{u}} (G : GroupScheme S) : Prop :=
  Flat G.carrier.map

abbrev IsSeparated {S : Scheme.{u}} (G : GroupScheme S) : Prop :=
  AlgebraicGeometry.IsSeparated G.carrier.map

end GroupScheme

end Formalization.Books.Groupoids.Unit04
