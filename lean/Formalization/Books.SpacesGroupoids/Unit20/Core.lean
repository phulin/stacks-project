import Mathlib.AlgebraicGeometry.Sites.Fpqc
import Mathlib.CategoryTheory.Bicategory.Functor.LocallyDiscrete
import Mathlib.CategoryTheory.Bicategory.Modification.Pseudo
import Mathlib.CategoryTheory.Sites.Over
import Formalization.«Books.Stacks».Unit01.Foundation

/-!
# Groupoids in Algebraic Spaces, Chapter 20: quotient stacks (core)

This file supplies the small geometric interface used by the quotient-stack
statements.  Mathlib has the fppf site of schemes and the Stacks chapter has
the categorical stackification interface, but it does not yet have an
algebraic-space implementation.  Algebraic spaces here are therefore
represented by fppf sheaves on the big site of schemes over a fixed scheme.
The groupoid interface is expressed on points, together with the pullback
functors and the arrow presentation supplied by the internal groupoid.
-/

noncomputable section

namespace Formalization.«Books.SpacesGroupoids».Unit20

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Pseudofunctor
open Opposite

open scoped CategoryTheory.Pseudofunctor.StrongTrans

universe u v

/-! The earlier Stacks foundation exposes the fibred-category and stack
interfaces, while the stronger stackification files in this project snapshot
currently depend on an unfinished auxiliary interface.  The following local
interface is the exact groupoid-stackification data needed here. -/

def StackInGroupoids {C : Type u} [Category.{v} C]
    (F : Formalization.«Books.Stacks».Unit01.FiberedCategory C)
    (J : GrothendieckTopology C) : Prop :=
  Formalization.«Books.Stacks».Unit01.FiberwiseGroupoid F ∧
    Formalization.«Books.Stacks».Unit01.Stack F J

structure QuotientStackificationData {C : Type u} [Category.{v} C]
    (F : Formalization.«Books.Stacks».Unit01.FiberedCategory C)
    (J : GrothendieckTopology C) where
  value : Formalization.«Books.Stacks».Unit01.FiberedCategory C
  map : Formalization.«Books.Stacks».Unit01.FiberedMorphism F value
  isStackInGroupoids : StackInGroupoids value J
  universal : ∀ (H : Formalization.«Books.Stacks».Unit01.FiberedCategory C),
    StackInGroupoids H J →
      (value ⟶ H) ≃ (F ⟶ H)
  universal_comp : ∀ (H : Formalization.«Books.Stacks».Unit01.FiberedCategory C)
      (hH : StackInGroupoids H J) (φ : value ⟶ H),
    universal H hH φ = map ≫ φ

theorem quotient_stackification_exists {C : Type u} [Category.{v} C]
    (F : Formalization.«Books.Stacks».Unit01.FiberedCategory C)
    (J : GrothendieckTopology C) :
    Nonempty (QuotientStackificationData F J) := by
  sorry

abbrev Scheme := AlgebraicGeometry.Scheme

/-- The category of schemes over a fixed base scheme. -/
abbrev SchemeOver (S : Scheme.{u}) := Over S

/-- The fppf topology on the big site of schemes over `S`. -/
abbrev FppfTopology (S : Scheme.{u}) : GrothendieckTopology (SchemeOver S) :=
  AlgebraicGeometry.Scheme.fppfTopology.over S

/-- An algebraic space over `S`, represented by its fppf sheaf of points. -/
abbrev AlgebraicSpace (S : Scheme.{u}) := Sheaf (FppfTopology S) (Type u)

/-- A morphism of algebraic spaces over `S`. -/
abbrev AlgebraicSpaceMorphism {S : Scheme.{u}}
    (X Y : AlgebraicSpace S) := X ⟶ Y

/-- An algebraic space over an algebraic space `B`. -/
structure AlgebraicSpaceOver {S : Scheme.{u}} (B : AlgebraicSpace S) where
  space : AlgebraicSpace S
  map : space ⟶ B

/-- A morphism of algebraic spaces over `B`. -/
structure AlgebraicSpaceOverHom {S : Scheme.{u}} {B : AlgebraicSpace S}
    (X Y : AlgebraicSpaceOver B) where
  map : X.space ⟶ Y.space
  comm : map ≫ Y.map = X.map := by cat_disch

namespace AlgebraicSpaceOverHom

/-- The identity morphism over `B`. -/
def id {S : Scheme.{u}} {B : AlgebraicSpace S} (X : AlgebraicSpaceOver B) :
    AlgebraicSpaceOverHom X X :=
  ⟨𝟙 X.space, by simp⟩

/-- Composition of morphisms over `B`. -/
def comp {S : Scheme.{u}} {B : AlgebraicSpace S}
    {X Y Z : AlgebraicSpaceOver B} (f : AlgebraicSpaceOverHom X Y)
    (g : AlgebraicSpaceOverHom Y Z) : AlgebraicSpaceOverHom X Z :=
  ⟨f.map ≫ g.map, by simp [f.comm, g.comm, Category.assoc]⟩

end AlgebraicSpaceOverHom

/-- The `T`-valued points of an algebraic space over `S`. -/
abbrev SpacePoint {S : Scheme.{u}} (X : AlgebraicSpace S)
    (T : SchemeOver S) := X.obj.obj (op T)

/-- The map on points induced by a morphism of algebraic spaces. -/
def pointMap {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) (T : SchemeOver S) : SpacePoint X T → SpacePoint Y T :=
  f.hom.app (op T)

/-- Restriction of a point along a morphism of schemes over `S`. -/
def restrictPoint {S : Scheme.{u}} (X : AlgebraicSpace S)
    {T₁ T₂ : SchemeOver S} (f : T₁ ⟶ T₂) : SpacePoint X T₂ → SpacePoint X T₁ :=
  X.obj.map f.op

/-- The underlying `T`-valued points of an object over `B`. -/
abbrev OverPoint {S : Scheme.{u}} {B : AlgebraicSpace S}
    (X : AlgebraicSpaceOver B) (T : SchemeOver S) := SpacePoint X.space T

/-- The map on points induced by a morphism over `B`. -/
def overPointMap {S : Scheme.{u}} {B : AlgebraicSpace S}
    {X Y : AlgebraicSpaceOver B} (f : AlgebraicSpaceOverHom X Y)
    (T : SchemeOver S) : OverPoint X T → OverPoint Y T :=
  pointMap f.map T

/-- The arrows of the internal groupoid with fixed source and target. -/
def GroupoidArrow {S : Scheme.{u}} {B : AlgebraicSpace S}
    {U R : AlgebraicSpaceOver B} (s t : AlgebraicSpaceOverHom R U)
    (T : SchemeOver S) (x y : OverPoint U T) :=
  {r : OverPoint R T // overPointMap s T r = x ∧ overPointMap t T r = y}

/-- A groupoid in algebraic spaces over `B`, presented on all fppf points.

The field `fiber` records the groupoid of `T`-valued points and `arrows`
identifies its arrows with the `R`-valued points having the prescribed source
and target.  The `pullback` field records the contravariant functoriality in
`T`; this is the pointwise form of the presheaf in groupoids in the source.
-/
structure AlgebraicSpaceGroupoid {S : Scheme.{u}} (B : AlgebraicSpace S) where
  U : AlgebraicSpaceOver B
  R : AlgebraicSpaceOver B
  s : AlgebraicSpaceOverHom R U
  t : AlgebraicSpaceOverHom R U
  fiber : ∀ T : SchemeOver S, Groupoid (OverPoint U T)
  arrows : ∀ (T : SchemeOver S) (x y : OverPoint U T),
    GroupoidArrow s t T x y ≃
      @Quiver.Hom (OverPoint U T) (fiber T).toCategory.toQuiver x y
  pullback : ∀ {T₁ T₂ : SchemeOver S} (_f : T₁ ⟶ T₂),
    @CategoryTheory.Functor (OverPoint U T₂) (fiber T₂).toCategory
      (OverPoint U T₁) (fiber T₁).toCategory
  pullback_obj : ∀ {T₁ T₂ : SchemeOver S} (f : T₁ ⟶ T₂)
      (x : OverPoint U T₂),
    (pullback f).obj x = restrictPoint U.space f x
  pullback_source : ∀ {T₁ T₂ : SchemeOver S} (f : T₁ ⟶ T₂)
      (r : OverPoint R T₂),
    overPointMap s T₁ (restrictPoint R.space f r) =
      restrictPoint U.space f (overPointMap s T₂ r)
  pullback_target : ∀ {T₁ T₂ : SchemeOver S} (f : T₁ ⟶ T₂)
      (r : OverPoint R T₂),
    overPointMap t T₁ (restrictPoint R.space f r) =
      restrictPoint U.space f (overPointMap t T₂ r)
  pullback_id : ∀ T : SchemeOver S, pullback (𝟙 T) = Functor.id _
  pullback_comp : ∀ {T₁ T₂ T₃ : SchemeOver S} (f : T₁ ⟶ T₂) (g : T₂ ⟶ T₃),
    pullback (f ≫ g) = pullback g ⋙ pullback f

namespace AlgebraicSpaceGroupoid

/-- A pair of composable arrows, written in the source's order: first the
target arrow and then the source arrow. -/
abbrev ComposablePair {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : AlgebraicSpaceGroupoid B) (T : SchemeOver S) :=
  {p : OverPoint G.R T × OverPoint G.R T //
    overPointMap G.s T p.1 = overPointMap G.t T p.2}

/-- The composition operation on `R`-valued points. -/
def composition {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : AlgebraicSpaceGroupoid B) (T : SchemeOver S)
    (p : ComposablePair G T) : OverPoint G.R T := by
  letI := G.fiber T
  let r₀ := p.1.1
  let r₁ := p.1.2
  let a₀ := (G.arrows T (overPointMap G.s T r₀) (overPointMap G.t T r₀))
    ⟨r₀, rfl, rfl⟩
  let a₁ := (G.arrows T (overPointMap G.s T r₁) (overPointMap G.t T r₁))
    ⟨r₁, rfl, rfl⟩
  exact ((G.arrows T (overPointMap G.s T r₁) (overPointMap G.t T r₀)).symm
    (a₁ ≫ eqToHom p.2.symm ≫ a₀)).1

/-- The identity arrow at a point. -/
def identity {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : AlgebraicSpaceGroupoid B) (T : SchemeOver S) (x : OverPoint G.U T) :
    OverPoint G.R T := by
  letI := G.fiber T
  exact ((G.arrows T x x).symm (𝟙 x)).1

/-- The inverse of an `R`-valued point. -/
def inverse {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : AlgebraicSpaceGroupoid B) (T : SchemeOver S) (r : OverPoint G.R T) :
    OverPoint G.R T := by
  letI := G.fiber T
  let a := (G.arrows T (overPointMap G.s T r) (overPointMap G.t T r))
    ⟨r, rfl, rfl⟩
  exact ((G.arrows T (overPointMap G.t T r) (overPointMap G.s T r)).symm (inv a)).1

/-- The source-facing names for composition, identities, and inverses. -/
abbrev c {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : AlgebraicSpaceGroupoid B) (T : SchemeOver S)
    (p : ComposablePair G T) : OverPoint G.R T :=
  composition G T p
abbrev one {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : AlgebraicSpaceGroupoid B) (T : SchemeOver S)
    (x : OverPoint G.U T) : OverPoint G.R T :=
  identity G T x
abbrev inv {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : AlgebraicSpaceGroupoid B) (T : SchemeOver S)
    (r : OverPoint G.R T) : OverPoint G.R T :=
  inverse G T r

theorem composition_source {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : AlgebraicSpaceGroupoid B) (T : SchemeOver S)
    (p : ComposablePair G T) :
    overPointMap G.s T (composition G T p) = overPointMap G.s T p.1.2 := by
  sorry

theorem composition_target {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : AlgebraicSpaceGroupoid B) (T : SchemeOver S)
    (p : ComposablePair G T) :
    overPointMap G.t T (composition G T p) = overPointMap G.t T p.1.1 := by
  sorry

theorem identity_source {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : AlgebraicSpaceGroupoid B) (T : SchemeOver S)
    (x : OverPoint G.U T) :
    overPointMap G.s T (identity G T x) = x := by
  sorry

theorem identity_target {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : AlgebraicSpaceGroupoid B) (T : SchemeOver S)
    (x : OverPoint G.U T) :
    overPointMap G.t T (identity G T x) = x := by
  sorry

theorem inverse_source {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : AlgebraicSpaceGroupoid B) (T : SchemeOver S)
    (r : OverPoint G.R T) :
    overPointMap G.s T (inverse G T r) = overPointMap G.t T r := by
  sorry

theorem inverse_target {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : AlgebraicSpaceGroupoid B) (T : SchemeOver S)
    (r : OverPoint G.R T) :
    overPointMap G.t T (inverse G T r) = overPointMap G.s T r := by
  sorry

theorem composition_identity {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : AlgebraicSpaceGroupoid B) (T : SchemeOver S)
    (r : OverPoint G.R T) :
    ∃ h₁ : overPointMap G.s T (identity G T (overPointMap G.t T r)) =
        overPointMap G.t T r,
      ∃ h₂ : overPointMap G.s T r =
        overPointMap G.t T (identity G T (overPointMap G.s T r)),
        composition G T ⟨⟨identity G T (overPointMap G.t T r), r⟩, h₁⟩ = r ∧
        composition G T ⟨⟨r, identity G T (overPointMap G.s T r)⟩, h₂⟩ = r := by
  sorry

theorem composition_inverse {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : AlgebraicSpaceGroupoid B) (T : SchemeOver S)
    (r : OverPoint G.R T) :
    ∃ h₁ : overPointMap G.s T r =
        overPointMap G.t T (inverse G T r),
      ∃ h₂ : overPointMap G.s T (inverse G T r) =
        overPointMap G.t T r,
        composition G T ⟨⟨r, inverse G T r⟩, h₁⟩ =
            identity G T (overPointMap G.t T r) ∧
        composition G T ⟨⟨inverse G T r, r⟩, h₂⟩ =
            identity G T (overPointMap G.s T r) := by
  sorry

theorem composition_associative {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : AlgebraicSpaceGroupoid B) (T : SchemeOver S)
    (r₁ r₂ r₃ : OverPoint G.R T)
    (h₁₂ : overPointMap G.s T r₁ = overPointMap G.t T r₂)
    (h₂₃ : overPointMap G.s T r₂ = overPointMap G.t T r₃) :
    ∃ h₁₂₃ :
        overPointMap G.s T (composition G T ⟨⟨r₁, r₂⟩, h₁₂⟩) =
          overPointMap G.t T r₃,
      ∃ h₁_₂₃ :
          overPointMap G.s T r₁ =
            overPointMap G.t T (composition G T ⟨⟨r₂, r₃⟩, h₂₃⟩),
        composition G T
              ⟨⟨composition G T ⟨⟨r₁, r₂⟩, h₁₂⟩, r₃⟩, h₁₂₃⟩ =
            composition G T
              ⟨⟨r₁, composition G T ⟨⟨r₂, r₃⟩, h₂₃⟩⟩, h₁_₂₃⟩ := by
  sorry

theorem composition_pullback {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : AlgebraicSpaceGroupoid B) {T₁ T₂ : SchemeOver S}
    (f : T₁ ⟶ T₂) (p : ComposablePair G T₂) :
    ∃ h : overPointMap G.s T₁ (restrictPoint G.R.space f p.1.1) =
        overPointMap G.t T₁ (restrictPoint G.R.space f p.1.2),
      restrictPoint G.R.space f (composition G T₂ p) =
        composition G T₁
          ⟨⟨restrictPoint G.R.space f p.1.1,
            restrictPoint G.R.space f p.1.2⟩, h⟩ := by
  sorry

end AlgebraicSpaceGroupoid

/-- The quotient-fibre category associated to a groupoid in algebraic spaces. -/
abbrev QuotientFiber {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : AlgebraicSpaceGroupoid B) (T : SchemeOver S) := OverPoint G.U T

/-- The presheaf in groupoids `S' ↦ (U(S'), R(S'), s, t, c)` from the source.

The earlier Stacks formalization presents a fibred category by a family of
fibre categories indexed by the base category.  Its `LocallyDiscrete` base
records those fibres and the groupoid's pullback functors are retained in
`AlgebraicSpaceGroupoid.pullback` above.
-/
noncomputable def quotientPresheaf {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : AlgebraicSpaceGroupoid B) :
    Formalization.«Books.Stacks».Unit01.FiberedCategory (SchemeOver S) :=
  LocallyDiscrete.mkPseudofunctor
    (fun T => letI : Category (QuotientFiber G T.unop) := (G.fiber T.unop).toCategory
      Cat.of (QuotientFiber G T.unop))
    (fun {T T'} f => by
      letI : Category (QuotientFiber G T.unop) := (G.fiber T.unop).toCategory
      letI : Category (QuotientFiber G T'.unop) := (G.fiber T'.unop).toCategory
      exact (G.pullback f.unop).toCatHom)
    (fun T => by
      letI : Category (QuotientFiber G T.unop) := (G.fiber T.unop).toCategory
      change (G.pullback (𝟙 T.unop)).toCatHom ≅ 𝟙 _
      exact eqToIso (congrArg Functor.toCatHom (G.pullback_id T.unop)))
    (fun {b₀ b₁ b₂ : (SchemeOver S)ᵒᵖ} f g => by
      letI : Category (QuotientFiber G b₀.unop) :=
        (G.fiber b₀.unop).toCategory
      letI : Category (QuotientFiber G b₁.unop) :=
        (G.fiber b₁.unop).toCategory
      letI : Category (QuotientFiber G b₂.unop) :=
        (G.fiber b₂.unop).toCategory
      change (G.pullback (g.unop ≫ f.unop)).toCatHom ≅
        (G.pullback f.unop).toCatHom ≫ (G.pullback g.unop).toCatHom
      exact eqToIso (congrArg Functor.toCatHom
        (G.pullback_comp g.unop f.unop)))
    (map₂_associator := by sorry)
    (map₂_left_unitor := by sorry)
    (map₂_right_unitor := by sorry)

/-- A chosen stackification of the presheaf in groupoids defining the quotient stack. -/
abbrev QuotientStackification {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : AlgebraicSpaceGroupoid B) :=
  QuotientStackificationData
    (quotientPresheaf G) (FppfTopology S)

/-- The quotient stack is the chosen value of a groupoid stackification. -/
noncomputable def quotientStackification {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : AlgebraicSpaceGroupoid B) : QuotientStackification G :=
  Classical.choice
    (quotient_stackification_exists
      (quotientPresheaf G) (FppfTopology S))

/-- The fibred category underlying the quotient stack `[U/R]`. -/
abbrev quotientStack {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : AlgebraicSpaceGroupoid B) :
    Formalization.«Books.Stacks».Unit01.FiberedCategory (SchemeOver S) :=
  (quotientStackification G).value

/-- The canonical map from the presheaf in groupoids to its quotient stack. -/
abbrev quotientStackificationMap {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : AlgebraicSpaceGroupoid B) :
    Formalization.«Books.Stacks».Unit01.FiberedMorphism
      (quotientPresheaf G) (quotientStack G) :=
  (quotientStackification G).map

end Formalization.«Books.SpacesGroupoids».Unit20
