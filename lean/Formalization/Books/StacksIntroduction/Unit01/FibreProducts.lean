import Formalization.Books.StacksIntroduction.Unit01.ModuliStack
import Mathlib.CategoryTheory.Yoneda

/-!
# Introducing Algebraic Stacks, Chapter 1: fibre products

The point-valued functor in the source is written explicitly.  Its
restriction maps use the canonical pullback presentation from the preliminary
section; the coherence of the chosen presentations is recorded by theorem
interfaces.  This lets the source's representability and relative smoothness
definitions use actual presheaves and schemes.
-/

universe u

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

noncomputable section

namespace Formalization.Books.StacksIntroduction.Unit01

/-! ### Triples over a test scheme -/

/-- A `T`-point of the fibre product of two moduli points. -/
structure EllipticFiberProductPoint {S S' : Scheme.{u}}
    (E : ModuliPoint S) (E' : ModuliPoint S') (T : Scheme.{u}) where
  toS : T ⟶ S
  toS' : T ⟶ S'
  identification : EllipticCurveIso (E.baseChange toS) (E'.baseChange toS')

/-- Pull a triple back along a test-scheme map.

The identification is transported through the chosen base-change
presentations, including the associativity isomorphisms that compare an
iterated pullback with the pullback along a composite.  This is the canonical
map on the displayed representatives; it is not itself used as a strict
presheaf map, since the coherence isomorphisms need not be identities. -/
noncomputable def EllipticFiberProductPoint.restrict
    {S S' T T' : Scheme.{u}} {E : ModuliPoint S} {E' : ModuliPoint S'}
    (u : T' ⟶ T) (x : EllipticFiberProductPoint E E' T) :
    EllipticFiberProductPoint E E' T' :=
  { toS := u ≫ x.toS
    toS' := u ≫ x.toS'
    identification :=
      (EllipticCurveIso.baseChange_assoc E x.toS u).trans
        ((x.identification.baseChange u).trans
          (EllipticCurveIso.baseChange_assoc E' x.toS' u).symm) }

/-- The chosen restriction has the expected map to `S`. -/
theorem EllipticFiberProductPoint.restrict_toS
    {S S' T T' : Scheme.{u}} {E : ModuliPoint S} {E' : ModuliPoint S'}
    (u : T' ⟶ T) (x : EllipticFiberProductPoint E E' T) :
    (x.restrict u).toS = u ≫ x.toS :=
  rfl

/-- The chosen restriction has the expected map to `S'`. -/
theorem EllipticFiberProductPoint.restrict_toS'
    {S S' T T' : Scheme.{u}} {E : ModuliPoint S} {E' : ModuliPoint S'}
    (u : T' ⟶ T) (x : EllipticFiberProductPoint E E' T) :
    (x.restrict u).toS' = u ≫ x.toS' :=
  rfl

/-!
The source treats these triples as a presheaf of sets.  With the chosen
pullback presentations above, the canonical restriction is only coherent up
to the displayed elliptic-curve isomorphisms.  A strict presheaf therefore
needs the strictification data explicitly; it must not be inferred from
equality of `EllipticCurveIso` structures.
-/
structure EllipticFiberProductRestriction {S S' : Scheme.{u}}
    (E : ModuliPoint S) (E' : ModuliPoint S') where
  restrict : ∀ {T T' : Scheme.{u}} (u : T' ⟶ T),
    EllipticFiberProductPoint E E' T → EllipticFiberProductPoint E E' T'
  restrict_toS : ∀ {T T' : Scheme.{u}} (u : T' ⟶ T)
    (x : EllipticFiberProductPoint E E' T),
    (restrict u x).toS = u ≫ x.toS
  restrict_toS' : ∀ {T T' : Scheme.{u}} (u : T' ⟶ T)
    (x : EllipticFiberProductPoint E E' T),
    (restrict u x).toS' = u ≫ x.toS'
  restrict_id : ∀ {T : Scheme.{u}} (x : EllipticFiberProductPoint E E' T),
    restrict (𝟙 T) x = x
  restrict_comp : ∀ {T T' T'' : Scheme.{u}} (u : T' ⟶ T) (v : T'' ⟶ T')
    (x : EllipticFiberProductPoint E E' T),
    restrict (v ≫ u) x = restrict v (restrict u x)

/-- The strictification required before the triple-valued construction is a
presheaf of sets.  Its construction is a separate stack-coherence result;
the canonical pullback map above does not provide it definitionally. -/
theorem exists_ellipticFiberProductRestriction
    {S S' : Scheme.{u}} (E : ModuliPoint S) (E' : ModuliPoint S') :
    Nonempty (EllipticFiberProductRestriction E E') := by
  sorry

noncomputable def ellipticFiberProductRestriction
    {S S' : Scheme.{u}} (E : ModuliPoint S) (E' : ModuliPoint S') :
    EllipticFiberProductRestriction E E' :=
  Classical.choice (exists_ellipticFiberProductRestriction E E')

/-! ### The presheaf in the key fact -/

/-- The source's functor `Schᵒᵖ ⟶ Sets`, with its triples as values. -/
def ellipticFiberProductPresheaf {S S' : Scheme.{u}}
    (E : ModuliPoint S) (E' : ModuliPoint S') :
    Scheme.{u}ᵒᵖ ⥤ Type u :=
  let R := ellipticFiberProductRestriction E E'
  { obj := fun T => EllipticFiberProductPoint E E' T.unop
    map := fun {X Y} f =>
      TypeCat.ofHom (fun (x : EllipticFiberProductPoint E E' X.unop) =>
        R.restrict f.unop x)
    map_id := by
      intro T
      apply ConcreteCategory.hom_ext
      intro x
      exact R.restrict_id x
    map_comp := by
      intro X Y Z f g
      apply ConcreteCategory.hom_ext
      intro x
      exact R.restrict_comp f.unop g.unop x }

/-! ### Representability and the key fact -/

/-- A representation of the fibre-product presheaf, including its two projections. -/
structure FiberProductPresentation {S S' : Scheme.{u}}
    (E : ModuliPoint S) (E' : ModuliPoint S') where
  scheme : Scheme.{u}
  representing : (ellipticFiberProductPresheaf E E').RepresentableBy scheme

/-- The universal point supplied by a representation, evaluated at the identity. -/
noncomputable def FiberProductPresentation.universalPoint
    {S S' : Scheme.{u}} {E : ModuliPoint S} {E' : ModuliPoint S'}
    (P : FiberProductPresentation E E') :
    EllipticFiberProductPoint E E' P.scheme :=
  P.representing.homEquiv (𝟙 P.scheme)

/-- The key fact: the triple-valued presheaf is represented by a scheme. -/
theorem exists_fiberProductPresentation {S S' : Scheme.{u}}
    (E : ModuliPoint S) (E' : ModuliPoint S') :
    Nonempty (FiberProductPresentation E E') := by
  sorry

/-- A chosen representative of the fibre-product presheaf. -/
noncomputable def fiberProductPresentation {S S' : Scheme.{u}}
    (E : ModuliPoint S) (E' : ModuliPoint S') : FiberProductPresentation E E' :=
  Classical.choice (exists_fiberProductPresentation E E')

/-- The scheme denoted by `S ×ₘ S'` in the source. -/
noncomputable def moduliFiberProductScheme {S S' : Scheme.{u}}
    (E : ModuliPoint S) (E' : ModuliPoint S') : Scheme.{u} :=
  (fiberProductPresentation E E').scheme

/-- Its projection to the second scheme. -/
noncomputable def moduliFiberProductProjection {S S' : Scheme.{u}}
    (E : ModuliPoint S) (E' : ModuliPoint S') :
    moduliFiberProductScheme E E' ⟶ S' :=
  (fiberProductPresentation E E').universalPoint.toS'

/-- Its projection to the first scheme. -/
noncomputable def moduliFiberProductFirstProjection {S S' : Scheme.{u}}
    (E : ModuliPoint S) (E' : ModuliPoint S') :
    moduliFiberProductScheme E E' ⟶ S :=
  (fiberProductPresentation E E').universalPoint.toS

/-! ### Relative smoothness and surjectivity -/

/-- Smoothness of a map into the moduli object, tested after every moduli base change. -/
def IsSmoothModuliMorphism {S : Scheme.{u}} (E : ModuliPoint S) : Prop :=
  ∀ {S' : Scheme.{u}} (E' : ModuliPoint S'),
    Smooth (moduliFiberProductProjection E E')

/-- Surjectivity of a map into the moduli object, tested after every moduli base change. -/
def IsSurjectiveModuliMorphism {S : Scheme.{u}} (E : ModuliPoint S) : Prop :=
  ∀ {S' : Scheme.{u}} (E' : ModuliPoint S'),
    Surjective (moduliFiberProductProjection E E')

end Formalization.Books.StacksIntroduction.Unit01
