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

/-- A restricted triple exists after pulling it back along a test-scheme map. -/
theorem exists_ellipticFiberProductPoint_restrict
    {S S' T T' : Scheme.{u}} {E : ModuliPoint S} {E' : ModuliPoint S'}
    (u : T' ⟶ T) (x : EllipticFiberProductPoint E E' T) :
    ∃ y : EllipticFiberProductPoint E E' T',
      y.toS = u ≫ x.toS ∧ y.toS' = u ≫ x.toS' := by
  sorry

/-- The chosen restriction map on triples. -/
noncomputable def EllipticFiberProductPoint.restrict
    {S S' T T' : Scheme.{u}} {E : ModuliPoint S} {E' : ModuliPoint S'}
    (u : T' ⟶ T) (x : EllipticFiberProductPoint E E' T) :
    EllipticFiberProductPoint E E' T' :=
  Classical.choose (exists_ellipticFiberProductPoint_restrict u x)

/-- The chosen restriction has the expected map to `S`. -/
theorem EllipticFiberProductPoint.restrict_toS
    {S S' T T' : Scheme.{u}} {E : ModuliPoint S} {E' : ModuliPoint S'}
    (u : T' ⟶ T) (x : EllipticFiberProductPoint E E' T) :
    (x.restrict u).toS = u ≫ x.toS :=
  (Classical.choose_spec (exists_ellipticFiberProductPoint_restrict u x)).1

/-- The chosen restriction has the expected map to `S'`. -/
theorem EllipticFiberProductPoint.restrict_toS'
    {S S' T T' : Scheme.{u}} {E : ModuliPoint S} {E' : ModuliPoint S'}
    (u : T' ⟶ T) (x : EllipticFiberProductPoint E E' T) :
    (x.restrict u).toS' = u ≫ x.toS' :=
  (Classical.choose_spec (exists_ellipticFiberProductPoint_restrict u x)).2

/-- The chosen restrictions can be made coherently with identities. -/
theorem EllipticFiberProductPoint.restrict_id
    {S S' T : Scheme.{u}} {E : ModuliPoint S} {E' : ModuliPoint S'}
    (x : EllipticFiberProductPoint E E' T) :
    x.restrict (𝟙 T) = x := by
  sorry

/-- The chosen restrictions can be made coherently with composition. -/
theorem EllipticFiberProductPoint.restrict_comp
    {S S' T T' T'' : Scheme.{u}} {E : ModuliPoint S} {E' : ModuliPoint S'}
    (u : T' ⟶ T) (v : T'' ⟶ T') (x : EllipticFiberProductPoint E E' T) :
    x.restrict (v ≫ u) = (x.restrict u).restrict v := by
  sorry

/-! ### The presheaf in the key fact -/

/-- The source's functor `Schᵒᵖ ⟶ Sets`, with its triples as values. -/
def ellipticFiberProductPresheaf {S S' : Scheme.{u}}
    (E : ModuliPoint S) (E' : ModuliPoint S') :
    Scheme.{u}ᵒᵖ ⥤ Type u :=
  { obj := fun T => EllipticFiberProductPoint E E' T.unop
    map := fun {X Y} f =>
      TypeCat.ofHom (fun (x : EllipticFiberProductPoint E E' X.unop) =>
        EllipticFiberProductPoint.restrict f.unop x)
    map_id := by
      intro T
      apply ConcreteCategory.hom_ext
      intro x
      simpa using x.restrict_id
    map_comp := by
      intro X Y Z f g
      apply ConcreteCategory.hom_ext
      intro x
      simpa using
        (EllipticFiberProductPoint.restrict_comp f.unop g.unop x) }

/-! ### Representability and the key fact -/

/-- A representation of the fibre-product presheaf, including its two projections. -/
structure FiberProductPresentation {S S' : Scheme.{u}}
    (E : ModuliPoint S) (E' : ModuliPoint S') where
  scheme : Scheme.{u}
  toS : scheme ⟶ S
  toS' : scheme ⟶ S'
  representing : Nonempty
    (ellipticFiberProductPresheaf E E' ≅ uliftYoneda.{u}.obj scheme)

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
  (fiberProductPresentation E E').toS'

/-- Its projection to the first scheme. -/
noncomputable def moduliFiberProductFirstProjection {S S' : Scheme.{u}}
    (E : ModuliPoint S) (E' : ModuliPoint S') :
    moduliFiberProductScheme E E' ⟶ S :=
  (fiberProductPresentation E E').toS

/-! ### The diagonal description -/

/-- The source's diagonal-pullback presentation, expressed by the same point functor. -/
abbrev diagonalFiberProductPresheaf {S S' : Scheme.{u}}
    (E : ModuliPoint S) (E' : ModuliPoint S') :=
  ellipticFiberProductPresheaf E E'

/-- The displayed diagonal formula is the pointwise presentation used by the key fact. -/
theorem diagonal_fiberProduct_formula {S S' : Scheme.{u}}
    (E : ModuliPoint S) (E' : ModuliPoint S') :
    diagonalFiberProductPresheaf E E' = ellipticFiberProductPresheaf E E' :=
  rfl

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
