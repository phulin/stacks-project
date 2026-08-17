import Formalization.Books.StacksIntroduction.Unit01.Preliminary
import Mathlib.AlgebraicGeometry.Limits
import Mathlib.RingTheory.Polynomial.Basic

/-!
# Introducing Algebraic Stacks, Chapter 1: the moduli stack of elliptic curves

This section presents the moduli stack through its functor of points and its
witnesses for commutative triangles.  The declarations below keep the
witnesses explicit; this is the source's intended 2-categorical interface and
does not pretend that Mathlib already has a native category of stacks.
-/

universe u

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

noncomputable section

namespace Formalization.Books.StacksIntroduction.Unit01

/-! ### Triangles and their witnesses -/

/-- The enlarged collection of objects obtained by adjoining the moduli symbol. -/
inductive EnlargedModuliObject : Type (u + 1)
  | scheme (S : Scheme.{u})
  | ellipticModuli

/-- The adjoined object `M₁,₁`. -/
def ellipticModuliObject : EnlargedModuliObject :=
  .ellipticModuli

/-- A commutative triangle at the moduli object means that a witness exists. -/
def ModuliTriangleCommutes {S S' : Scheme.{u}} (a : S ⟶ S')
    (E : ModuliPoint S) (E' : ModuliPoint S') : Prop :=
  Nonempty (EllipticCurveMorphism a E E')

/-- The witness type for a commutative triangle. -/
abbrev ModuliTriangleWitness {S S' : Scheme.{u}} (a : S ⟶ S')
    (E : ModuliPoint S) (E' : ModuliPoint S') :=
  EllipticCurveMorphism a E E'

/-- The definition of commutativity is exactly existence of a witness. -/
theorem moduliTriangleCommutes_iff_exists_witness
    {S S' : Scheme.{u}} {a : S ⟶ S'}
    {E : ModuliPoint S} {E' : ModuliPoint S'} :
    ModuliTriangleCommutes a E E' ↔ Nonempty (ModuliTriangleWitness a E E') :=
  Iff.rfl

/-- Witnesses compose, so the outer triangle is commutative. -/
theorem moduliTriangleCommutes_comp
    {S S' S'' : Scheme.{u}} {a : S ⟶ S'} {a' : S' ⟶ S''}
    {E : ModuliPoint S} {E' : ModuliPoint S'} {E'' : ModuliPoint S''}
    (h : ModuliTriangleCommutes a E E')
    (h' : ModuliTriangleCommutes a' E' E'') :
    ModuliTriangleCommutes (a ≫ a') E E'' := by
  rcases h with ⟨α⟩
  rcases h' with ⟨β⟩
  exact ⟨EllipticCurveMorphism.comp α β⟩

/-! ### Composition with a scheme map -/

/-- The composition `S ⟶ S' ⟶ M₁,₁` is the base-changed family. -/
noncomputable def moduliComposition {S S' : Scheme.{u}} (a : S ⟶ S')
    (E' : ModuliPoint S') : ModuliPoint S :=
  E'.baseChange a

/-- Its underlying triple is the pullback triple displayed in the source. -/
theorem moduliComposition_toData {S S' : Scheme.{u}} (a : S ⟶ S')
    (E' : ModuliPoint S') :
    (moduliComposition a E').toData = E'.toData.baseChange a :=
  EllipticCurve.baseChange_toData E' a

/-! ### Rules out of the moduli object -/

/-- A rule `M₁,₁ ⟶ T` is a natural assignment on every family. -/
abbrev ModuliRule (T : Scheme.{u}) := ModuliMorphismToScheme T

/-- The affine line over `ℤ` used for the source's `j`-invariant example. -/
def affineLineOverIntegers : Scheme.{1} :=
  Scheme.Spec.obj (Opposite.op (CommRingCat.of (Polynomial (ULift ℤ))))

/-- A constant natural rule into the affine line.

This witnesses the general rule interface only; it is not the source's
`j`-invariant, whose construction needs a Weierstrass-model interface. -/
theorem exists_constantModuliRule :
    Nonempty (ModuliRule affineLineOverIntegers) := by
  let zeroEvaluation : Polynomial (ULift ℤ) →+* ULift ℤ :=
    Polynomial.eval₂RingHom (RingHom.id _) 0
  let zeroSection : Scheme.Spec.obj (Opposite.op (CommRingCat.of (ULift ℤ))) ⟶
      affineLineOverIntegers :=
    Scheme.Spec.map (CommRingCat.ofHom zeroEvaluation).op
  refine ⟨{ map := ?_, natural := ?_ }⟩
  · intro S E
    exact specULiftZIsTerminal.from S ≫ zeroSection
  · intro S S' a E E' α
    rw [← Category.assoc]
    congr 1
    apply specULiftZIsTerminal.hom_ext

/-- The chosen constant rule into `A¹_ℤ`. -/
noncomputable def constantModuliRule : ModuliRule affineLineOverIntegers :=
  Classical.choice exists_constantModuliRule

/-! ### Endomorphisms and the source's identity-only convention -/

/-- A moduli endomorphism assigns a new family and preserves witnesses. -/
structure ModuliSelfMorphism where
  map : ∀ {S : Scheme.{u}}, ModuliPoint S → ModuliPoint S
  preserves : ∀ {S S' : Scheme.{u}} {a : S ⟶ S'}
    {E : ModuliPoint S} {E' : ModuliPoint S'},
    EllipticCurveMorphism a E E' →
      Nonempty (EllipticCurveMorphism a (map E) (map E'))

/-- The identity endomorphism, with the same witness as input. -/
def identityModuliSelfMorphism : ModuliSelfMorphism :=
  { map := fun {_} E => E
    preserves := fun {_ _} {_} {_ _} α => ⟨α⟩ }

/-- The set of self-morphisms retained by the source's temporary convention. -/
def moduliSelfMorphismSet : Set ModuliSelfMorphism :=
  {identityModuliSelfMorphism}

/-! ### Witnessed 2-categorical language -/

/-- A triangle together with a chosen witness, rather than just its truth value. -/
structure WitnessedModuliTriangle {S S' : Scheme.{u}} (a : S ⟶ S')
    (E : ModuliPoint S) (E' : ModuliPoint S') where
  witness : ModuliTriangleWitness a E E'

/-- The chosen witnesses admit the composition operation used by the chapter. -/
noncomputable def WitnessedModuliTriangle.comp
    {S S' S'' : Scheme.{u}} {a : S ⟶ S'} {a' : S' ⟶ S''}
    {E : ModuliPoint S} {E' : ModuliPoint S'} {E'' : ModuliPoint S''}
    (left : WitnessedModuliTriangle a E E')
    (right : WitnessedModuliTriangle a' E' E'') :
    WitnessedModuliTriangle (a ≫ a') E E'' := by
  exact { witness := EllipticCurveMorphism.comp left.witness right.witness }

end Formalization.Books.StacksIntroduction.Unit01
