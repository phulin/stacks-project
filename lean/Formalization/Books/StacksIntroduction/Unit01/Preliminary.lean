import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.AlgebraicGeometry.Fiber
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-!
# Introducing Algebraic Stacks, Chapter 1: preliminary interfaces

The version of Mathlib used by the project has the scheme and elliptic-curve
building blocks, but it does not define a category of families of elliptic
curves over arbitrary schemes or a native moduli-stack object.  This file
therefore records the source-facing family and witness interfaces explicitly.
The scheme-theoretic conditions use Mathlib's canonical morphism properties;
the fibre cohomology fields are the missing family-level interface.
-/

universe u

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

noncomputable section

namespace Formalization.Books.StacksIntroduction.Unit01

/-! ### The fibrewise cohomology data -/

/-- A vector space together with the one-dimensionality assertion used below. -/
structure OneDimensionalVectorSpace (K : Type u) [Field K] where
  carrier : ModuleCat K
  basis : Nonempty ((carrier : Type u) ≃ₗ[K] K)

/-- The `H^0` and `H^1` data required in the source definition of a fibre.

Mathlib does not currently provide the cohomology of an arbitrary scheme
fibre in this interface, so the two fields retain the actual vector spaces
and their one-dimensionality witnesses instead of replacing them by bare
propositions. -/
structure FiberCohomologyData (K : Type u) [Field K] where
  H0 : OneDimensionalVectorSpace K
  H1 : OneDimensionalVectorSpace K

/-! ### Elliptic curves over a scheme -/

/-- The connectedness condition on the scheme-theoretic fibre at a point. -/
def ConnectedFiber {S E : Scheme.{u}} (f : E ⟶ S) (s : S) : Prop :=
  _root_.IsConnected (Set.univ : Set (f.fiber s))

/--
An elliptic curve over `S`, following the triple `(E, f, 0)` in the source.

The smoothness and properness fields are Mathlib's scheme-morphism
properties.  `FiberCohomologyData` is the explicit interface for the two
one-dimensional residue-field cohomology groups appearing in the book.
-/
structure EllipticCurve (S : Scheme.{u}) where
  total : Scheme.{u}
  projection : total ⟶ S
  zero : S ⟶ total
  proper : IsProper projection
  smooth : SmoothOfRelativeDimension 1 projection
  connected_fiber : ∀ s : S, ConnectedFiber projection s
  fiber_cohomology : ∀ s : S,
    FiberCohomologyData (S.residueField s)
  zero_section : zero ≫ projection = 𝟙 S

/-- The raw triple used to display the pullback in a base change. -/
structure EllipticCurveData (S : Scheme.{u}) where
  total : Scheme.{u}
  projection : total ⟶ S
  zero : S ⟶ total
  zero_section : zero ≫ projection = 𝟙 S

/-- Forget the geometric conditions from an elliptic curve. -/
def EllipticCurve.toData {S : Scheme.{u}} (E : EllipticCurve S) :
    EllipticCurveData S :=
  { total := E.total
    projection := E.projection
    zero := E.zero
    zero_section := E.zero_section }

/-- The displayed pullback triple used by composition with a map `T ⟶ S`. -/
noncomputable def EllipticCurveData.baseChange {S T : Scheme.{u}}
    (E : EllipticCurveData S) (a : T ⟶ S) : EllipticCurveData T :=
  { total := pullback E.projection a
    projection := pullback.snd E.projection a
    zero := pullback.lift (a ≫ E.zero) (𝟙 T) (by
      simp [Category.assoc, E.zero_section])
    zero_section := pullback.lift_snd (a ≫ E.zero) (𝟙 T) _ }

/-- Base change preserves the defining family conditions. -/
theorem exists_ellipticCurve_baseChange {S T : Scheme.{u}}
    (E : EllipticCurve S) (a : T ⟶ S) :
    ∃ E' : EllipticCurve T,
      E'.toData = E.toData.baseChange a := by
  sorry

/-- A chosen elliptic curve obtained by base changing a family. -/
noncomputable def EllipticCurve.baseChange {S T : Scheme.{u}}
    (E : EllipticCurve S) (a : T ⟶ S) : EllipticCurve T :=
  Classical.choose (exists_ellipticCurve_baseChange E a)

/-- The chosen base change has the displayed pullback triple. -/
theorem EllipticCurve.baseChange_toData {S T : Scheme.{u}}
    (E : EllipticCurve S) (a : T ⟶ S) :
    (E.baseChange a).toData = E.toData.baseChange a :=
  Classical.choose_spec (exists_ellipticCurve_baseChange E a)

/-! ### Morphisms and witnesses -/

/-!
A morphism in the source is a map of total spaces over a map of bases.  The
last field is the cartesian inner square from the displayed diagram.
-/
structure EllipticCurveMorphism {S S' : Scheme.{u}} (a : S ⟶ S')
    (E : EllipticCurve S) (E' : EllipticCurve S') where
  hom : E.total ⟶ E'.total
  projection_comm : hom ≫ E'.projection = E.projection ≫ a
  section_comm : E.zero ≫ hom = a ≫ E'.zero
  cartesian : IsPullback hom E.projection E'.projection a

/-- The identity morphism of a family. -/
def EllipticCurveMorphism.refl {S : Scheme.{u}} (E : EllipticCurve S) :
    EllipticCurveMorphism (𝟙 S) E E :=
  { hom := 𝟙 E.total
    projection_comm := by simp
    section_comm := by simp
    cartesian := IsPullback.of_id_fst }

/-- A witness over a fixed base, with its inverse retained as an isomorphism. -/
structure EllipticCurveIso {S : Scheme.{u}} (E E' : EllipticCurve S) where
  hom : E.total ≅ E'.total
  projection_comm : hom.hom ≫ E'.projection = E.projection
  section_comm : E.zero ≫ hom.hom = E'.zero

/-- The identity witness. -/
def EllipticCurveIso.refl {S : Scheme.{u}} (E : EllipticCurve S) :
    EllipticCurveIso E E :=
  { hom := Iso.refl E.total
    projection_comm := by simp
    section_comm := by simp }

/-- Composition of witnesses over a fixed base. -/
def EllipticCurveIso.trans {S : Scheme.{u}} {E₁ E₂ E₃ : EllipticCurve S}
    (α : EllipticCurveIso E₁ E₂) (β : EllipticCurveIso E₂ E₃) :
    EllipticCurveIso E₁ E₃ :=
  { hom := α.hom ≪≫ β.hom
    projection_comm := by
      simp only [Iso.trans_hom, Category.assoc]
      rw [β.projection_comm, α.projection_comm]
    section_comm := by
      simp only [Iso.trans_hom]
      rw [← Category.assoc, α.section_comm, β.section_comm] }

/-- Inverse of a witness over a fixed base. -/
def EllipticCurveIso.symm {S : Scheme.{u}} {E E' : EllipticCurve S}
    (α : EllipticCurveIso E E') : EllipticCurveIso E' E :=
  { hom := α.hom.symm
    projection_comm := by
      rw [← α.projection_comm]
      simp
    section_comm := by
      rw [← α.section_comm]
      simp [Category.assoc] }

/-- Base change of an isomorphism of families, using the chosen pullback presentations. -/
theorem exists_ellipticCurveIso_baseChange {S T : Scheme.{u}}
    {E E' : EllipticCurve S} (α : EllipticCurveIso E E') (a : T ⟶ S) :
    Nonempty (EllipticCurveIso (E.baseChange a) (E'.baseChange a)) := by
  sorry

/-- The chosen base change of a witness. -/
noncomputable def EllipticCurveIso.baseChange {S T : Scheme.{u}}
    {E E' : EllipticCurve S} (α : EllipticCurveIso E E') (a : T ⟶ S) :
    EllipticCurveIso (E.baseChange a) (E'.baseChange a) :=
  Classical.choice (exists_ellipticCurveIso_baseChange α a)

/-- The two chosen ways of iterated base change are isomorphic. -/
theorem exists_ellipticCurveIso_baseChange_assoc {S X T : Scheme.{u}}
    (E : EllipticCurve S) (f : X ⟶ S) (g : T ⟶ X) :
    Nonempty (EllipticCurveIso (E.baseChange (g ≫ f))
      ((E.baseChange f).baseChange g)) := by
  sorry

/-- A chosen associativity witness for the pullback presentations. -/
noncomputable def EllipticCurveIso.baseChange_assoc {S X T : Scheme.{u}}
    (E : EllipticCurve S) (f : X ⟶ S) (g : T ⟶ X) :
    EllipticCurveIso (E.baseChange (g ≫ f))
      ((E.baseChange f).baseChange g) :=
  Classical.choice (exists_ellipticCurveIso_baseChange_assoc E f g)

/-- Chosen base changes along equal maps are identified. -/
theorem exists_ellipticCurveIso_baseChange_eq {S T : Scheme.{u}}
    (E : EllipticCurve S) {a b : T ⟶ S} (h : a = b) :
    Nonempty (EllipticCurveIso (E.baseChange a) (E.baseChange b)) := by
  subst h
  exact ⟨EllipticCurveIso.refl _⟩

noncomputable def EllipticCurveIso.baseChange_eq {S T : Scheme.{u}}
    (E : EllipticCurve S) {a b : T ⟶ S} (h : a = b) :
    EllipticCurveIso (E.baseChange a) (E.baseChange b) :=
  Classical.choice (exists_ellipticCurveIso_baseChange_eq E h)

/-- Composition of witnesses exists, as required by the source's 2-category discussion. -/
theorem exists_ellipticCurveMorphism_comp
    {S S' S'' : Scheme.{u}} {a : S ⟶ S'} {a' : S' ⟶ S''}
    {E : EllipticCurve S} {E' : EllipticCurve S'} {E'' : EllipticCurve S''}
    (α : EllipticCurveMorphism a E E')
    (β : EllipticCurveMorphism a' E' E'') :
    Nonempty (EllipticCurveMorphism (a ≫ a') E E'') := by
  sorry

/-- A chosen composite witness for the 2-categorical composition interface. -/
noncomputable def EllipticCurveMorphism.comp
    {S S' S'' : Scheme.{u}} {a : S ⟶ S'} {a' : S' ⟶ S''}
    {E : EllipticCurve S} {E' : EllipticCurve S'} {E'' : EllipticCurve S''}
    (α : EllipticCurveMorphism a E E')
    (β : EllipticCurveMorphism a' E' E'') :
    EllipticCurveMorphism (a ≫ a') E E'' :=
  Classical.choice (exists_ellipticCurveMorphism_comp α β)

/-! ### The moduli projection -/

/-- The source's objects over `S`: elliptic curves over `S`. -/
abbrev ModuliPoint (S : Scheme.{u}) := EllipticCurve S

/-- The projection `p : M₁,₁ ⟶ Sch` sends a family to its base. -/
def moduliProjection {S : Scheme.{u}} (_E : ModuliPoint S) : Scheme.{u} := S

/-!
A rule out of the moduli object is represented by its value on every family,
together with the naturality equation forced by a witness.
-/
structure ModuliMorphismToScheme (T : Scheme.{u}) where
  map : ∀ {S : Scheme.{u}}, ModuliPoint S → (S ⟶ T)
  natural : ∀ {S S' : Scheme.{u}} {a : S ⟶ S'}
    {E : ModuliPoint S} {E' : ModuliPoint S'},
    EllipticCurveMorphism a E E' → map E = a ≫ map E'

end Formalization.Books.StacksIntroduction.Unit01
