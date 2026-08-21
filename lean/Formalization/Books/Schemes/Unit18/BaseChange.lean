import Formalization.Books.Schemes.Unit17.FibreProducts
import Mathlib.AlgebraicGeometry.Fiber
import Mathlib.AlgebraicGeometry.Over

/-!
# Schemes, Chapter 18: Base change in algebraic geometry

This file records the source-facing language for schemes over a base, base changes, and
scheme-theoretic fibres.  The underlying constructions are Mathlib's canonical over-category,
pullback, fibre, stalk, and residue-field APIs.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry
open Topology
open TopologicalSpace
open scoped TensorProduct

namespace Formalization.Books.Schemes.Unit18

universe u

/-! ## Schemes over a base -/

/- The textbook's phrase `scheme over S` is Mathlib's existing `Scheme.Over` typeclass. -/
abbrev IsSchemeOver (X S : Scheme.{u}) := X.Over S

/-- The structure morphism of a scheme over a base. -/
abbrev structureMorphism (X S : Scheme.{u}) [X.Over S] : X ⟶ S := X ↘ S

/-- A morphism of schemes over `S`, using Mathlib's canonical compatibility predicate. -/
abbrev IsMorphismOver (S : Scheme.{u}) {X Y : Scheme.{u}} [X.Over S] [Y.Over S]
    (f : X ⟶ Y) : Prop := f.IsOver S

/-- The set `Mor_S(X, Y)` of morphisms over a fixed base. -/
def morphismsOver (S X Y : Scheme.{u}) [X.Over S] [Y.Over S] : Set (X ⟶ Y) :=
  {f | IsMorphismOver S f}

/-! ## Base changes -/

/-- The scheme `S' ×_S X`, for a scheme `X` over `S` and a map `S' ⟶ S`. -/
abbrev baseChangeScheme {S S' : Scheme.{u}} (X : Scheme.{u}) [X.Over S]
    (g : S' ⟶ S) : Scheme.{u} :=
  pullback g (X ↘ S)

/-- The canonical structure morphism `S' ×_S X ⟶ S'`. -/
abbrev baseChangeSchemeStructureMap {S S' : Scheme.{u}} (X : Scheme.{u}) [X.Over S]
    (g : S' ⟶ S) : baseChangeScheme X g ⟶ S' :=
  pullback.fst g (X ↘ S)

noncomputable instance baseChangeScheme_over {S S' : Scheme.{u}} (X : Scheme.{u})
    [X.Over S] (g : S' ⟶ S) : (baseChangeScheme X g).Over S' :=
  ⟨baseChangeSchemeStructureMap X g⟩

/-- The induced morphism `S' ×_S X ⟶ S' ×_S Y` associated to an `S`-morphism `f`. -/
def baseChangeMorphism {S X Y S' : Scheme.{u}} [X.Over S] [Y.Over S]
    (f : X ⟶ Y) [f.IsOver S] (g : S' ⟶ S) :
    baseChangeScheme X g ⟶ baseChangeScheme Y g :=
  pullback.map g (X ↘ S) g (Y ↘ S) (𝟙 S') f (𝟙 S)
    (by simp) (CategoryTheory.comp_over f S).symm

noncomputable instance baseChangeMorphism_isOver {S X Y S' : Scheme.{u}} [X.Over S] [Y.Over S]
    (f : X ⟶ Y) [f.IsOver S] (g : S' ⟶ S) :
    (baseChangeMorphism (S := S) (S' := S') f g).IsOver S' := by
  sorry

/-! ## Base change along a ring map -/

/-- The scheme map induced by a ring homomorphism, viewed as a base change map. -/
abbrev ringBaseChangeMap {R R' : Type u} [CommRing R] [CommRing R'] (φ : R →+* R') :
    Spec (CommRingCat.of R') ⟶ Spec (CommRingCat.of R) :=
  Spec.map (CommRingCat.ofHom φ)

/- The textbook's phrase `scheme over R` is the existing `Scheme.Over` instance over `Spec R`. -/
abbrev IsSchemeOverRing {R : Type u} [CommRing R] (X : Scheme.{u}) :=
  X.Over (Spec (CommRingCat.of R))

/-- The base change `X_{R'}` of a scheme over `R` along `R ⟶ R'`. -/
abbrev ringBaseChangeScheme {R R' : Type u} [CommRing R] [CommRing R']
    (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of R))] (φ : R →+* R') : Scheme.{u} :=
  baseChangeScheme X (ringBaseChangeMap φ)

/- The structure map of `X_{R'}` to `Spec R'`. -/
abbrev ringBaseChangeStructureMap {R R' : Type u} [CommRing R] [CommRing R']
    (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of R))] (φ : R →+* R') :
    ringBaseChangeScheme X φ ⟶ Spec (CommRingCat.of R') :=
  baseChangeSchemeStructureMap X (ringBaseChangeMap φ)

/-! ## Preservation under base change -/

/-- Immersions remain immersions after arbitrary base change. -/
theorem baseChangeMorphism_isImmersion {S X Y S' : Scheme.{u}} [X.Over S] [Y.Over S]
    (f : X ⟶ Y) [f.IsOver S] [IsImmersion f] (g : S' ⟶ S) :
    IsImmersion (baseChangeMorphism (S := S) (S' := S') f g) := by
  sorry

/-- Closed immersions remain closed immersions after arbitrary base change. -/
theorem baseChangeMorphism_isClosedImmersion {S X Y S' : Scheme.{u}} [X.Over S] [Y.Over S]
    (f : X ⟶ Y) [f.IsOver S] [IsClosedImmersion f] (g : S' ⟶ S) :
    IsClosedImmersion (baseChangeMorphism (S := S) (S' := S') f g) := by
  sorry

/-- Open immersions remain open immersions after arbitrary base change. -/
theorem baseChangeMorphism_isOpenImmersion {S X Y S' : Scheme.{u}} [X.Over S] [Y.Over S]
    (f : X ⟶ Y) [f.IsOver S] [IsOpenImmersion f] (g : S' ⟶ S) :
    IsOpenImmersion (baseChangeMorphism (S := S) (S' := S') f g) := by
  sorry

/-- The base change of a property of schemes over a base. -/
abbrev SchemeOverProperty : Type (u + 1) :=
  ∀ {S X : Scheme.{u}} [X.Over S], Prop

/-- The base change of a property of morphisms of schemes over a base. -/
abbrev SchemeMorphismOverProperty : Type (u + 1) :=
  ∀ {S X Y : Scheme.{u}} [X.Over S] [Y.Over S]
    (f : X ⟶ Y) [f.IsOver S], Prop

/-- A property of schemes over a base is preserved by arbitrary base change. -/
def schemePropertyPreservedByBaseChange (P : SchemeOverProperty.{u}) : Prop :=
  ∀ {S X S' : Scheme.{u}} [X.Over S] (g : S' ⟶ S),
    P (S := S) (X := X) →
      P (S := S') (X := baseChangeScheme (S := S) (S' := S') X g)

/-- A property of morphisms over a base is preserved by arbitrary base change. -/
def morphismPropertyPreservedByBaseChange (P : SchemeMorphismOverProperty.{u}) : Prop :=
  ∀ {S X Y S' : Scheme.{u}} [X.Over S] [Y.Over S]
    (f : X ⟶ Y) [f.IsOver S] (g : S' ⟶ S),
    P (S := S) (X := X) (Y := Y) f →
      P (S := S')
        (X := baseChangeScheme (S := S) (S' := S') X g)
        (Y := baseChangeScheme (S := S) (S' := S') Y g)
        (baseChangeMorphism (S := S) (S' := S') f g)

/-! ## Scheme-theoretic fibres -/

/-- The scheme-theoretic fibre of `f` over the point `s`. -/
abbrev schemeTheoreticFiber {X S : Scheme.{u}} (f : X ⟶ S) (s : S) : Scheme.{u} :=
  f.fiber s

/-- The canonical map from the scheme-theoretic fibre to `X`. -/
abbrev schemeTheoreticFiberInclusion {X S : Scheme.{u}} (f : X ⟶ S) (s : S) :
    schemeTheoreticFiber f s ⟶ X :=
  f.fiberι s

/-- The canonical structure map of the fibre to `Spec κ(s)`. -/
abbrev schemeTheoreticFiberStructureMap {X S : Scheme.{u}} (f : X ⟶ S) (s : S) :
    schemeTheoreticFiber f s ⟶ Spec (S.residueField s) :=
  f.fiberToSpecResidueField s

/-- The fibre, bundled as a scheme over the residue field of the chosen point. -/
abbrev schemeTheoreticFiberOverResidueField {X S : Scheme.{u}} (f : X ⟶ S) (s : S) :=
  f.fiberOverSpecResidueField s

/-! ## Topological fibre squares -/

/-- The scheme-theoretic fibre square remains a pullback after forgetting to topological spaces. -/
theorem schemeTheoreticFiber_topological_isPullback {X S : Scheme.{u}} (f : X ⟶ S) (s : S) :
    IsPullback (f.fiberι s).base (f.fiberToSpecResidueField s).base
      f.base (S.fromSpecResidueField s).base := by
  sorry

/-- The fibre inclusion is a homeomorphism onto its image. -/
theorem schemeTheoreticFiber_topological_isEmbedding {X S : Scheme.{u}} (f : X ⟶ S) (s : S) :
    IsEmbedding (f.fiberι s) := by
  exact (f.fiberι s).isEmbedding

/-- The local-ring fibre `Spec(O_{S,s}) ×_S X`, with its projection to `X`. -/
abbrev localRingFiber {X S : Scheme.{u}} (f : X ⟶ S) (s : S) : Scheme.{u} :=
  pullback f (S.fromSpecStalk s)

/-- The canonical map from the local-ring fibre to `X`. -/
abbrev localRingFiberInclusion {X S : Scheme.{u}} (f : X ⟶ S) (s : S) :
    localRingFiber f s ⟶ X :=
  pullback.fst f (S.fromSpecStalk s)

/-- The local-ring fibre square remains a pullback after forgetting to topological spaces. -/
theorem localRingFiber_topological_isPullback {X S : Scheme.{u}} (f : X ⟶ S) (s : S) :
    IsPullback (pullback.fst f (S.fromSpecStalk s)).base
      (pullback.snd f (S.fromSpecStalk s)).base
      f.base (S.fromSpecStalk s).base := by
  sorry

/-- The local-ring fibre inclusion is a homeomorphism onto its image. -/
theorem localRingFiber_topological_isEmbedding {X S : Scheme.{u}} (f : X ⟶ S) (s : S) :
    IsEmbedding (localRingFiberInclusion f s) := by
  exact (localRingFiberInclusion f s).isEmbedding

/-! ## Stalks of fibres -/

/-- At a point `x` over `s`, the fibre stalk is the local-ring quotient and its tensor form. -/
theorem localRingFiber_stalk_quotient_tensor {X S : Scheme.{u}} (f : X ⟶ S) (x : X) :
    let R := S.presheaf.stalk (f x)
    let A := X.presheaf.stalk x
    letI : Algebra R A := (f.stalkMap x).hom.toAlgebra
    letI : Algebra R (S.residueField (f x)) := (S.residue (f x)).hom.toAlgebra
    Nonempty
        ((schemeTheoreticFiber f (f x)).presheaf.stalk (f.asFiber x) ≅
          CommRingCat.of
            (A ⧸ Ideal.map (f.stalkMap x).hom (IsLocalRing.maximalIdeal R))) ∧
      Nonempty
        (CommRingCat.of
            (A ⧸ Ideal.map (f.stalkMap x).hom (IsLocalRing.maximalIdeal R)) ≅
          CommRingCat.of (A ⊗[R] (S.residueField (f x)))) := by
  sorry

end Formalization.Books.Schemes.Unit18
