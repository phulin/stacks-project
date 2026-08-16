import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
import Mathlib.AlgebraicGeometry.Restrict
import Mathlib.Data.PNat.Notation
import Mathlib.RingTheory.Polynomial.Basic

/-!
# Examples, Chapter 24: Taking scheme theoretic images

This file formalizes the example in the source section “Taking scheme
theoretic images”.  The scheme-theoretic image itself is Mathlib's canonical
`Scheme.Hom.image`; the declarations below expose the source construction and
record the two failures described in the example.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits
open TopologicalSpace
open AlgebraicGeometry

namespace Formalization.«Books.Examples».Unit24

/-- The polynomial variable `t` in the target ring `k[t]`. -/
def schemeTheoreticImageVariable (k : Type u) [Field k] : Polynomial k :=
  Polynomial.X

/-- The target affine scheme `Y = Spec(k[t])`, with `k[t]` represented by `Polynomial k`. -/
abbrev schemeTheoreticImageTarget (k : Type u) [Field k] : Scheme :=
  Spec (CommRingCat.of (Polynomial k))

/-- The ideal `(tⁿ)` defining the `n`-th infinitesimal neighbourhood of `t = 0`. -/
def schemeTheoreticImageComponentIdeal (k : Type u) [Field k] (n : ℕ+) : Ideal (Polynomial k) :=
  Ideal.span {schemeTheoreticImageVariable k ^ (n : ℕ)}

/-- The coordinate ring `k[t]/(tⁿ)` of the `n`-th component. -/
abbrev schemeTheoreticImageComponentRing (k : Type u) [Field k] (n : ℕ+) :=
  Polynomial k ⧸ schemeTheoreticImageComponentIdeal k n

/-- The closed immersion `Spec(k[t]/(tⁿ)) ⟶ Spec(k[t])`. -/
noncomputable def schemeTheoreticImageComponentMap (k : Type u) [Field k] (n : ℕ+) :
    Spec (CommRingCat.of (schemeTheoreticImageComponentRing k n)) ⟶
      schemeTheoreticImageTarget k :=
  Spec.map <| CommRingCat.ofHom <| Ideal.Quotient.mk
    (schemeTheoreticImageComponentIdeal k n)

instance schemeTheoreticImageComponentMap_isClosedImmersion
    (k : Type u) [Field k] (n : ℕ+) :
    IsClosedImmersion (schemeTheoreticImageComponentMap k n) := by
  change IsClosedImmersion
    (Spec.map (CommRingCat.ofHom
      (Ideal.Quotient.mk (schemeTheoreticImageComponentIdeal k n))))
  exact IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective

/-- The countable coproduct `X = ⨿ₙ Spec(k[t]/(tⁿ))`. -/
noncomputable def schemeTheoreticImageSource (k : Type u) [Field k] : Scheme :=
  ∐ fun n : ℕ+ ↦ Spec (CommRingCat.of (schemeTheoreticImageComponentRing k n))

/-- The morphism obtained by assembling the component closed immersions. -/
noncomputable def schemeTheoreticImageMorphism (k : Type u) [Field k] :
    schemeTheoreticImageSource k ⟶ schemeTheoreticImageTarget k :=
  Sigma.desc fun n : ℕ+ ↦ schemeTheoreticImageComponentMap k n

/-- The ordinary topological image of the displayed morphism. -/
def schemeTheoreticImageTopologicalImage (k : Type u) [Field k] :
    Set (schemeTheoreticImageTarget k) :=
  Set.range (schemeTheoreticImageMorphism k)

/-- The closed subset underlying the scheme-theoretic image. -/
def schemeTheoreticImageCarrier (k : Type u) [Field k] :
    Set (schemeTheoreticImageTarget k) :=
  Set.range (schemeTheoreticImageMorphism k).imageι

/-- The closed point `t = 0`, written as the zero locus of `t`. -/
def schemeTheoreticImageClosedPoint (k : Type u) [Field k] :
    Set (schemeTheoreticImageTarget k) :=
  PrimeSpectrum.zeroLocus
    ({(schemeTheoreticImageVariable k : ↑(CommRingCat.of (Polynomial k)))} :
      Set (↑(CommRingCat.of (Polynomial k))))

/-- In this example the scheme-theoretic image is the whole target scheme. -/
theorem schemeTheoreticImage_is_target (k : Type u) [Field k] :
    IsIso (schemeTheoreticImageMorphism k).imageι := by
  sorry

/-- The ordinary image is the closed point `t = 0`. -/
theorem schemeTheoreticImageTopologicalImage_eq_closedPoint (k : Type u) [Field k] :
    schemeTheoreticImageTopologicalImage k = schemeTheoreticImageClosedPoint k := by
  sorry

/-- The scheme-theoretic image carrier is not the closure of the ordinary image. -/
theorem schemeTheoreticImageCarrier_ne_closure_topologicalImage
    (k : Type u) [Field k] :
    schemeTheoreticImageCarrier k ≠ closure (schemeTheoreticImageTopologicalImage k) := by
  sorry

/-- The open `D(t) ⊆ Y`, viewed as the basic open of the target spectrum. -/
def schemeTheoreticImageOpen (k : Type u) [Field k] :
    (schemeTheoreticImageTarget k).Opens :=
  PrimeSpectrum.basicOpen
    (R := ↑(CommRingCat.of (Polynomial k)))
    (schemeTheoreticImageVariable k : ↑(CommRingCat.of (Polynomial k)))

/-- The open `D(t)` is the affine scheme `Spec(k[t, 1/t])`. -/
noncomputable def schemeTheoreticImageOpenIsoSpecLocalization (k : Type u) [Field k] :
    (schemeTheoreticImageOpen k).toScheme ≅
      Spec (.of (Localization.Away (schemeTheoreticImageVariable k))) :=
  basicOpenIsoSpecAway (R := CommRingCat.of (Polynomial k))
    (schemeTheoreticImageVariable k : ↑(CommRingCat.of (Polynomial k)))

/-- The source has empty preimage over `D(t)`. -/
def schemeTheoreticImageSourcePreimageOfOpen (k : Type u) [Field k] :
    (schemeTheoreticImageSource k).Opens :=
  schemeTheoreticImageMorphism k ⁻¹ᵁ schemeTheoreticImageOpen k

theorem schemeTheoreticImageSourcePreimageOfOpen_eq_empty (k : Type u) [Field k] :
    schemeTheoreticImageSourcePreimageOfOpen k = ⊥ := by
  sorry

/-- The restriction of the example morphism to `D(t)`. -/
noncomputable def schemeTheoreticImageRestrictedMorphism (k : Type u) [Field k] :
    (schemeTheoreticImageSourcePreimageOfOpen k).toScheme ⟶
      (schemeTheoreticImageOpen k).toScheme :=
  schemeTheoreticImageMorphism k ∣_ schemeTheoreticImageOpen k

/-- The restricted morphism has the empty scheme as its scheme-theoretic image. -/
theorem schemeTheoreticImageRestrictedMorphism_image_is_empty
    (k : Type u) [Field k] :
    IsEmpty (schemeTheoreticImageRestrictedMorphism k).image := by
  sorry

/-- The restricted scheme-theoretic image is isomorphic to the empty scheme. -/
theorem schemeTheoreticImageRestrictedMorphism_image_iso_empty
    (k : Type u) [Field k] :
    Nonempty ((schemeTheoreticImageRestrictedMorphism k).image ≅ (∅ : Scheme)) := by
  sorry

/-- Restriction to `D(t)` does not preserve the scheme-theoretic image. -/
theorem schemeTheoreticImageRestrictedMorphism_imageι_not_isIso
    (k : Type u) [Field k] :
    ¬ IsIso (schemeTheoreticImageRestrictedMorphism k).imageι := by
  sorry

end Formalization.«Books.Examples».Unit24
