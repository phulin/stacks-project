import Formalization.Books.Algebra.Unit17.Spectrum
import Formalization.Books.Schemes.Unit03.OpenImmersions
import Mathlib.AlgebraicGeometry.Morphisms.OpenImmersion
import Mathlib.RingTheory.RingHom.Etale
import Mathlib.RingTheory.RingHom.QuasiFinite
import Mathlib.RingTheory.TensorProduct.Basic

/-!
# Pro-étale Cohomology, Chapter 3: Local isomorphisms

This file records the definitions and statements in the source section
“Local isomorphisms”.  The algebraic predicates use Mathlib's canonical
localizations, affine schemes, étale and quasi-finite ring-map properties,
and localization maps at primes.
-/

namespace Formalization.Books.Proetale.Unit03

open Set Function CategoryTheory
open AlgebraicGeometry
open scoped TensorProduct

universe u v

noncomputable section

/-! ## Definitions -/

/--
A ring map is a local isomorphism when every point of its target has a
standard-open neighborhood whose induced affine-scheme map is an open
immersion.
-/
def IsLocalIsomorphism {A B : Type u} [CommRing A] [CommRing B]
    (φ : A →+* B) : Prop :=
  ∀ q : PrimeSpectrum B, ∃ g : B, g ∉ q.asIdeal ∧
    IsOpenImmersion
      (Spec.map
        (CommRingCat.ofHom ((algebraMap B (Localization.Away g)).comp φ)))

/--
A ring map identifies local rings when its canonical map between the local
localizations at corresponding prime ideals is bijective.
-/
def IdentifiesLocalRings {A B : Type u} [CommRing A] [CommRing B]
    (φ : A →+* B) : Prop :=
  ∀ q : PrimeSpectrum B,
    Function.Bijective
      (Localization.localRingHom (q.asIdeal.comap φ) q.asIdeal φ rfl)

/-! ## Elementary permanence properties -/

theorem baseChange_isLocalIsomorphism
    {A B A' : Type u} [CommRing A] [CommRing B] [CommRing A']
    (φ : A →+* B) (ψ : A →+* A') (h : IsLocalIsomorphism φ) :
    letI := φ.toAlgebra
    letI := ψ.toAlgebra
    IsLocalIsomorphism
      (Algebra.TensorProduct.includeRight.toRingHom :
        A' →+* B ⊗[A] A') := by
  sorry

theorem baseChange_identifiesLocalRings
    {A B A' : Type u} [CommRing A] [CommRing B] [CommRing A']
    (φ : A →+* B) (ψ : A →+* A') (h : IdentifiesLocalRings φ) :
    letI := φ.toAlgebra
    letI := ψ.toAlgebra
    IdentifiesLocalRings
      (Algebra.TensorProduct.includeRight.toRingHom :
        A' →+* B ⊗[A] A') := by
  sorry

theorem comp_isLocalIsomorphism
    {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    (φ : A →+* B) (ψ : B →+* C)
    (hφ : IsLocalIsomorphism φ) (hψ : IsLocalIsomorphism ψ) :
    IsLocalIsomorphism (ψ.comp φ) := by
  sorry

theorem comp_identifiesLocalRings
    {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    (φ : A →+* B) (ψ : B →+* C)
    (hφ : IdentifiesLocalRings φ) (hψ : IdentifiesLocalRings ψ) :
    IdentifiesLocalRings (ψ.comp φ) := by
  sorry

theorem of_isLocalIsomorphism_of_isLocalIsomorphism
    {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra A C]
    (f : B →ₐ[A] C)
    (hB : IsLocalIsomorphism (algebraMap A B))
    (hC : IsLocalIsomorphism (algebraMap A C)) :
    IsLocalIsomorphism f.toRingHom := by
  sorry

theorem of_identifiesLocalRings_of_identifiesLocalRings
    {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra A C]
    (f : B →ₐ[A] C)
    (hB : IdentifiesLocalRings (algebraMap A B))
    (hC : IdentifiesLocalRings (algebraMap A C)) :
    IdentifiesLocalRings f.toRingHom := by
  sorry

/-! ## Consequences of local isomorphisms -/

theorem IsLocalIsomorphism.isEtale
    {A B : Type u} [CommRing A] [CommRing B]
    {φ : A →+* B} (hφ : IsLocalIsomorphism φ) :
    RingHom.Etale φ := by
  sorry

theorem IsLocalIsomorphism.identifiesLocalRings
    {A B : Type u} [CommRing A] [CommRing B]
    {φ : A →+* B} (hφ : IsLocalIsomorphism φ) :
    IdentifiesLocalRings φ := by
  sorry

theorem IsLocalIsomorphism.isQuasiFinite
    {A B : Type u} [CommRing A] [CommRing B]
    {φ : A →+* B} (hφ : IsLocalIsomorphism φ) :
    RingHom.QuasiFinite φ := by
  sorry

/-! ## A finite standard-open presentation -/

theorem IsLocalIsomorphism.exists_finite_standardOpen_cover
    {A B : Type u} [CommRing A] [CommRing B]
    {φ : A →+* B} (hφ : IsLocalIsomorphism φ) :
    ∃ (n : ℕ) (g : Fin n → B) (f : Fin n → A),
      Ideal.span (Set.range g) = ⊤ ∧
        ∀ i, ∃ e : Localization.Away (f i) ≃+* Localization.Away (g i),
          e.toRingHom.comp (algebraMap A (Localization.Away (f i))) =
            (algebraMap B (Localization.Away (g i))).comp φ := by
  sorry

/-! ## Locally ringed spaces over a fixed base -/

/-- The adjoint form of the structure-sheaf map of a locally ringed-space
morphism.  This is the canonical map from the pullback of the target sheaf to
the source sheaf. -/
def structureSheafPullbackMap
    {X Y : LocallyRingedSpace.{u}} (p : Y ⟶ X) :
    (TopCat.Sheaf.pullback CommRingCat p.base).obj X.𝒪 ⟶ Y.𝒪 :=
  let c : X.𝒪 ⟶ (TopCat.Sheaf.pushforward CommRingCat p.base).obj Y.𝒪 :=
    (TopCat.Sheaf.forget CommRingCat X.toTopCat).preimage p.toShHom.hom.c
  ((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat p.base).homEquiv
    X.𝒪 Y.𝒪).symm c

/-- The structure sheaf of the source is the pullback of the target sheaf. -/
def IsPullbackStructureSheaf
    {X Y : LocallyRingedSpace.{u}} (p : Y ⟶ X) : Prop :=
  IsIso (structureSheafPullbackMap p)

abbrev LRSOverHom
    {X Y Z : LocallyRingedSpace.{u}} (p : Y ⟶ X) (q : Z ⟶ X) :=
  (CostructuredArrow.mk q : CostructuredArrow (𝟭 LocallyRingedSpace) X) ⟶
    CostructuredArrow.mk p

abbrev TopOverHom
    {X Y Z : LocallyRingedSpace.{u}} (p : Y ⟶ X) (q : Z ⟶ X) :=
  (CostructuredArrow.mk q.base : CostructuredArrow (𝟭 TopCat) X.toTopCat) ⟶
    CostructuredArrow.mk p.base

/-- Forget a locally ringed-space morphism over `X` to its underlying map of
topological spaces over `X`. -/
def lrsOverHomToTopOverHom
    {X Y Z : LocallyRingedSpace.{u}} (p : Y ⟶ X) (q : Z ⟶ X) :
    LRSOverHom p q → TopOverHom p q := fun f =>
  CostructuredArrow.homMk f.left.base (by
    simpa using congrArg (fun h : Z ⟶ X => h.base) (CostructuredArrow.w f))

theorem fullyFaithfulSpacesOverX
    {X Y Z : LocallyRingedSpace.{u}} (p : Y ⟶ X) (q : Z ⟶ X)
    (hp : IsPullbackStructureSheaf p) :
    Function.Bijective (lrsOverHomToTopOverHom p q) := by
  sorry

/-! ## The affine local-isomorphism functor -/

/-- Morphisms over `Spec A` between the affine topological spaces associated
to two `A`-algebras. -/
abbrev AffineTopOverHom
    {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    (φB : A →+* B) (φC : A →+* C) :=
  (CostructuredArrow.mk (Spec.map (CommRingCat.ofHom φC)).base :
      CostructuredArrow (𝟭 TopCat)
        (Spec (CommRingCat.of A)).toLocallyRingedSpace.toTopCat) ⟶
    CostructuredArrow.mk (Spec.map (CommRingCat.ofHom φB)).base

/-- The map on morphisms induced by the affine `Spec` construction. -/
def affineRingHomToTopOverHom
    {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    (φB : A →+* B) (φC : A →+* C) :
    {f : B →+* C // f.comp φB = φC} → AffineTopOverHom φB φC := fun f =>
  CostructuredArrow.homMk (Spec.map (CommRingCat.ofHom f.1)).base (by
    have hcomp :
        (CommRingCat.ofHom φB) ≫ CommRingCat.ofHom f.1 =
          CommRingCat.ofHom φC := by
      rw [← CommRingCat.ofHom_comp]
      exact congrArg CommRingCat.ofHom f.2
    have hspec := congrArg (fun h => h.base) (show
        Spec.map (CommRingCat.ofHom f.1) ≫
            Spec.map (CommRingCat.ofHom φB) =
          Spec.map (CommRingCat.ofHom φC) by
      rw [← Spec.map_comp, hcomp])
    change (Spec.map (CommRingCat.ofHom f.1)).base ≫
        (Spec.map (CommRingCat.ofHom φB)).base =
      (Spec.map (CommRingCat.ofHom φC)).base
    exact hspec)

theorem spec_fullyFaithful_of_identifiesLocalRings
    {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    (φB : A →+* B) (φC : A →+* C)
    (hB : IdentifiesLocalRings φB) (hC : IdentifiesLocalRings φC) :
    Function.Bijective (affineRingHomToTopOverHom φB φC) := by
  sorry

end

end Formalization.Books.Proetale.Unit03
