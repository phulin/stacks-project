import Formalization.Books.Algebra.Unit17.Spectrum
import Formalization.Books.Schemes.Unit03.OpenImmersions
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import Mathlib.AlgebraicGeometry.Morphisms.OpenImmersion
import Mathlib.RingTheory.RingHom.Etale
import Mathlib.RingTheory.LocalIso
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
Mathlib's `Algebra.IsLocalIso` is the canonical algebraic formulation of the
source's local-isomorphism definition.  The wrapper below equips a bare ring
homomorphism with its canonical algebra structure before using that predicate.
-/
def IsLocalIsomorphism {A B : Type u} [CommRing A] [CommRing B]
    (φ : A →+* B) : Prop :=
  letI : Algebra A B := φ.toAlgebra
  Algebra.IsLocalIso A B

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

/- The source's category of `A`-algebras is the full subcategory of the
   canonical under-category whose objects identify local rings. -/
def affineAlgebraProperty (A : Type u) [CommRing A] :
    ObjectProperty (Under (CommRingCat.of A)) :=
  fun B => IdentifiesLocalRings B.hom.hom

abbrev AffineAlgebrasWithIdentifiesLocalRings
    (A : Type u) [CommRing A] :=
  (affineAlgebraProperty A).FullSubcategory

abbrev AffineTopologicalSpacesOverSpec
    (A : Type u) [CommRing A] :=
  CostructuredArrow (𝟭 TopCat)
    (Spec (CommRingCat.of A)).toLocallyRingedSpace.toTopCat

/- The object part of the source's functor is the affine spectrum, regarded
   as a topological space over `Spec A`. -/
def affineSpecTopObject
    {A : Type u} [CommRing A]
    (B : AffineAlgebrasWithIdentifiesLocalRings A) :
    AffineTopologicalSpacesOverSpec A :=
  CostructuredArrow.mk (Spec.map B.obj.hom).base

/- The affine Spec construction on an algebra morphism, before packaging the
   resulting assignments as a functor. -/
def affineSpecTopMap
    {A : Type u} [CommRing A]
    {B C : AffineAlgebrasWithIdentifiesLocalRings A}
    (f : B ⟶ C) : affineSpecTopObject C ⟶ affineSpecTopObject B :=
  CostructuredArrow.homMk (Spec.map f.hom.right).base (by
    have hcomp : B.obj.hom ≫ f.hom.right = C.obj.hom := Under.w f.hom
    have hspec := congrArg (fun h => h.base) (show
        Spec.map f.hom.right ≫ Spec.map B.obj.hom = Spec.map C.obj.hom by
      rw [← Spec.map_comp, hcomp])
    change (Spec.map f.hom.right).base ≫ (Spec.map B.obj.hom).base =
      (Spec.map C.obj.hom).base
    exact hspec)

/- The actual functor named in the final statement of the source section. -/
def affineSpecTopFunctor (A : Type u) [CommRing A] :
    (AffineAlgebrasWithIdentifiesLocalRings A)ᵒᵖ ⥤
      AffineTopologicalSpacesOverSpec A where
  obj := fun B => affineSpecTopObject B.unop
  map := fun f => affineSpecTopMap f.unop
  map_id := by
    intro B
    apply CostructuredArrow.hom_ext
    change (Spec.map (𝟙 B.unop.obj.right)).base = _
    rfl
  map_comp := by
    intro B C D f g
    apply CostructuredArrow.hom_ext
    change (Spec.map (g.unop.hom.right ≫ f.unop.hom.right)).base = _
    rw [Spec.map_comp]
    rfl

theorem spec_fullyFaithful_of_identifiesLocalRings
    {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    (φB : A →+* B) (φC : A →+* C)
    (hB : IdentifiesLocalRings φB) (hC : IdentifiesLocalRings φC) :
    Function.Bijective (affineRingHomToTopOverHom φB φC) := by
  sorry

theorem affineSpecTopFunctor_fullyFaithful
    (A : Type u) [CommRing A] :
    Nonempty (affineSpecTopFunctor A).FullyFaithful := by
  sorry

end

end Formalization.Books.Proetale.Unit03
