import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Functor
import Mathlib.RingTheory.GradedAlgebra.Homogeneous.Maps
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.RingTheory.ReesAlgebra
import Mathlib.Topology.Sets.Closeds

/-!
# Exercises, Chapter 27: Proj of a ring

The chapter is expressed using Mathlib's internally graded rings and its
canonical projective spectrum.  In particular, `ProjectiveSpectrum` is the
source-facing set of relevant homogeneous prime ideals, `basicOpen` is
`D₊(f)`, `zeroLocus` is `V₊(I)`, and `HomogeneousLocalization.Away` is the
degree-zero localization `R_(f)`.
The blowup interfaces use Mathlib's canonical Rees algebra.  Mathlib does not
currently package its grading as a `GradedRing`, so a small presentation
structure records that grading and the degree-zero identification needed by
the natural map to `Spec(A)`.
-/

noncomputable section

universe u v

open CategoryTheory
open TopologicalSpace
open AlgebraicGeometry

namespace Formalization.Books.Exercises.Unit27

/-! ## Homogeneous ideals, Proj, and its standard opens -/

variable {R : Type u} [CommRing R]

/- The source's homogeneous-ideal predicate is Mathlib's canonical
   `Ideal.IsHomogeneous`; no parallel ideal structure is introduced. -/
abbrev IsHomogeneousIdeal (𝒜 : ℕ → Submodule ℤ R) [GradedAlgebra 𝒜]
    (I : Ideal R) : Prop :=
  Ideal.IsHomogeneous 𝒜 I

/- The source's `Proj(R)` as a point set is Mathlib's canonical
   `ProjectiveSpectrum`; the scheme `AlgebraicGeometry.«Proj»` is used only
   for the stronger scheme-level map recorded below. -/
abbrev ProjPoints (𝒜 : ℕ → Submodule ℤ R) [GradedAlgebra 𝒜] :=
  ProjectiveSpectrum 𝒜

/- The inclusion in `Spec(R)` is represented by the canonical prime ideal
   attached to a point of `ProjectiveSpectrum`. -/
def projToPrimeSpectrum (𝒜 : ℕ → Submodule ℤ R) [GradedAlgebra 𝒜]
    (x : ProjectiveSpectrum 𝒜) : PrimeSpectrum R :=
  ⟨x.asHomogeneousIdeal.toIdeal, x.isPrime⟩

/- Mathlib's `ProjectiveSpectrum.basicOpen` is an open.  Its carrier is the
   book's `D(g) ∩ Proj(R)` when `g` has degree zero, and is `D₊(f)` when `f`
   is homogeneous of positive degree. -/
abbrev dOnProj (𝒜 : ℕ → Submodule ℤ R) [GradedAlgebra 𝒜] (g : R) :
    Set (ProjectiveSpectrum 𝒜) :=
  (ProjectiveSpectrum.basicOpen 𝒜 g : Set (ProjectiveSpectrum 𝒜))

abbrev dPlus (𝒜 : ℕ → Submodule ℤ R) [GradedAlgebra 𝒜] (f : R) :
    Set (ProjectiveSpectrum 𝒜) :=
  dOnProj 𝒜 f

abbrev vPlus (𝒜 : ℕ → Submodule ℤ R) [GradedAlgebra 𝒜]
    (I : HomogeneousIdeal 𝒜) : Set (ProjectiveSpectrum 𝒜) :=
  ProjectiveSpectrum.zeroLocus 𝒜 (I : Set R)

/- The degree-zero part of the homogeneous localization is Mathlib's
   canonical `Away` construction. -/
abbrev degreeZeroLocalization (𝒜 : ℕ → Submodule ℤ R) [GradedAlgebra 𝒜]
    (f : R) :=
  HomogeneousLocalization.Away 𝒜 f

/- The scheme-level version of the continuous map in the chapter's remark. -/
noncomputable def projScheme (𝒜 : ℕ → Submodule ℤ R) [GradedAlgebra 𝒜] : Scheme :=
  AlgebraicGeometry.«Proj» 𝒜

noncomputable def projToSpecZeroScheme (𝒜 : ℕ → Submodule ℤ R) [GradedAlgebra 𝒜] :
    projScheme 𝒜 ⟶ Spec (CommRingCat.of (𝒜 0)) :=
  AlgebraicGeometry.Proj.toSpecZero 𝒜

/-! ## Rees algebras and the blowup presentations -/

/- Mathlib's Rees algebra is the canonical subalgebra
   `A[It] = ⨁ₙ Iⁿ tⁿ`, and is the usable representation of the book's
   `Bl_I(A)`. -/
abbrev blowupAlgebra {A : Type u} [CommRing A] (I : Ideal A) :=
  reesAlgebra I

def quotientIdeal {A : Type u} [CommRing A] (I p : Ideal A) : Ideal (A ⧸ p) :=
  Ideal.map (Ideal.Quotient.mk p) I

/- A grading and a degree-zero ring identification are the precise data needed
   to apply Mathlib's canonical Proj construction to a Rees algebra. -/
structure BlowupPresentation {A : Type u} [CommRing A] (I : Ideal A) where
  gradedPieces : ℕ → Submodule ℤ (blowupAlgebra I)
  graded : GradedRing gradedPieces
  degreeZeroEquiv : (gradedPieces 0) ≃+* A

abbrev blowupProjPoints {A : Type u} [CommRing A] {I : Ideal A}
    (P : BlowupPresentation I) : Type u :=
  letI : GradedRing P.gradedPieces := P.graded
  ProjectiveSpectrum P.gradedPieces

noncomputable def blowupProjScheme {A : Type u} [CommRing A] {I : Ideal A}
    (P : BlowupPresentation I) : Scheme :=
  letI : GradedRing P.gradedPieces := P.graded
  AlgebraicGeometry.«Proj» P.gradedPieces

noncomputable def blowupMap {A : Type u} [CommRing A] {I : Ideal A}
    (P : BlowupPresentation I) :
    blowupProjScheme P ⟶ Spec (CommRingCat.of A) :=
  letI : GradedRing P.gradedPieces := P.graded
  AlgebraicGeometry.Proj.toSpecZero P.gradedPieces ≫
    Spec.map (CommRingCat.ofHom P.degreeZeroEquiv.symm.toRingHom)

def blowupBaseOpen {A : Type u} [CommRing A] (I : Ideal A) :
    Set (PrimeSpectrum A) :=
  (PrimeSpectrum.zeroLocus (I : Set A))ᶜ

def blowupRestrictionMap {A : Type u} [CommRing A] {I : Ideal A}
    (P : BlowupPresentation I) :
    {x : blowupProjPoints P // (blowupMap P).base x ∈ blowupBaseOpen I} →
      {p : PrimeSpectrum A // p ∈ blowupBaseOpen I} :=
  fun x => ⟨(blowupMap P).base x.1, x.2⟩

/- The strict transform data records exactly the source hypotheses: an
   irreducible closed subset with a generic point outside `V(I)`, together
   with the unique point above that generic point. -/
structure StrictTransformData {A : Type u} [CommRing A] {I : Ideal A}
    (P : BlowupPresentation I) where
  Z : IrreducibleCloseds (PrimeSpectrum A)
  genericPoint : PrimeSpectrum A
  genericPoint_isGeneric : IsGenericPoint genericPoint Z
  genericPoint_mem_baseOpen : genericPoint ∈ blowupBaseOpen I
  lift : blowupProjPoints P
  lift_over_generic : (blowupMap P).base lift = genericPoint
  lift_unique : ∀ y : blowupProjPoints P,
    (blowupMap P).base y = genericPoint → y = lift

def strictTransform {A : Type u} [CommRing A] {I : Ideal A}
    {P : BlowupPresentation I} (D : StrictTransformData P) :
    Set (blowupProjPoints P) :=
  closure ({D.lift} : Set (blowupProjPoints P))

def strictTransformViaOpen {A : Type u} [CommRing A] {I : Ideal A}
    {P : BlowupPresentation I} (D : StrictTransformData P) :
    Set (blowupProjPoints P) :=
  closure ((blowupMap P).base ⁻¹' ((D.Z : Set (PrimeSpectrum A)) ∩ blowupBaseOpen I))

/- A prime-defined strict transform is convenient for the explicit blowing-up
   exercises and is the special case `Z = V(p)`. -/
structure PrimeStrictTransformData {A : Type u} [CommRing A] {I : Ideal A}
    (P : BlowupPresentation I) (p : Ideal A) (hp : p.IsPrime) where
  lift : blowupProjPoints P
  lift_over_prime : (blowupMap P).base lift = ⟨p, hp⟩
  lift_unique : ∀ y : blowupProjPoints P,
    (blowupMap P).base y = ⟨p, hp⟩ → y = lift

def primeStrictTransform {A : Type u} [CommRing A] {I : Ideal A}
    {P : BlowupPresentation I} {p : Ideal A} {hp : p.IsPrime}
    (D : PrimeStrictTransformData P p hp) :
    Set (blowupProjPoints P) :=
  closure ({D.lift} : Set (blowupProjPoints P))

/-! ## The quotient blowup used in Part III -/

structure BlowupQuotientMapData {A : Type u} [CommRing A]
    {I p : Ideal A} (P : BlowupPresentation I)
    (Q : BlowupPresentation (quotientIdeal I p)) where
  map :
    letI : GradedRing P.gradedPieces := P.graded
    letI : GradedRing Q.gradedPieces := Q.graded
    P.gradedPieces →+*ᵍ Q.gradedPieces
  surjective : Function.Surjective map
  irrelevant_le :
    letI : GradedRing P.gradedPieces := P.graded
    letI : GradedRing Q.gradedPieces := Q.graded
    HomogeneousIdeal.irrelevant Q.gradedPieces ≤
      (HomogeneousIdeal.irrelevant P.gradedPieces).map map

noncomputable def blowupQuotientProjMap {A : Type u} [CommRing A]
    {I p : Ideal A} {P : BlowupPresentation I}
    {Q : BlowupPresentation (quotientIdeal I p)}
    (F : BlowupQuotientMapData P Q) :
    blowupProjScheme Q ⟶ blowupProjScheme P :=
  letI : GradedRing P.gradedPieces := P.graded
  letI : GradedRing Q.gradedPieces := Q.graded
  AlgebraicGeometry.Proj.map F.map F.irrelevant_le

noncomputable def blowupStrictTransformIdeal {A : Type u} [CommRing A]
    {I p : Ideal A} {P : BlowupPresentation I}
    {Q : BlowupPresentation (quotientIdeal I p)}
    (F : BlowupQuotientMapData P Q) :
    letI : GradedRing P.gradedPieces := P.graded
    letI : GradedRing Q.gradedPieces := Q.graded
    HomogeneousIdeal P.gradedPieces :=
  letI : GradedRing P.gradedPieces := P.graded
  letI : GradedRing Q.gradedPieces := Q.graded
  (⊥ : HomogeneousIdeal Q.gradedPieces).comap F.map

/- A homogeneous Rees element makes the source's formula
   `P_d = I^d ∩ p` usable without introducing a second Rees algebra. -/
def reesHomogeneousElement {A : Type u} [CommRing A] (I : Ideal A)
    (d : ℕ) {a : A} (ha : a ∈ I ^ d) : blowupAlgebra I :=
  ⟨Polynomial.monomial d a, reesAlgebra.monomial_mem.mpr ha⟩

end Formalization.Books.Exercises.Unit27
