import Formalization.Books.Algebra.Unit12.TensorProducts
import Formalization.Books.Algebra.Unit78.FiniteProjectiveModules
import Formalization.Books.Algebra.Unit134.NaiveCotangentComplex
import Formalization.Books.Algebra.Unit137.SmoothRingMaps
import Formalization.Books.Algebra.Unit143.EtaleRingMaps
import Mathlib.Algebra.Module.RingHom
import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.LinearAlgebra.SymmetricAlgebra.Basic
import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.RingTheory.AdicCompletion.Basic
import Mathlib.RingTheory.IntegralClosure.IsIntegral.Basic
import Mathlib.RingTheory.Polynomial.UniversalFactorizationRing
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.RingTheory.TensorProduct.Quotient

/-!
# More on Algebra, Chapter 9: Lifting

This file records the definitions and theorem interfaces in the chapter on
lifting.  The étale quotient-lift data, finite projective predicate, smooth
algebras, and cotangent modules are the canonical interfaces established in
earlier chapters or in Mathlib.
-/

namespace Formalization.Books.MoreAlgebra.Unit09

open CategoryTheory
open Set
open scoped TensorProduct

noncomputable section

universe u v w

/-! ## Common lifting data and the introductory covering statement -/

/-- The chapter's étale extension lifting an algebra over `A ⧸ I` is the
canonical quotient-lift interface from Chapter 143, specialized to the
quotient algebra itself. -/
abbrev EtaleQuotientLiftData (A : Type u) [CommRing A] (I : Ideal A) :=
  Formalization.Books.Algebra.Unit143.EtaleLiftData A (A ⧸ I) I

/-- The quotient identification belonging to an étale quotient lift, oriented
from the base quotient to the quotient of the lifted algebra. -/
noncomputable def quotientLiftEquiv
    {A : Type u} [CommRing A] (I : Ideal A)
    (D : EtaleQuotientLiftData A I) :
    letI : CommRing D.S := D.commRingS
    letI : Algebra A D.S := D.algebraRS
    letI : Algebra (A ⧸ I)
        (D.S ⧸ Ideal.map (algebraMap A D.S) I) :=
      Ideal.Quotient.algebraQuotientOfLEComap Ideal.le_comap_map
    (A ⧸ I) ≃ₐ[A ⧸ I]
      (D.S ⧸ Ideal.map (algebraMap A D.S) I) := by
  letI : CommRing D.S := D.commRingS
  letI : Algebra A D.S := D.algebraRS
  letI : Algebra (A ⧸ I)
      (D.S ⧸ Ideal.map (algebraMap A D.S) I) :=
    Ideal.Quotient.algebraQuotientOfLEComap Ideal.le_comap_map
  exact (Classical.choice D.quotientEquiv).symm

/-- A finite disjoint open cover of an affine spectrum. -/
structure FiniteDisjointOpenCover
    (R : Type u) [CommRing R] (J : Type v) [Finite J] where
  opens : J → Set (PrimeSpectrum R)
  isOpen : ∀ j, IsOpen (opens j)
  pairwiseDisjoint : Pairwise (fun i j => Disjoint (opens i) (opens j))
  cover : ⋃ j, opens j = Set.univ

/-- The map on spectra induced by the quotient identification in an étale
quotient lift. -/
noncomputable def quotientSpectrumMap
    {A : Type u} [CommRing A] (I : Ideal A)
    (D : EtaleQuotientLiftData A I) :
    letI : CommRing D.S := D.commRingS
    letI : Algebra A D.S := D.algebraRS
    PrimeSpectrum (A ⧸ I) → PrimeSpectrum D.S := by
  letI : CommRing D.S := D.commRingS
  letI : Algebra A D.S := D.algebraRS
  letI : Algebra (A ⧸ I)
      (D.S ⧸ Ideal.map (algebraMap A D.S) I) :=
    Ideal.Quotient.algebraQuotientOfLEComap Ideal.le_comap_map
  exact PrimeSpectrum.comap (Ideal.Quotient.mk _) ∘
    (PrimeSpectrum.comapEquiv (quotientLiftEquiv I D).toRingEquiv)

/-- The assertion that `U'` is a lifted cover of `U`. -/
def CoverLifts
    {A : Type u} [CommRing A] (I : Ideal A)
    {J : Type v} [Finite J]
    (D : EtaleQuotientLiftData A I)
    (U : FiniteDisjointOpenCover (A ⧸ I) J)
    (U' : letI : CommRing D.S := D.commRingS
      FiniteDisjointOpenCover D.S J) : Prop :=
  letI : CommRing D.S := D.commRingS
  ∀ j, U.opens j = quotientSpectrumMap I D ⁻¹' U'.opens j

/-- The local étale-at-a-prime condition for a ring homomorphism. -/
def IsEtaleAtOver
    {A B : Type u} [CommRing A] [CommRing B]
    (f : A →+* B) (q : Ideal B) [q.IsPrime] : Prop :=
  letI : Algebra A B := f.toAlgebra
  Algebra.IsEtaleAt A q

/- The introductory catalogue is a cross-reference to the earlier algebra
   chapters for idempotents, projective and stably free modules, basis
   elements, formally smooth/syntomic/smooth/étale maps, polynomial
   factorization, and henselian local rings.  Those referenced results are
   not new assertions of this section; the chapter-specific interfaces are
   recorded below. -/

/-- Étale quotient identifications compose along composable étale ring maps.
This is the formal version of the general composition remark before the
numbered lemmas. -/
theorem compose_etale_quotient_lifts
    {A A' A'' : Type u} [CommRing A] [CommRing A'] [CommRing A'']
    (I : Ideal A) (f : A →+* A') (g : A' →+* A'')
    (hf : RingHom.Etale f) (hg : RingHom.Etale g)
    (e₁ : (A ⧸ I) ≃+* (A' ⧸ Ideal.map f I))
    (e₂ : (A' ⧸ Ideal.map f I) ≃+*
      (A'' ⧸ Ideal.map g (Ideal.map f I))) :
    RingHom.Etale (g.comp f) ∧
      Nonempty ((A ⧸ I) ≃+* (A'' ⧸ Ideal.map g (Ideal.map f I))) := by
  exact ⟨RingHom.Etale.stableUnderComposition f g hf hg,
    ⟨e₁.trans e₂⟩⟩

/-! ## Lifting individual elements -/

/-- A unit in `A ⧸ I` lifts to a unit in an étale extension of `A`. -/
theorem lift_invertible_element
    {A : Type u} [CommRing A] (I : Ideal A)
    (uBar : A ⧸ I) (hu : IsUnit uBar) :
    ∃ D : EtaleQuotientLiftData A I,
      letI : CommRing D.S := D.commRingS
      letI : Algebra A D.S := D.algebraRS
      ∃ u' : D.S, IsUnit u' ∧
        quotientLiftEquiv I D uBar = Ideal.Quotient.mk _ u' := by
  sorry

/-- An idempotent in `A ⧸ I` lifts to an idempotent in an étale extension of
`A`. -/
theorem lift_idempotent
    {A : Type u} [CommRing A] (I : Ideal A)
    (eBar : A ⧸ I) (he : IsIdempotentElem eBar) :
    ∃ D : EtaleQuotientLiftData A I,
      letI : CommRing D.S := D.commRingS
      letI : Algebra A D.S := D.algebraRS
      ∃ e' : D.S, IsIdempotentElem e' ∧
        quotientLiftEquiv I D eBar = Ideal.Quotient.mk _ e' := by
  sorry

/-- A finite disjoint open cover of `Spec (A ⧸ I)` lifts to one on an étale
extension of `A`. -/
theorem lift_open_covering
    {A : Type u} [CommRing A] (I : Ideal A)
    {J : Type v} [Finite J]
    (U : FiniteDisjointOpenCover (A ⧸ I) J) :
    ∃ D : EtaleQuotientLiftData A I,
      letI : CommRing D.S := D.commRingS
      letI : Algebra A D.S := D.algebraRS
      ∃ U' : FiniteDisjointOpenCover D.S J, CoverLifts I D U U' := by
  sorry

/-! ## Localizing an étale map -/

/-- If a map is étale at every prime over `J`, then after inverting one
element which is `1` modulo `J`, the resulting localization is étale. -/
theorem localize_upstairs
    {A B : Type u} [CommRing A] [CommRing B]
    (f : A →+* B) (J : Ideal B)
    (h : ∀ (q : Ideal B) [q.IsPrime], J ≤ q → IsEtaleAtOver f q) :
    letI : Algebra A B := f.toAlgebra
    ∃ g : B, IsUnit (Ideal.Quotient.mk J g) ∧
      Algebra.Etale A (Localization.Away g) := by
  sorry

/-! ## Lifting factorizations -/

/-- Data recording a factorization after an étale extension, together with
its prescribed reduction along the quotient identification. -/
def PolynomialFactorizationLift
    {A : Type u} [CommRing A] (I : Ideal A)
    (f : Polynomial A) (gBar hBar : Polynomial (A ⧸ I)) : Prop :=
  ∃ D : EtaleQuotientLiftData A I,
    letI : CommRing D.S := D.commRingS
    letI : Algebra A D.S := D.algebraRS
    ∃ g' h' : Polynomial D.S,
      Polynomial.map (algebraMap A D.S) f = g' * h' ∧
      Polynomial.map (Ideal.Quotient.mk _) g' =
        Polynomial.map (quotientLiftEquiv I D).toRingHom gBar ∧
      Polynomial.map (Ideal.Quotient.mk _) h' =
        Polynomial.map (quotientLiftEquiv I D).toRingHom hBar

/-- The stronger factorization data in which the lifted factors are monic. -/
def MonicPolynomialFactorizationLift
    {A : Type u} [CommRing A] (I : Ideal A)
    (f : Polynomial A) (gBar hBar : Polynomial (A ⧸ I)) : Prop :=
  ∃ D : EtaleQuotientLiftData A I,
    letI : CommRing D.S := D.commRingS
    letI : Algebra A D.S := D.algebraRS
    ∃ g' h' : Polynomial D.S,
      Polynomial.map (algebraMap A D.S) f = g' * h' ∧
      g'.Monic ∧ h'.Monic ∧
      Polynomial.map (Ideal.Quotient.mk _) g' =
        Polynomial.map (quotientLiftEquiv I D).toRingHom gBar ∧
      Polynomial.map (Ideal.Quotient.mk _) h' =
        Polynomial.map (quotientLiftEquiv I D).toRingHom hBar

/-- A coprime factorization of a monic polynomial lifts after an étale
extension when both factors are monic. -/
theorem lift_factorization_monic
    {A : Type u} [CommRing A] (I : Ideal A)
    (f : Polynomial A) (hf : f.Monic)
    (gBar hBar : Polynomial (A ⧸ I))
    (hfactor : Polynomial.map (Ideal.Quotient.mk I) f = gBar * hBar)
    (hg : gBar.Monic) (hh : hBar.Monic)
    (hcoprime : IsCoprime gBar hBar) :
    MonicPolynomialFactorizationLift I f gBar hBar := by
  sorry

/-- The factorization lifting theorem with the weaker hypothesis that one
factor has invertible leading coefficient. -/
theorem lift_factorization_easy
    {A : Type u} [CommRing A] (I : Ideal A)
    (f : Polynomial A) (hf : f.Monic)
    (gBar hBar : Polynomial (A ⧸ I))
    (hfactor : Polynomial.map (Ideal.Quotient.mk I) f = gBar * hBar)
    (hleading : IsUnit gBar.leadingCoeff)
    (hcoprime : IsCoprime gBar hBar) :
    PolynomialFactorizationLift I f gBar hBar := by
  sorry

/-- The ideal and polynomial appearing in the characteristic-two factorization
example. -/
def fourIdeal : Ideal ℤ := Ideal.span ({(4 : ℤ)} : Set ℤ)

def badFactor : Polynomial (ℤ ⧸ fourIdeal) :=
  Polynomial.C 1 + Polynomial.C 2 * Polynomial.X +
    Polynomial.C 2 * Polynomial.X ^ 2

/-- The reduction of `1` has the displayed factorization into two equal
factors, which generate the unit ideal, while the factor has nonunit leading
coefficient. -/
theorem bad_factorization_properties :
    Polynomial.map
        (Ideal.Quotient.mk fourIdeal)
        (1 : Polynomial ℤ) = badFactor * badFactor ∧
      IsCoprime badFactor badFactor ∧
      ¬ IsUnit badFactor.leadingCoeff := by
  sorry

/-- The source's 2-adic completion warning for an étale extension realizing
the same quotient as `ℤ / 4ℤ`. -/
def TwoAdicCompletionEquivZ2
    {A' : Type u} [CommRing A'] (f : ℤ →+* A') : Prop :=
  Nonempty
    (AdicCompletion (Ideal.span ({f 2} : Set A')) A' ≃+* PadicInt 2)

/-- An étale extension of `ℤ` with unchanged quotient modulo `4` has the
2-adic completion described in the example. -/
theorem bad_factorization_two_adic_completion
    {A' : Type u} [CommRing A'] (f : ℤ →+* A')
    (hf : RingHom.Etale f)
    (hquot :
      letI : Algebra ℤ A' := f.toAlgebra
      letI : Algebra (ℤ ⧸ fourIdeal)
          (A' ⧸ Ideal.map f fourIdeal) :=
        Ideal.Quotient.algebraQuotientOfLEComap Ideal.le_comap_map
      Nonempty ((ℤ ⧸ fourIdeal) ≃ₐ[ℤ ⧸ fourIdeal]
        (A' ⧸ Ideal.map f fourIdeal))) :
    TwoAdicCompletionEquivZ2 f := by
  sorry

/-- The displayed factor over the 2-adic integers. -/
def badFactorPadic : Polynomial (PadicInt 2) :=
  Polynomial.C 1 + Polynomial.C 2 * Polynomial.X +
    Polynomial.C 2 * Polynomial.X ^ 2

/-- Every polynomial congruent to the displayed factor modulo `4` is a
nonunit in the polynomial ring over the 2-adic integers. -/
theorem bad_factorization_two_adic_nonunit :
    ∀ q : Polynomial (PadicInt 2),
      (∀ n : ℕ,
        q.coeff n - badFactorPadic.coeff n ∈
          Ideal.span ({(4 : PadicInt 2)} : Set (PadicInt 2))) →
      ¬ IsUnit q := by
  sorry

/-- The factorization in the preceding example cannot be lifted through any
étale extension. -/
theorem cannot_lift_factorization :
    ¬ PolynomialFactorizationLift
      fourIdeal (1 : Polynomial ℤ)
      badFactor badFactor := by
  sorry

/-! ## Closed images and integral elements -/

/-- Disjointness of the closed image of `Spec B` over `J` from the closed set
defined by `I` produces an element which is `1` modulo `I` and maps into `J`.
The source's proof uses an integral element and the preceding factorization
lifting result. -/
theorem separate_image_closed_from_closed
    {A B : Type u} [CommRing A] [CommRing B]
    (f : A →+* B) (I : Ideal A) (J : Ideal B)
    (hdisjoint :
      Disjoint
        (closure (PrimeSpectrum.comap f ''
          PrimeSpectrum.zeroLocus (J : Set B)))
        (PrimeSpectrum.zeroLocus (I : Set A))) :
    ∃ a : A, Ideal.Quotient.mk I a = 1 ∧ f a ∈ J := by
  sorry

/-- An integral element which is idempotent modulo `I` satisfies a monic
polynomial whose reduction is `x^d (x - 1)^d`. -/
theorem helper_integral
    {A B : Type u} [CommRing A] [CommRing B]
    (f : A →+* B) (I : Ideal A) (hIntegral : f.IsIntegral) (b : B)
    (hb : IsIdempotentElem
      (Ideal.Quotient.mk (Ideal.map f I) b)) :
    ∃ p : Polynomial A, p.Monic ∧ Polynomial.eval₂ f b p = 0 ∧
      ∃ d : ℕ, 1 ≤ d ∧
        Polynomial.map (Ideal.Quotient.mk I) p =
          Polynomial.X ^ d *
            (Polynomial.X - Polynomial.C (1 : A ⧸ I)) ^ d := by
  sorry

/-! ## Lifting idempotents and projective modules upstairs -/

/-- An idempotent modulo an ideal becomes an idempotent after an étale base
extension, after tensoring with the original algebra. -/
def TensorQuotientElementLift
    {A B : Type u} [CommRing A] [CommRing B]
    (f : A →+* B) (I : Ideal A) (b : B)
    (D : EtaleQuotientLiftData A I) : Prop :=
  letI : Algebra A B := f.toAlgebra
  letI : CommRing D.S := D.commRingS
  letI : Algebra A D.S := D.algebraRS
  let T := B ⊗[A] D.S
  ∃ e' : T, IsIdempotentElem e' ∧
    ∃ q : (B ⧸ Ideal.map f I) ≃+*
        (T ⧸ Ideal.map (algebraMap A T) I),
      (∀ x : B,
        q (Ideal.Quotient.mk _ x) =
          Ideal.Quotient.mk _
            (Algebra.TensorProduct.includeLeftRingHom x)) ∧
      q (Ideal.Quotient.mk _ b) = Ideal.Quotient.mk _ e'

/-- An integral idempotent modulo `I` lifts to an idempotent upstairs after an
étale extension. -/
theorem lift_idempotent_upstairs
    {A B : Type u} [CommRing A] [CommRing B]
    (f : A →+* B) (I : Ideal A) (hIntegral : f.IsIntegral) (b : B)
    (hb : IsIdempotentElem
      (Ideal.Quotient.mk (Ideal.map f I) b)) :
    ∃ D : EtaleQuotientLiftData A I, TensorQuotientElementLift f I b D := by
  sorry

/-- A finite projective module over `A ⧸ I` lifts to a finite projective
module over an étale extension of `A`. -/
def FiniteProjectiveModuleQuotientLift
    {A : Type u} [CommRing A] (I : Ideal A)
    (PBar : ModuleCat.{u} (A ⧸ I))
    (D : EtaleQuotientLiftData A I) : Prop :=
  letI : CommRing D.S := D.commRingS
  letI : Algebra A D.S := D.algebraRS
  ∃ P' : ModuleCat.{u} D.S,
    Formalization.Books.Algebra.Unit78.FiniteProjective D.S P' ∧
      let Q := P' ⧸
        (Ideal.map (algebraMap A D.S) I • (⊤ : Submodule D.S P'))
      letI : Module (A ⧸ I) Q :=
        Module.compHom Q (quotientLiftEquiv I D).toRingHom
      Nonempty (Q ≃ₗ[A ⧸ I] PBar)

/-- Finite projectivity lifts across a quotient after passing to an étale
extension of the base. -/
theorem lift_projective_module
    {A : Type u} [CommRing A] (I : Ideal A)
    (PBar : ModuleCat.{u} (A ⧸ I))
    [Module.Finite (A ⧸ I) PBar]
    [Module.Projective (A ⧸ I) PBar] :
    ∃ D : EtaleQuotientLiftData A I,
      FiniteProjectiveModuleQuotientLift I PBar D := by
  sorry

/-! ## The symmetric algebra and its cotangent complex -/

/-- The polynomial presentation of a symmetric algebra obtained from a
surjection `p : A^m → M`. -/
noncomputable def symmetricAlgebraPresentationMap
    {A M : Type u} [CommRing A] [AddCommGroup M] [Module A M]
    {m : ℕ} (p : (Fin m → A) →ₗ[A] M) :
    MvPolynomial (Fin m) A →ₐ[A] SymmetricAlgebra A M :=
  MvPolynomial.aeval (fun i =>
    SymmetricAlgebra.ι A M (p (Pi.single i 1)))

/-- The presentation map in the preceding definition is surjective when the
chosen finite family generates `M`. -/
theorem symmetricAlgebraPresentationMap_surjective
    {A M : Type u} [CommRing A] [AddCommGroup M] [Module A M]
    {m : ℕ} (p : (Fin m → A) →ₗ[A] M)
    (hp : Function.Surjective p) :
    Function.Surjective (symmetricAlgebraPresentationMap p) := by
  sorry

/-- The `Algebra.Generators` presentation attached to a surjective polynomial
map into the symmetric algebra. -/
noncomputable def symmetricAlgebraPresentation
    {A M : Type u} [CommRing A] [AddCommGroup M] [Module A M]
    {m : ℕ} (p : (Fin m → A) →ₗ[A] M)
    (hp : Function.Surjective p) :
    Formalization.Books.Algebra.Unit134.Presentation
      A (SymmetricAlgebra A M) (Fin m) :=
  Formalization.Books.Algebra.Unit134.presentationFromSurjective
    (symmetricAlgebraPresentationMap p)
    (symmetricAlgebraPresentationMap_surjective p hp)

/-- The coordinate map used in the displayed cotangent complex. -/
noncomputable def symmetricAlgebraCoordinateMap
    {A K C : Type u} [CommRing A] [CommRing K]
    [Module A K] [CommRing C] [Algebra A C]
    {m : ℕ} (i : K →ₗ[A] (Fin m → A)) :
    K →ₗ[A] C →ₗ[A] (Fin m → C) where
  toFun k :=
    { toFun := fun c j => c * algebraMap A C (i k j)
      map_add' := by
        intro c d
        ext j
        simp [add_mul]
      map_smul' := by
        intro a c
        ext j
        simp [Algebra.smul_def, mul_assoc, mul_comm, mul_left_comm] }
  map_add' := by
    intro k l
    ext c j
    simp [mul_add]
  map_smul' := by
    intro a k
    ext c j
    simp [Algebra.smul_def, mul_left_comm]

/-- The tensor-product map in the source's displayed cotangent complex. -/
noncomputable def symmetricAlgebraCotangentMap
    {A K C : Type u} [CommRing A] [CommRing K]
    [Module A K] [CommRing C] [Algebra A C]
    {m : ℕ} (i : K →ₗ[A] (Fin m → A)) :
    K ⊗[A] C →ₗ[A] (Fin m → C) :=
  TensorProduct.lift (R := A) (M := K) (N := C) (P₂ := Fin m → C)
    (symmetricAlgebraCoordinateMap i)

/-- A source-facing package for the exact cotangent complex of a symmetric
algebra presentation.  The first equivalence identifies the conormal module,
the second identifies the presentation cotangent space with coordinates, and
the last field records the displayed differential. -/
structure SymmetricAlgebraCotangentModel
    {A K M : Type u} [CommRing A] [CommRing K] [AddCommGroup M]
    [Module A K] [Module A M]
    {m : ℕ} (i : K →ₗ[A] (Fin m → A))
    (p : (Fin m → A) →ₗ[A] M)
    (hp : Function.Surjective p) where
  tensorModule : Module (SymmetricAlgebra A M)
    (K ⊗[A] SymmetricAlgebra A M)
  conormalEquiv :
    letI : Module (SymmetricAlgebra A M)
        (K ⊗[A] SymmetricAlgebra A M) := tensorModule
    Formalization.Books.Algebra.Unit134.PresentationConormal
        (symmetricAlgebraPresentation p hp) ≃ₗ[SymmetricAlgebra A M]
          K ⊗[A] SymmetricAlgebra A M
  cotangentSpaceEquiv :
    Formalization.Books.Algebra.Unit134.PresentationCotangentSpace
        (symmetricAlgebraPresentation p hp) ≃ₗ[SymmetricAlgebra A M]
          (Fin m → SymmetricAlgebra A M)
  differential_commutes :
    letI : Module (SymmetricAlgebra A M)
        (K ⊗[A] SymmetricAlgebra A M) := tensorModule
    ∀ x : Formalization.Books.Algebra.Unit134.PresentationConormal
        (symmetricAlgebraPresentation p hp),
      cotangentSpaceEquiv
          ((Formalization.Books.Algebra.Unit134.PresentationNaiveCotangentComplex
            (symmetricAlgebraPresentation p hp)) x) =
        symmetricAlgebraCotangentMap i (conormalEquiv x)

/-- The source's cotangent-complex calculation for a symmetric algebra. -/
theorem cotangent_complex_symmetric_algebra
    {A K M : Type u} [CommRing A] [CommRing K] [AddCommGroup M]
    [Module A K] [Module A M]
    {m : ℕ} (i : K →ₗ[A] (Fin m → A))
    (p : (Fin m → A) →ₗ[A] M)
    (hi : Function.Injective i) (hexact : Function.Exact i p)
    (hp : Function.Surjective p) :
    letI : Module (SymmetricAlgebra A M)
        (M ⊗[A] SymmetricAlgebra A M) :=
      Formalization.Books.Algebra.Unit12.tensorProductBModule
        A (SymmetricAlgebra A M) M (SymmetricAlgebra A M)
    Nonempty (SymmetricAlgebraCotangentModel i p hp) ∧
      Nonempty
        (Formalization.Books.Algebra.Unit131.ModuleOfDifferentials
          A (SymmetricAlgebra A M) ≃ₗ[SymmetricAlgebra A M]
          M ⊗[A] SymmetricAlgebra A M) := by
  sorry

/-- The displayed Kähler-differential consequence of the symmetric-algebra
calculation. -/
theorem symmetric_algebra_differentials
    {A M : Type u} [CommRing A] [AddCommGroup M] [Module A M] :
    letI : Module (SymmetricAlgebra A M)
        (M ⊗[A] SymmetricAlgebra A M) :=
      Formalization.Books.Algebra.Unit12.tensorProductBModule
        A (SymmetricAlgebra A M) M (SymmetricAlgebra A M)
    Nonempty
      (Formalization.Books.Algebra.Unit131.ModuleOfDifferentials
        A (SymmetricAlgebra A M) ≃ₗ[SymmetricAlgebra A M]
        M ⊗[A] SymmetricAlgebra A M) := by
  sorry

/-! ## Smoothness and lifting sections -/

/-- A symmetric algebra is smooth exactly when its module of generators is
finite projective. -/
theorem symmetric_algebra_smooth
    {A M : Type u} [CommRing A] [AddCommGroup M] [Module A M] :
    Algebra.Smooth A (SymmetricAlgebra A M) ↔
      Formalization.Books.Algebra.Unit78.FiniteProjective A M := by
  sorry

/-- A section of a smooth morphism after quotienting the base lifts after an
étale extension of the base. -/
theorem lift_section_smooth_morphism
    {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    (I : Ideal A) [Algebra.Smooth A B]
    (g : B →ₐ[A] A ⧸ I) :
    ∃ D : EtaleQuotientLiftData A I,
      letI : CommRing D.S := D.commRingS
      letI : Algebra A D.S := D.algebraRS
      ∃ lift : B →ₐ[A] D.S,
        ∀ b : B,
          quotientLiftEquiv I D (g b) =
            Ideal.Quotient.mk _ (lift b) := by
  sorry

end

end Formalization.Books.MoreAlgebra.Unit09
