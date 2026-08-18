import Formalization.Books.Algebra.Unit148.FormallyUnramifiedMaps
import Mathlib.RingTheory.RingHom.Etale
import Mathlib.RingTheory.FinitePresentation
import Mathlib.RingTheory.FiniteStability
import Mathlib.RingTheory.Kaehler.TensorProduct
import Mathlib.RingTheory.KrullDimension.Polynomial
import Mathlib.RingTheory.RingHom.QuasiFinite
import Mathlib.RingTheory.Unramified.Finite
import Mathlib.RingTheory.Unramified.LocalStructure
import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
import Mathlib.RingTheory.Spectrum.Maximal.Localization

/-!
# Commutative Algebra, Chapter 151: Unramified ring maps

The source uses “unramified” for finite type with vanishing Kähler
differentials, and “G-unramified” for finite presentation with the same
vanishing condition.  Mathlib's `Algebra.Unramified` is the canonical first
notion; this file adds the finite-presentation variant and records the local
and structural statements of the chapter.
-/

namespace Formalization.Books.Algebra.Unit151

open Set
open scoped TensorProduct

noncomputable section

universe u v

/-- The finite-presentation version of Mathlib's unramified algebra predicate. -/
class _root_.Algebra.GUnramified (R : Type v) (S : Type u) [CommRing R] [CommRing S]
    [Algebra R S] : Prop where
  formallyUnramified : _root_.Algebra.FormallyUnramified R S := by infer_instance
  finitePresentation : _root_.Algebra.FinitePresentation R S := by infer_instance

attribute [instance] _root_.Algebra.GUnramified.formallyUnramified
  _root_.Algebra.GUnramified.finitePresentation

/-- Unramifiedness on a basic open of the target. -/
def UnramifiedAt
    (R : Type v) (S : Type u) [CommRing R] [CommRing S] [Algebra R S]
    (q : PrimeSpectrum S) : Prop :=
  ∃ g : S, g ∉ q.asIdeal ∧ Algebra.Unramified R (Localization.Away g)

/-- G-unramifiedness on a basic open of the target. -/
def GUnramifiedAt
    (R : Type v) (S : Type u) [CommRing R] [CommRing S] [Algebra R S]
    (q : PrimeSpectrum S) : Prop :=
  ∃ g : S, g ∉ q.asIdeal ∧ Algebra.GUnramified R (Localization.Away g)

/-- Localized Kähler differentials at a prime of the target. -/
abbrev LocalizedDifferentials
    (R : Type v) (S : Type u) [CommRing R] [CommRing S] [Algebra R S]
    (q : PrimeSpectrum S) :=
  LocalizedModule q.asIdeal.primeCompl (KaehlerDifferential R S)

/- The canonical residue-field homomorphism is used below to express the
source's finite separable residue-field extension without introducing a new
field-extension construction. -/
noncomputable def residueFieldMapAt
    {R : Type v} {S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) (p : PrimeSpectrum R) (q : PrimeSpectrum S)
    (hq : PrimeSpectrum.comap f q = p) :
    p.asIdeal.ResidueField →+* q.asIdeal.ResidueField :=
  Ideal.ResidueField.map p.asIdeal q.asIdeal f (by
    simpa [PrimeSpectrum.comap_asIdeal] using
      (congrArg PrimeSpectrum.asIdeal hq).symm)

/-! ## The definition and permanence properties -/

/-- Formal unramifiedness plus finite type is Mathlib's unramified predicate. -/
theorem formallyUnramified_and_finiteType_iff_unramified
    {R : Type v} {S : Type u} [CommRing R] [CommRing S] [Algebra R S] :
    Algebra.FormallyUnramified R S ∧ Algebra.FiniteType R S ↔
      Algebra.Unramified R S := by
  constructor
  · rintro ⟨hformal, hfinite⟩
    exact { formallyUnramified := hformal, finiteType := hfinite }
  · intro h
    exact ⟨h.formallyUnramified, h.finiteType⟩

/-- Formal unramifiedness plus finite presentation is G-unramified. -/
theorem formallyUnramified_and_finitePresentation_iff_gUnramified
    {R : Type v} {S : Type u} [CommRing R] [CommRing S] [Algebra R S] :
    Algebra.FormallyUnramified R S ∧ Algebra.FinitePresentation R S ↔
      Algebra.GUnramified R S := by
  constructor
  · rintro ⟨hformal, hfinite⟩
    exact { formallyUnramified := hformal, finitePresentation := hfinite }
  · intro h
    exact ⟨h.formallyUnramified, h.finitePresentation⟩

/-- Every G-unramified map is unramified. -/
theorem gUnramified_toUnramified
    {R : Type v} {S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.GUnramified R S] : Algebra.Unramified R S := by
  exact { formallyUnramified := inferInstance
          finiteType := inferInstance }

/-- Unramified maps are stable under arbitrary base change. -/
theorem unramified_baseChange
    {R S R' : Type u} [CommRing R] [CommRing S] [CommRing R']
    [Algebra R S] [Algebra R R'] [Algebra.Unramified R S] :
    letI : Algebra R' (R' ⊗[R] S) := Algebra.TensorProduct.leftAlgebra
    Algebra.Unramified R' (R' ⊗[R] S) := by
  infer_instance

/-- G-unramified maps are stable under arbitrary base change. -/
theorem gUnramified_baseChange
    {R S R' : Type u} [CommRing R] [CommRing S] [CommRing R']
    [Algebra R S] [Algebra R R'] [Algebra.GUnramified R S] :
    letI : Algebra R' (R' ⊗[R] S) := Algebra.TensorProduct.leftAlgebra
    Algebra.GUnramified R' (R' ⊗[R] S) := by
  sorry

/-- Unramified maps are stable under composition. -/
theorem unramified_comp
    {R S T : Type u} [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra S T] [Algebra R T] [IsScalarTower R S T]
    [Algebra.Unramified R S] [Algebra.Unramified S T] :
    Algebra.Unramified R T := by
  exact Algebra.Unramified.comp R S T

/-- G-unramified maps are stable under composition. -/
theorem gUnramified_comp
    {R S T : Type u} [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra S T] [Algebra R T] [IsScalarTower R S T]
    [Algebra.GUnramified R S] [Algebra.GUnramified S T] :
    Algebra.GUnramified R T := by
  sorry

/-- A principal localization is both G-unramified and unramified. -/
theorem principalLocalization_gUnramified
    {R : Type u} [CommRing R] (f : R) :
    Algebra.GUnramified R (Localization.Away f) := by
  exact { formallyUnramified := Algebra.FormallyUnramified.of_isLocalization
            (Submonoid.powers f)
          finitePresentation := IsLocalization.Away.finitePresentation f }

theorem principalLocalization_unramified
    {R : Type u} [CommRing R] (f : R) :
    Algebra.Unramified R (Localization.Away f) := by
  exact Algebra.Unramified.of_isLocalization_Away f

/-- A quotient by an ideal is unramified. -/
theorem quotient_unramified
    {R : Type u} [CommRing R] (I : Ideal R) :
    Algebra.Unramified R (R ⧸ I) := by
  exact { formallyUnramified := inferInstance, finiteType := inferInstance }

/-- A quotient by a finitely generated ideal is G-unramified. -/
theorem quotient_gUnramified
    {R : Type u} [CommRing R] (I : Ideal R) (hI : I.FG) :
    Algebra.GUnramified R (R ⧸ I) := by
  exact { formallyUnramified := inferInstance
          finitePresentation := Algebra.FinitePresentation.quotient hI }

/-- Étale maps are both G-unramified and unramified. -/
theorem etale_gUnramified
    {R : Type u} {S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.Etale R S] : Algebra.GUnramified R S := by
  exact { formallyUnramified := inferInstance, finitePresentation := inferInstance }

theorem etale_unramified
    {R : Type u} {S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.Etale R S] : Algebra.Unramified R S := by
  exact { formallyUnramified := inferInstance, finiteType := inferInstance }

/-! ## Differential criteria on basic opens -/

/-- Vanishing after localizing the finite module of differentials gives an
unramified neighborhood. -/
theorem unramifiedAt_of_localizedDifferentials_subsingleton
    {R : Type v} {S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    (hfinite : Algebra.FiniteType R S) (q : PrimeSpectrum S)
    (hΩ : Subsingleton (LocalizedDifferentials R S q)) :
    UnramifiedAt R S q := by
  sorry

theorem gUnramifiedAt_of_localizedDifferentials_subsingleton
    {R : Type v} {S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    (hfinitePresentation : Algebra.FinitePresentation R S) (q : PrimeSpectrum S)
    (hΩ : Subsingleton (LocalizedDifferentials R S q)) :
    GUnramifiedAt R S q := by
  sorry

/-- The residue-field fibre of the differentials at a target prime. -/
abbrev CotangentSpaceAt
    (R : Type v) (S : Type u) [CommRing R] [CommRing S] [Algebra R S]
    (q : PrimeSpectrum S) :=
  KaehlerDifferential R S ⊗[S] q.asIdeal.ResidueField

/- The source's fibre criteria use the canonical base-change identity
`Ω[κ(p) ⊗[R] S / κ(p)] ≅ (κ(p) ⊗[R] S) ⊗[S] Ω[S/R]`. -/
theorem fiber_differentials_baseChange
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    (p : PrimeSpectrum R) :
    letI : Algebra p.asIdeal.ResidueField
        (p.asIdeal.ResidueField ⊗[R] S) := Algebra.TensorProduct.leftAlgebra
    letI : Algebra S (p.asIdeal.ResidueField ⊗[R] S) :=
      Algebra.TensorProduct.rightAlgebra
    Nonempty
      ((p.asIdeal.ResidueField ⊗[R] S) ⊗[S] KaehlerDifferential R S ≃ₗ[
        p.asIdeal.ResidueField ⊗[R] S]
        KaehlerDifferential p.asIdeal.ResidueField
          (p.asIdeal.ResidueField ⊗[R] S)) := by
  let _ : Algebra p.asIdeal.ResidueField
      (p.asIdeal.ResidueField ⊗[R] S) := Algebra.TensorProduct.leftAlgebra
  let _ : Algebra S (p.asIdeal.ResidueField ⊗[R] S) :=
    Algebra.TensorProduct.rightAlgebra
  exact ⟨KaehlerDifferential.tensorKaehlerEquiv
    R p.asIdeal.ResidueField S (p.asIdeal.ResidueField ⊗[R] S)⟩

theorem unramifiedAt_of_cotangentSpace_subsingleton
    {R : Type v} {S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    (hfinite : Algebra.FiniteType R S) (q : PrimeSpectrum S)
    (hΩ : Subsingleton (CotangentSpaceAt R S q)) :
    UnramifiedAt R S q := by
  sorry

theorem gUnramifiedAt_of_cotangentSpace_subsingleton
    {R : Type v} {S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    (hfinitePresentation : Algebra.FinitePresentation R S) (q : PrimeSpectrum S)
    (hΩ : Subsingleton (CotangentSpaceAt R S q)) :
    GUnramifiedAt R S q := by
  sorry

/-! ## Fibre criteria -/

/-- A prime of the fibre over `p` lying below a chosen prime `q`. -/
structure FiberPrime
    {R : Type v} {S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    (p : PrimeSpectrum R) (q : PrimeSpectrum S)
    (hq : PrimeSpectrum.comap (algebraMap R S) q = p) where
  qbar : PrimeSpectrum (p.asIdeal.ResidueField ⊗[R] S)
  comap_eq :
    PrimeSpectrum.comap Algebra.TensorProduct.includeRight.toRingHom qbar = q

/-- The localized Kähler differentials of the fibre at a chosen fibre prime. -/
def FiberLocalizedDifferentials
    {R : Type v} {S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    (p : PrimeSpectrum R) (q : PrimeSpectrum S)
    (hq : PrimeSpectrum.comap (algebraMap R S) q = p)
    (qbar : FiberPrime p q hq) : Prop :=
  letI : Algebra p.asIdeal.ResidueField
      (p.asIdeal.ResidueField ⊗[R] S) := Algebra.TensorProduct.leftAlgebra
  Subsingleton
    (LocalizedModule qbar.qbar.asIdeal.primeCompl
      (KaehlerDifferential p.asIdeal.ResidueField
        (p.asIdeal.ResidueField ⊗[R] S)))

/-- The cotangent space of the fibre at a chosen fibre prime. -/
def FiberCotangentSpace
    {R : Type v} {S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    (p : PrimeSpectrum R) (q : PrimeSpectrum S)
    (hq : PrimeSpectrum.comap (algebraMap R S) q = p)
    (qbar : FiberPrime p q hq) : Type _ :=
  letI : Algebra p.asIdeal.ResidueField
      (p.asIdeal.ResidueField ⊗[R] S) := Algebra.TensorProduct.leftAlgebra
  KaehlerDifferential p.asIdeal.ResidueField
      (p.asIdeal.ResidueField ⊗[R] S) ⊗[
        p.asIdeal.ResidueField ⊗[R] S] qbar.qbar.asIdeal.ResidueField

/-- The prime of the fibre associated to a prime over `p` exists. -/
theorem exists_fiberPrime
    {R : Type v} {S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    (p : PrimeSpectrum R) (q : PrimeSpectrum S)
    (hq : PrimeSpectrum.comap (algebraMap R S) q = p) :
    Nonempty (FiberPrime p q hq) := by
  sorry

theorem unramifiedAt_of_fiber_localizedDifferentials_subsingleton
    {R : Type v} {S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    (hfinite : Algebra.FiniteType R S) (p : PrimeSpectrum R) (q : PrimeSpectrum S)
    (hq : PrimeSpectrum.comap (algebraMap R S) q = p)
    (qbar : FiberPrime p q hq)
    (hΩ : FiberLocalizedDifferentials p q hq qbar) :
    UnramifiedAt R S q := by
  sorry

theorem gUnramifiedAt_of_fiber_localizedDifferentials_subsingleton
    {R : Type v} {S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    (hfinitePresentation : Algebra.FinitePresentation R S)
    (p : PrimeSpectrum R) (q : PrimeSpectrum S)
    (hq : PrimeSpectrum.comap (algebraMap R S) q = p)
    (qbar : FiberPrime p q hq)
    (hΩ : FiberLocalizedDifferentials p q hq qbar) :
    GUnramifiedAt R S q := by
  sorry

theorem unramifiedAt_of_fiber_cotangentSpace_subsingleton
    {R : Type v} {S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    (hfinite : Algebra.FiniteType R S) (p : PrimeSpectrum R) (q : PrimeSpectrum S)
    (hq : PrimeSpectrum.comap (algebraMap R S) q = p)
    (qbar : FiberPrime p q hq)
    (hΩ : Subsingleton (FiberCotangentSpace p q hq qbar)) :
    UnramifiedAt R S q := by
  sorry

theorem gUnramifiedAt_of_fiber_cotangentSpace_subsingleton
    {R : Type v} {S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    (hfinitePresentation : Algebra.FinitePresentation R S)
    (p : PrimeSpectrum R) (q : PrimeSpectrum S)
    (hq : PrimeSpectrum.comap (algebraMap R S) q = p)
    (qbar : FiberPrime p q hq)
    (hΩ : Subsingleton (FiberCotangentSpace p q hq qbar)) :
    GUnramifiedAt R S q := by
  sorry

/-! ## Locality and finite-type approximation -/

theorem unramified_of_basicOpen_cover
    {R : Type u} {S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    (m : ℕ) (g : Fin m → S)
    (hgen : Ideal.span (Set.range g) = (⊤ : Ideal S))
    (hU : ∀ i, Algebra.Unramified R (Localization.Away (g i))) :
    Algebra.Unramified R S := by
  sorry

theorem gUnramified_of_basicOpen_cover
    {R : Type u} {S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    (m : ℕ) (g : Fin m → S)
    (hgen : Ideal.span (Set.range g) = (⊤ : Ideal S))
    (hG : ∀ i, Algebra.GUnramified R (Localization.Away (g i))) :
    Algebra.GUnramified R S := by
  sorry

theorem unramified_of_unramifiedAt_all_primes
    {R : Type u} {S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    (h : ∀ q : PrimeSpectrum S, UnramifiedAt R S q) :
    Algebra.Unramified R S := by
  sorry

theorem gUnramified_of_gUnramifiedAt_all_primes
    {R : Type u} {S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    (h : ∀ q : PrimeSpectrum S, GUnramifiedAt R S q) :
    Algebra.GUnramified R S := by
  sorry

/-! ## Approximation over the integers -/

/-- The finite-type-over-`ℤ` approximation in the G-unramified case. -/
structure GUnramifiedApproximation
    (R : Type u) (S : Type u) [CommRing R] [CommRing S] [Algebra R S] where
  R₀ : Type u
  [commRingR₀ : CommRing R₀]
  S₀ : Type u
  [commRingS₀ : CommRing S₀]
  [algebraIntR₀ : Algebra ℤ R₀]
  [algebraR₀R : Algebra R₀ R]
  [algebraR₀S₀ : Algebra R₀ S₀]
  finiteTypeOverIntegers : Algebra.FiniteType ℤ R₀
  gUnramified : Algebra.GUnramified R₀ S₀
  baseChange :
    letI : Algebra R (R ⊗[R₀] S₀) := Algebra.TensorProduct.leftAlgebra
    Nonempty ((R ⊗[R₀] S₀) ≃ₐ[R] S)

theorem gUnramified_finite_type_approximation
    {R : Type u} {S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.GUnramified R S] :
    Nonempty (GUnramifiedApproximation R S) := by
  sorry

/-- The finite-type-over-`ℤ` approximation in the unramified case. -/
structure UnramifiedApproximation
    (R : Type u) (S : Type u) [CommRing R] [CommRing S] [Algebra R S] where
  R₀ : Type u
  [commRingR₀ : CommRing R₀]
  S₀ : Type u
  [commRingS₀ : CommRing S₀]
  [algebraIntR₀ : Algebra ℤ R₀]
  [algebraR₀R : Algebra R₀ R]
  [algebraR₀S₀ : Algebra R₀ S₀]
  finiteTypeOverIntegers : Algebra.FiniteType ℤ R₀
  unramified : Algebra.Unramified R₀ S₀
  quotientIdeal :
    letI : Algebra R (R ⊗[R₀] S₀) := Algebra.TensorProduct.leftAlgebra
    Ideal (R ⊗[R₀] S₀)
  quotient :
    letI : Algebra R (R ⊗[R₀] S₀) := Algebra.TensorProduct.leftAlgebra
    Nonempty (((R ⊗[R₀] S₀) ⧸ quotientIdeal) ≃ₐ[R] S)

theorem unramified_finite_type_approximation
    {R : Type u} {S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.Unramified R S] :
    Nonempty (UnramifiedApproximation R S) := by
  sorry

/-! ## The diagonal -/

/-- Data expressing that the diagonal of an unramified algebra is open and
closed in the tensor square. -/
structure DiagonalUnramifiedData
    (R : Type u) (S : Type u) [CommRing R] [CommRing S] [Algebra R S] where
  e : S ⊗[R] S
  idempotent : IsIdempotentElem e
  equivalence : S ≃ₐ[S] Localization.Away e
  map_commutes :
      equivalence.toRingHom.comp (Algebra.TensorProduct.lmul'' R).toRingHom =
      algebraMap (S ⊗[R] S) (Localization.Away e)

theorem diagonal_unramified
    {R : Type u} {S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.Unramified R S] :
    Nonempty (DiagonalUnramifiedData R S) := by
  sorry

/-! ## Prime-local structure and quasi-finiteness -/

theorem unramifiedAt_prime_structure
    {R : Type v} {S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    (p : PrimeSpectrum R) (q : PrimeSpectrum S)
    (hq : PrimeSpectrum.comap (algebraMap R S) q = p)
    (h : UnramifiedAt R S q) :
    p.asIdeal.map (algebraMap R (Localization.AtPrime q.asIdeal)) =
        q.asIdeal.map (algebraMap S (Localization.AtPrime q.asIdeal)) ∧
      q.asIdeal.map (algebraMap S (Localization.AtPrime q.asIdeal)) =
        IsLocalRing.maximalIdeal (Localization.AtPrime q.asIdeal) ∧
      letI : Algebra p.asIdeal.ResidueField q.asIdeal.ResidueField :=
        (residueFieldMapAt
          (algebraMap R S) p q hq).toAlgebra
      Module.Finite p.asIdeal.ResidueField q.asIdeal.ResidueField ∧
        Algebra.IsSeparable p.asIdeal.ResidueField q.asIdeal.ResidueField := by
  sorry

theorem unramifiedAt_quasiFiniteAt
    {R : Type v} {S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    (hfinite : Algebra.FiniteType R S) (q : PrimeSpectrum S)
    (h : UnramifiedAt R S q) :
    RingHom.QuasiFiniteAt (algebraMap R S) q.asIdeal := by
  sorry

theorem unramified_quasiFinite
    {R : Type u} {S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.Unramified R S] :
    RingHom.QuasiFinite (algebraMap R S) := by
  sorry

/-- The local converse: finite type, a fibre which is a field at `q`, and a
finite separable residue-field extension imply unramifiedness at `q`. -/
theorem characterize_unramifiedAt
    {R : Type v} {S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    (p : PrimeSpectrum R) (q : PrimeSpectrum S)
    (hq : PrimeSpectrum.comap (algebraMap R S) q = p)
    (hfinite : Algebra.FiniteType R S)
    (hmax : p.asIdeal.map (algebraMap R (Localization.AtPrime q.asIdeal)) =
      IsLocalRing.maximalIdeal (Localization.AtPrime q.asIdeal))
    (hsep :
      letI : Algebra p.asIdeal.ResidueField q.asIdeal.ResidueField :=
        (residueFieldMapAt
          (algebraMap R S) p q hq).toAlgebra
      Module.Finite p.asIdeal.ResidueField q.asIdeal.ResidueField ∧
        Algebra.IsSeparable p.asIdeal.ResidueField q.asIdeal.ResidueField) :
    UnramifiedAt R S q := by
  sorry

/-! ## Étale characterizations -/

theorem etale_iff_flat_and_gUnramified
    {R : Type u} {S : Type u} [CommRing R] [CommRing S] [Algebra R S] :
    List.TFAE [
      Algebra.Etale R S,
      RingHom.Flat (algebraMap R S) ∧ Algebra.GUnramified R S,
      RingHom.Flat (algebraMap R S) ∧ Algebra.Unramified R S ∧
        Algebra.FinitePresentation R S] := by
  sorry

/-! ## Polynomial-ring criterion -/

/-- The differentials of the coordinate images generate the module of
Kähler differentials. -/
def PolynomialDifferentialsGenerate
    {k A : Type u} [Field k] [CommRing A]
    (n : ℕ) (φ : MvPolynomial (Fin n) k →+* A) : Prop :=
  letI : Algebra k A :=
    (φ.comp (algebraMap k (MvPolynomial (Fin n) k))).toAlgebra
  Submodule.span A (Set.range (fun i : Fin n =>
    KaehlerDifferential.D k A (φ (MvPolynomial.X i)))) = ⊤

theorem etale_polynomial_iff
    {k A : Type u} [Field k] [CommRing A]
    (n : ℕ) (φ : MvPolynomial (Fin n) k →+* A)
    (hfinite : RingHom.FiniteType φ) :
    RingHom.Etale φ ↔
      (∀ m : MaximalSpectrum A,
        ringKrullDim (Localization.AtPrime m.asIdeal) = n) ∧
      PolynomialDifferentialsGenerate n φ := by
  sorry

end

end Formalization.Books.Algebra.Unit151
