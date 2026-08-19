import Formalization.Books.Smoothing.Unit07
import Formalization.Books.Smoothing.Unit03.Presentations
import Mathlib.Algebra.Algebra.Prod
import Mathlib.RingTheory.FinitePresentation
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Localization.Basic
import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.RingTheory.RingHom.Smooth

/-!
# Smoothing Ring Maps, Chapter 8: warmup and reduction to a base field

This file records the global situation, the filtered-colimit predicate, the
product and delocalization lemmas, and the reduction-to-a-field theorem. The
filtered-colimit predicate and the standard-element predicates are reused
from the preceding smoothing chapters.
-/

namespace Formalization.Books.Smoothing.Unit08

open Formalization.Books.Smoothing.Unit02
open Formalization.Books.Smoothing.Unit07
open scoped TensorProduct

noncomputable section

universe u v

/-! ## The global situation -/

/- The Mathlib geometric-regularity predicate is specialized to noetherian
   algebras. Fibers of a regular map are used here before a noetherian
   instance for each particular fiber has been constructed, so this is the
   equivalent finite-type-field-extension formulation used by the source. -/

/-- Geometric regularity of an algebra, tested after finite-type field
extensions. -/
def GeometricallyRegularAlgebra
    (k : Type u) (A : Type v) [Field k] [CommRing A] [Algebra k A] : Prop :=
  ∀ (K : Type u) [Field K] [Algebra k K] [Algebra.FiniteType k K],
    IsRegularRing (K ⊗[k] A)

/-- A regular ring map: it is flat and all of its fibers are geometrically
regular over the corresponding residue fields. -/
def IsRegularRingMap
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] (f : R →+* S) : Prop :=
  RingHom.Flat f ∧
    ∀ p : PrimeSpectrum R,
      letI : Algebra R S := f.toAlgebra
      let F := p.asIdeal.Fiber S
      letI : Algebra p.asIdeal.ResidueField F :=
        Algebra.TensorProduct.leftAlgebra
      GeometricallyRegularAlgebra p.asIdeal.ResidueField F

/-- The source's global situation: a regular map between noetherian rings. -/
structure RegularRingMapSituation
    (R S : Type u) [CommRing R] [CommRing S] [Algebra R S] : Prop where
  base_noetherian : IsNoetherianRing R
  target_noetherian : IsNoetherianRing S
  regular : IsRegularRingMap (algebraMap R S)

/-! ## PT and products -/

/-- PT holds for `R → S` when `S` is a filtered colimit of smooth
`R`-algebras. This is the established filtered-algebra-colimit package from
the earlier presentation chapter. -/
abbrev PT
    {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S) : Prop :=
  Formalization.Books.Smoothing.Unit03.IsFilteredColimitOfSmooth f

/-- A product of two situations satisfying PT again satisfies PT. -/
theorem pt_product
    {R₁ S₁ R₂ S₂ : Type u}
    [CommRing R₁] [CommRing S₁] [Algebra R₁ S₁]
    [CommRing R₂] [CommRing S₂] [Algebra R₂ S₂]
    (s₁ : RegularRingMapSituation R₁ S₁)
    (s₂ : RegularRingMapSituation R₂ S₂)
    (h₁ : PT (algebraMap R₁ S₁))
    (h₂ : PT (algebraMap R₂ S₂)) :
  PT (RingHom.prodMap (algebraMap R₁ S₁) (algebraMap R₂ S₂)) := by
  sorry

/-! ## Delocalizing a smooth factorization -/

/- The two maps below are the canonical maps induced by localizing the base
   and an algebra map. They make the localization diagram in the source
   explicit rather than introducing a second localization API. -/

/-- The map from the localization of `R` to the localization of an `R`-
algebra at the image of a multiplicative set. -/
noncomputable def localizationBaseChangeMap
    {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
    (S : Submonoid R) :
    Localization S →+* Localization (S.map (algebraMap R A)) :=
  IsLocalization.map (Q := Localization (S.map (algebraMap R A)))
    (R := R) (P := A) (M := S) (T := S.map (algebraMap R A))
    (algebraMap R A) (by
    intro r hr
    exact (Submonoid.mem_map).2 ⟨r, hr, rfl⟩)

/-- The map between the two localizations induced by an `R`-algebra map. -/
noncomputable def localizedAlgebraMap
    {R A S : Type u} [CommRing R] [CommRing A] [CommRing S]
    [Algebra R A] [Algebra R S] (M : Submonoid R) (f : A →ₐ[R] S) :
    Localization (M.map (algebraMap R A)) →+*
      Localization (M.map (algebraMap R S)) :=
  IsLocalization.map (Q := Localization (M.map (algebraMap R S)))
    (R := A) (P := S) (M := M.map (algebraMap R A))
    (T := M.map (algebraMap R S)) f.toRingHom (by
    intro x hx
    rcases (Submonoid.mem_map).1 hx with ⟨r, hr, hrx⟩
    apply (Submonoid.mem_map).2
    refine ⟨r, hr, ?_⟩
    rw [← hrx]
    exact (f.commutes r).symm)

/-- A factorization after localizing `R`, with the smoothness hypothesis on
the middle algebra and the commutative localization diagram. -/
structure LocalizedSmoothFactorization
    {R A S : Type u} [CommRing R] [CommRing A] [CommRing S]
    [Algebra R A] [Algebra R S]
    (M : Submonoid R) (f : A →ₐ[R] S) where
  B' : Type u
  [commRingB' : CommRing B']
  [localizedBaseAlgebra : Algebra (Localization M) B']
  localizedA : Localization (M.map (algebraMap R A)) →+* B'
  localizedS : B' →+* Localization (M.map (algebraMap R S))
  factorization :
    localizedS.comp localizedA = localizedAlgebraMap M f
  smooth : RingHom.Smooth (algebraMap (Localization M) B')

/-- An ordinary `R`-algebra factorization `A → B → S`. -/
structure RingMapFactorization
    {R A S : Type u} [CommRing R] [CommRing A] [CommRing S]
    [Algebra R A] [Algebra R S] (f : A →ₐ[R] S) where
  B : Type u
  [commRingB : CommRing B]
  [algebraB : Algebra R B]
  AtoB : A →ₐ[R] B
  BtoS : B →ₐ[R] S
  factorization : BtoS.comp AtoB = f

/-- The delocalization lemma: a smooth localized factorization can be
delocalized so that an element of the original multiplicative set is
elementary standard in the middle algebra. -/
theorem pt_delocalize_base
    {R A S : Type u} [CommRing R] [CommRing A] [CommRing S]
    [Algebra R A] [Algebra R S] [Algebra.FinitePresentation R A]
    (M : Submonoid R) (f : A →ₐ[R] S)
    (h : LocalizedSmoothFactorization M f) :
    ∃ d : RingMapFactorization f,
      letI : CommRing d.B := d.commRingB
      letI : Algebra R d.B := d.algebraB
      ∃ r : R, r ∈ M ∧
        IsElementaryStandard R d.B (algebraMap R d.B r) := by
  sorry

/-! ## Reduction to a field -/

/-- The quotient map of a ring map by an ideal and its extended ideal. -/
def quotientMapOfRingHom
    {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) (I : Ideal R) :
    R ⧸ I →+* S ⧸ Ideal.map f I :=
  Ideal.quotientMap (Ideal.map f I) f Ideal.le_comap_map

/-- Regularity is preserved by the quotient base change used in the proof of
the reduction lemma. -/
theorem quotientMapOfRingHom_isRegular
    {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) (hf : IsRegularRingMap f) (I : Ideal R) :
    IsRegularRingMap (quotientMapOfRingHom f I) := by
  sorry

/-- A smooth factorization modulo `πⁿ`, including the finite-presentation and
smoothness properties of the middle algebra. This is the exact quotient
factorization used before the lifting and desingularization lemmas. -/
def HasSmoothPowerQuotientFactorization
    {R A S : Type u} [CommRing R] [CommRing A] [CommRing S]
    [Algebra R A] [Algebra R S]
    (π : R) (n : ℕ) (f : A →ₐ[R] S) : Prop :=
  ∃ (C : Type u) (hC : CommRing C)
    (hBase : Algebra (powerQuotient R π n) C),
    letI : CommRing C := hC
    letI : Algebra (powerQuotient R π n) C := hBase
    ∃ (_hfp : Algebra.FinitePresentation (powerQuotient R π n) C)
      (_hsmooth : RingHom.Smooth
        (algebraMap (powerQuotient R π n) C)),
      Nonempty
        (DesingularizationModPowerFactorization (C := C) (Λ := S) π f n)

/-- PT for the quotient base supplies the smooth factorization modulo the
eighth power used in the reduction proof. -/
theorem exists_smoothPowerQuotientFactorization_of_pt
    {R A S : Type u} [CommRing R] [CommRing A] [CommRing S]
    [Algebra R A] [Algebra R S] [Algebra.FinitePresentation R A]
    (π : R) (f : A →ₐ[R] S)
    (hpt : PT (powerQuotientAlgebraMap (R := R) (A := S) π 8)) :
    HasSmoothPowerQuotientFactorization π 8 f := by
  sorry

/-- If PT holds for every global situation whose base is a field, then PT
holds for every global situation. -/
theorem pt_reduce_to_field
    (hfield :
      ∀ {R S : Type u} [Field R] [CommRing S] [Algebra R S],
        RegularRingMapSituation R S → PT (algebraMap R S)) :
    ∀ {R S : Type u} [CommRing R] [CommRing S] [Algebra R S],
      RegularRingMapSituation R S → PT (algebraMap R S) := by
  sorry

end
end Formalization.Books.Smoothing.Unit08
