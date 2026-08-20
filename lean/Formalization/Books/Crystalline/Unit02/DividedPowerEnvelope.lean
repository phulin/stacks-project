import Formalization.Books.Dpa.Unit04.ExtendingDividedPowers
import Formalization.Books.Dpa.Unit05.DividedPowerPolynomialAlgebras
import Formalization.Books.Algebra.Unit75.TorGroups
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.RingTheory.Ideal.Quotient.Basic
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.RingHom.Flat
import Mathlib.RingTheory.TensorProduct.Basic

/-!
# Crystalline Cohomology, Chapter 2: Divided power envelope

The divided-power operations and polynomial rings below reuse the canonical
interfaces from the preceding divided-power-algebra chapters.
-/

namespace Formalization.Books.Crystalline.Unit02

open CategoryTheory CategoryTheory.Limits
open Formalization.Books.Algebra.Unit75
open Formalization.Books.Dpa.Unit03
open Formalization.Books.Dpa.Unit03.DividedPowerRing
open Formalization.Books.Dpa.Unit04
open Formalization.Books.Dpa.Unit05
open scoped TensorProduct

universe u
noncomputable section

/-- A map of pairs over a divided-power base. -/
structure EnvelopePairHom (A : DividedPowerRing.{u})
    {B : Type u} [CommRing B] (f : (A : Type u) →+* B) (J : Ideal B)
    (C : DividedPowerRing.{u}) (aC : DividedPowerRing.Hom A C) where
  hom : B →+* (C : Type u)
  commutes : ∀ x : A, hom (f x) = aC.hom x
  ideal_map : ∀ {x : B}, x ∈ J → hom x ∈ C.ideal

/-- A divided-power map over the same divided-power base. -/
structure EnvelopeDPMorphism (A : DividedPowerRing.{u})
    (D C : DividedPowerRing.{u}) (base : DividedPowerRing.Hom A D)
    (aC : DividedPowerRing.Hom A C) where
  hom : DividedPowerRing.Hom D C
  commutes : ∀ x : A, hom.hom (base.hom x) = aC.hom x

/-- The universal-property equivalence, expressed at every target. -/
def EnvelopeHomEquiv (A : DividedPowerRing.{u})
    {B : Type u} [CommRing B] (f : (A : Type u) →+* B) (J : Ideal B)
    (D : DividedPowerRing.{u}) (base : DividedPowerRing.Hom A D) : Prop :=
  ∀ (C : DividedPowerRing.{u}) (aC : DividedPowerRing.Hom A C),
    Nonempty
      (EnvelopeDPMorphism A D C base aC ≃ EnvelopePairHom A f J C aC)

/-- A divided-power envelope with the maps and universal property in the
source lemma. -/
structure DividedPowerEnvelope (A : DividedPowerRing.{u})
    {B : Type u} [CommRing B] (f : (A : Type u) →+* B) (J : Ideal B)
    (hIJ : Ideal.map f A.ideal ≤ J) where
  D : DividedPowerRing.{u}
  base : DividedPowerRing.Hom A D
  toD : B →+* (D : Type u)
  toD_base : ∀ x : A, toD (f x) = base.hom x
  toD_ideal : ∀ {x : B}, x ∈ J → toD x ∈ D.ideal
  quotient : (D : Type u) →+* (B ⧸ J)
  quotient_comp : ∀ x : B, quotient (toD x) = Ideal.Quotient.mk J x
  kernel_eq : RingHom.ker quotient = D.ideal
  universal : EnvelopeHomEquiv A f J D base

/-- Existence of the divided-power envelope. -/
theorem exists_dividedPowerEnvelope
    (A : DividedPowerRing.{u}) {B : Type u} [CommRing B]
    (f : (A : Type u) →+* B) (J : Ideal B)
    (hIJ : Ideal.map f A.ideal ≤ J) :
    Nonempty (DividedPowerEnvelope A f J hIJ) := by
  sorry

/-- The chosen divided-power envelope. -/
noncomputable def dividedPowerEnvelope
    (A : DividedPowerRing.{u}) {B : Type u} [CommRing B]
    (f : (A : Type u) →+* B) (J : Ideal B)
    (hIJ : Ideal.map f A.ideal ≤ J) : DividedPowerEnvelope A f J hIJ :=
  Classical.choice (exists_dividedPowerEnvelope A f J hIJ)

theorem dividedPowerEnvelope_universal
    {A : DividedPowerRing.{u}} {B : Type u} [CommRing B]
    {f : (A : Type u) →+* B} {J : Ideal B}
    {hIJ : Ideal.map f A.ideal ≤ J}
    (E : DividedPowerEnvelope A f J hIJ) :
    EnvelopeHomEquiv A f J E.D E.base := by
  exact E.universal

/-- The positive divided powers of the image of the envelope ideal. -/
def envelopePositiveDpowGenerators
    {A : DividedPowerRing.{u}} {B : Type u} [CommRing B]
    {f : (A : Type u) →+* B} {J : Ideal B}
    {hIJ : Ideal.map f A.ideal ≤ J}
    (E : DividedPowerEnvelope A f J hIJ) : Set (E.D : Type u) :=
  {y | ∃ n : ℕ, n ≠ 0 ∧ ∃ x : B, x ∈ J ∧
    y = E.D.dividedPowers.dpow n (E.toD x)}

theorem dividedPowerEnvelope_map_ideal
    {A : DividedPowerRing.{u}} {B : Type u} [CommRing B]
    {f : (A : Type u) →+* B} {J : Ideal B}
    {hIJ : Ideal.map f A.ideal ≤ J}
    (E : DividedPowerEnvelope A f J hIJ) :
    ∀ {x : B}, x ∈ J → E.toD x ∈ E.D.ideal :=
  E.toD_ideal

theorem dividedPowerEnvelope_quotient_kernel
    {A : DividedPowerRing.{u}} {B : Type u} [CommRing B]
    {f : (A : Type u) →+* B} {J : Ideal B}
    {hIJ : Ideal.map f A.ideal ≤ J}
    (E : DividedPowerEnvelope A f J hIJ) :
    RingHom.ker E.quotient = E.D.ideal :=
  E.kernel_eq

/-- The positive divided powers generate the divided-power ideal. -/
theorem dividedPowerEnvelope_ideal_generated
    {A : DividedPowerRing.{u}} {B : Type u} [CommRing B]
    {f : (A : Type u) →+* B} {J : Ideal B}
    {hIJ : Ideal.map f A.ideal ≤ J}
    (E : DividedPowerEnvelope A f J hIJ) :
    E.D.ideal = Ideal.span (envelopePositiveDpowGenerators E) := by
  sorry

/-- The positive divided powers generate the envelope as a B-algebra. -/
def dividedPowerEnvelope_algebra_generated
    {A : DividedPowerRing.{u}} {B : Type u} [CommRing B]
    {f : (A : Type u) →+* B} {J : Ideal B}
    {hIJ : Ideal.map f A.ideal ≤ J}
    (E : DividedPowerEnvelope A f J hIJ) : Prop :=
  letI : Algebra B (E.D : Type u) := E.toD.toAlgebra
  Algebra.adjoin B (envelopePositiveDpowGenerators E) = ⊤

theorem dividedPowerEnvelope_generates_as_algebra
    {A : DividedPowerRing.{u}} {B : Type u} [CommRing B]
    {f : (A : Type u) →+* B} {J : Ideal B}
    {hIJ : Ideal.map f A.ideal ≤ J}
    (E : DividedPowerEnvelope A f J hIJ) :
    dividedPowerEnvelope_algebra_generated E := by
  sorry

/-- An equivalence retaining divided-power maps. -/
structure DividedPowerRingEquiv (P Q : DividedPowerRing.{u}) where
  hom : DividedPowerRing.Hom P Q
  inv : DividedPowerRing.Hom Q P
  hom_inv_id : ∀ x : P, inv.hom (hom.hom x) = x
  inv_hom_id : ∀ x : Q, hom.hom (inv.hom x) = x

/-- The inverse image of an ideal along a ring map. -/
def envelopeIdealPreimage {B B' : Type u} [CommRing B] [CommRing B']
    (φ : B' →+* B) (J : Ideal B) : Ideal B' :=
  Ideal.comap φ J

/-- The ideal generated by positive divided powers of the kernel image. -/
def envelopeQuotientKernelIdeal
    {A : DividedPowerRing.{u}} {B : Type u} [CommRing B]
    {f : (A : Type u) →+* B}
    {J : Ideal B} {hIJ : Ideal.map f A.ideal ≤ J}
    (E : DividedPowerEnvelope A f J hIJ)
    (K : Ideal B) (_hK : K ≤ J) : Ideal (E.D : Type u) :=
  Ideal.span
    {y | ∃ n : ℕ, n ≠ 0 ∧ ∃ k : B, k ∈ K ∧
      y = E.D.dividedPowers.dpow n (E.toD k)}

/-- The quotient divided-power ring using Mathlib's quotient divided powers. -/
noncomputable def envelopeQuotientRing
    {A : DividedPowerRing.{u}} {B : Type u} [CommRing B]
    {f : (A : Type u) →+* B}
    {J : Ideal B} {hIJ : Ideal.map f A.ideal ≤ J}
    (E : DividedPowerEnvelope A f J hIJ)
    (K : Ideal B) (hK : K ≤ J)
    (hsub : E.D.dividedPowers.IsSubDPIdeal
      (envelopeQuotientKernelIdeal E K hK ⊓ E.D.ideal)) :
    DividedPowerRing.{u} :=
  { toCommRing := CommRingCat.of
      ((E.D : Type u) ⧸ envelopeQuotientKernelIdeal E K hK)
    ideal := Ideal.map
      (Ideal.Quotient.mk (envelopeQuotientKernelIdeal E K hK)) E.D.ideal
    dividedPowers := DividedPowers.Quotient.dividedPowers
      E.D.dividedPowers hsub }

/-- Proof-carrying data for the quotient divided-power ring in the quotient
lemma. -/
structure EnvelopeQuotientRingData
    {A : DividedPowerRing.{u}} {B : Type u} [CommRing B]
    {f : (A : Type u) →+* B}
    {J : Ideal B} {hIJ : Ideal.map f A.ideal ≤ J}
    (E : DividedPowerEnvelope A f J hIJ)
    (K : Ideal B) (hK : K ≤ J) where
  hsub : E.D.dividedPowers.IsSubDPIdeal
    (envelopeQuotientKernelIdeal E K hK ⊓ E.D.ideal)

noncomputable def EnvelopeQuotientRingData.quotient
    {A : DividedPowerRing.{u}} {B : Type u} [CommRing B]
    {f : (A : Type u) →+* B}
    {J : Ideal B} {hIJ : Ideal.map f A.ideal ≤ J}
    {E : DividedPowerEnvelope A f J hIJ}
    {K : Ideal B} {hK : K ≤ J}
    (Q : EnvelopeQuotientRingData E K hK) : DividedPowerRing.{u} :=
  envelopeQuotientRing E K hK Q.hsub

theorem kernel_le_preimage_ideal
    {B B' : Type u} [CommRing B] [CommRing B']
    (φ : B' →+* B) (J : Ideal B) :
    RingHom.ker φ ≤ envelopeIdealPreimage φ J := by
  intro x hx
  rw [envelopeIdealPreimage, Ideal.mem_comap]
  rw [RingHom.mem_ker] at hx
  simp [hx]

/-- The base ideal in B is carried into the inverse image ideal in B'. -/
theorem preimage_base_ideal_le
    (A : DividedPowerRing.{u}) {B B' : Type u}
    [CommRing B] [CommRing B'] (f : (A : Type u) →+* B)
    (f' : (A : Type u) →+* B') (φ : B' →+* B) (J : Ideal B)
    (hIJ : Ideal.map f A.ideal ≤ J)
    (hcompat : ∀ x : A, φ (f' x) = f x) :
    Ideal.map f' A.ideal ≤ envelopeIdealPreimage φ J := by
  sorry

noncomputable def preimageEnvelope
    (A : DividedPowerRing.{u}) {B B' : Type u}
    [CommRing B] [CommRing B'] (f : (A : Type u) →+* B)
    (f' : (A : Type u) →+* B') (φ : B' →+* B) (J : Ideal B)
    (hIJ : Ideal.map f A.ideal ≤ J)
    (hcompat : ∀ x : A, φ (f' x) = f x) :
    DividedPowerEnvelope A f'
      (envelopeIdealPreimage φ J)
      (preimage_base_ideal_le A f f' φ J hIJ hcompat) :=
  dividedPowerEnvelope A f'
    (envelopeIdealPreimage φ J)
    (preimage_base_ideal_le A f f' φ J hIJ hcompat)

/-- The quotient theorem with the quotient divided-power ring exposed
explicitly through EnvelopeQuotientRingData. -/
theorem dividedPowerEnvelope_quotient
    (A : DividedPowerRing.{u})
    {B B' : Type u} [CommRing B] [CommRing B']
    (f : (A : Type u) →+* B) (f' : (A : Type u) →+* B')
    (φ : B' →+* B) (hcompat : ∀ x : A, φ (f' x) = f x)
    (J : Ideal B) (hIJ : Ideal.map f A.ideal ≤ J)
    (hIJ' : Ideal.map f' A.ideal ≤ envelopeIdealPreimage φ J)
    (E' : DividedPowerEnvelope A f' (envelopeIdealPreimage φ J) hIJ')
    (hφ : Function.Surjective φ) :
    ∃ Q : EnvelopeQuotientRingData E' (RingHom.ker φ)
      (by exact (kernel_le_preimage_ideal φ J)),
      Nonempty (DividedPowerRingEquiv
        (dividedPowerEnvelope A f J hIJ).D Q.quotient) := by
  sorry

/-- Canonical divided powers on the infinitely generated polynomial algebra. -/
noncomputable def canonicalPolynomialDividedPowers
    (B : DividedPowerRing.{u}) (T : Type u) :
    DividedPowers
      (infiniteDividedPowerPolynomialIdeal (B : Type u) B.ideal T) :=
  Classical.choose
    (exists_unique_infiniteDividedPowerPolynomialDividedPowers B T)

theorem canonicalPolynomialDividedPowers_isStructure
    (B : DividedPowerRing.{u}) (T : Type u) :
    IsInfiniteDividedPowerPolynomialStructure B T
      (canonicalPolynomialDividedPowers B T) := by
  exact (Classical.choose_spec
    (exists_unique_infiniteDividedPowerPolynomialDividedPowers B T)).1

noncomputable def canonicalPolynomialRing
    (B : DividedPowerRing.{u}) (T : Type u) : DividedPowerRing.{u} :=
  infiniteDividedPowerPolynomialRing B T
    (canonicalPolynomialDividedPowers B T)

/-- The relation generators in the polynomial presentation. -/
def polynomialEnvelopeRelationGenerators
    (B : DividedPowerRing.{u}) (T : Type u) (f : T → (B : Type u))
    (δ : DividedPowers
      (infiniteDividedPowerPolynomialIdeal (B : Type u) B.ideal T)) :
    Set (infiniteDividedPowerPolynomialAlgebra (B : Type u) T) :=
  {y | ∃ n : ℕ, n ≠ 0 ∧ ∃ (r : T →₀ (B : Type u)) (r₀ : B),
    r₀ ∈ B.ideal ∧ r.sum (fun t rt => rt * f t) = r₀ ∧
    y = δ.dpow n
      (r.sum (fun t rt =>
        algebraMap (B : Type u)
          (infiniteDividedPowerPolynomialAlgebra (B : Type u) T) rt *
        infiniteDividedPowerVariable T t 1) -
        algebraMap (B : Type u)
          (infiniteDividedPowerPolynomialAlgebra (B : Type u) T) r₀)}

def polynomialEnvelopeKernelIdeal
    (B : DividedPowerRing.{u}) (T : Type u) (f : T → (B : Type u))
    (δ : DividedPowers
      (infiniteDividedPowerPolynomialIdeal (B : Type u) B.ideal T)) :
    Ideal (infiniteDividedPowerPolynomialAlgebra (B : Type u) T) :=
  Ideal.span
    (Set.range (fun t =>
      infiniteDividedPowerVariable T t 1 -
        algebraMap (B : Type u)
          (infiniteDividedPowerPolynomialAlgebra (B : Type u) T) (f t)) ∪
      polynomialEnvelopeRelationGenerators B T f δ)

/-- The envelope for a pair over a divided-power ring, using the identity map. -/
noncomputable def identityEnvelope
    (B : DividedPowerRing.{u}) (J : Ideal (B : Type u))
    (hIJ : B.ideal ≤ J) :
    DividedPowerEnvelope B (RingHom.id (B : Type u)) J (by simpa using hIJ) :=
  dividedPowerEnvelope B (RingHom.id (B : Type u)) J (by simpa using hIJ)

/-- The presentation by divided-power polynomial variables. -/
theorem describe_dividedPowerEnvelope
    (B : DividedPowerRing.{u}) (J : Ideal (B : Type u))
    (hIJ : B.ideal ≤ J) (T : Type u) (f : T → (B : Type u))
    (hgen : J = B.ideal ⊔ Ideal.span (Set.range f)) :
    ∃ h : DividedPowerRing.Hom (canonicalPolynomialRing B T)
        (identityEnvelope B J hIJ).D,
      Function.Surjective h.hom ∧
      (∀ t, h.hom (infiniteDividedPowerVariable T t 1) =
        (identityEnvelope B J hIJ).toD (f t)) ∧
      (∀ x : B, h.hom
          (algebraMap (B : Type u)
            (infiniteDividedPowerPolynomialAlgebra (B : Type u) T) x) =
        (identityEnvelope B J hIJ).base.hom x) ∧
      RingHom.ker h.hom =
        polynomialEnvelopeKernelIdeal B T f
          (canonicalPolynomialDividedPowers B T) := by
  sorry

/-- The ideal JB[x] + (x) in the ordinary multivariable polynomial ring. -/
def polynomialExtensionIdeal {B : Type u} [CommRing B]
    (J : Ideal B) (T : Type u) : Ideal (MvPolynomial T B) :=
  Ideal.map (algebraMap B (MvPolynomial T B)) J ⊔
    Ideal.span (Set.range (MvPolynomial.X : T → MvPolynomial T B))

def polynomialExtensionMap {A : DividedPowerRing.{u}}
    {B : Type u} [CommRing B] (f : (A : Type u) →+* B) (T : Type u) :
    (A : Type u) →+* MvPolynomial T B :=
  (algebraMap B (MvPolynomial T B)).comp f

theorem polynomialExtensionBaseIdeal_le
    (A : DividedPowerRing.{u}) {B : Type u} [CommRing B]
    (f : (A : Type u) →+* B) (J : Ideal B)
    (hIJ : Ideal.map f A.ideal ≤ J) (T : Type u) :
    Ideal.map (polynomialExtensionMap f T) A.ideal ≤
      polynomialExtensionIdeal J T := by
  sorry

/-- Adding variables commutes with taking the divided-power envelope. -/
theorem dividedPowerEnvelope_add_variables
    (A : DividedPowerRing.{u}) {B : Type u} [CommRing B]
    (f : (A : Type u) →+* B) (J : Ideal B)
    (hIJ : Ideal.map f A.ideal ≤ J) (T : Type u) :
    Nonempty (DividedPowerRingEquiv
      (dividedPowerEnvelope A (polynomialExtensionMap f T)
        (polynomialExtensionIdeal J T)
        (polynomialExtensionBaseIdeal_le A f J hIJ T)).D
      (canonicalPolynomialRing
        (dividedPowerEnvelope A f J hIJ).D T)) := by
  sorry

/-- The ideal extended from the base along an algebra map. -/
def envelopeBaseIdeal (A : DividedPowerRing.{u})
    {B : Type u} [CommRing B] (f : (A : Type u) →+* B) : Ideal B :=
  Ideal.map f A.ideal

def quotientBaseChangeMap {R S : Type u} [CommRing R] [CommRing S]
    (g : R →+* S) (I : Ideal R) (I' : Ideal S)
    (hI : Ideal.map g I ≤ I') : R ⧸ I →+* S ⧸ I' :=
  Ideal.Quotient.lift I ((Ideal.Quotient.mk I').comp g) (by
    intro x hx
    exact Ideal.Quotient.eq_zero_iff_mem.mpr
      (hI (Ideal.mem_map_of_mem g hx)))

theorem envelopeBaseIdeal_map_le
    (A : DividedPowerRing.{u}) {B B' : Type u}
    [CommRing B] [CommRing B'] (f : (A : Type u) →+* B)
    (g : B →+* B') :
    Ideal.map g (envelopeBaseIdeal A f) ≤
      envelopeBaseIdeal A (g.comp f) := by
  sorry

noncomputable def envelopeTensorBaseChangeRing
    {A : DividedPowerRing.{u}} {B B' : Type u}
    [CommRing B] [CommRing B']
    {f : (A : Type u) →+* B} {J : Ideal B}
    {hIJ : Ideal.map f A.ideal ≤ J}
    (E : DividedPowerEnvelope A f J hIJ) (g : B →+* B') : CommRingCat.{u} :=
  letI : Algebra B (E.D : Type u) := E.toD.toAlgebra
  letI : Algebra B B' := g.toAlgebra
  CommRingCat.of (TensorProduct B (E.D : Type u) B')

theorem baseChanged_base_ideal_le
    (A : DividedPowerRing.{u}) {B B' : Type u}
    [CommRing B] [CommRing B'] (f : (A : Type u) →+* B)
    (g : B →+* B') (J : Ideal B)
    (hIJ : envelopeBaseIdeal A f ≤ J) :
    Ideal.map (g.comp f) A.ideal ≤ Ideal.map g J := by
  sorry

noncomputable def baseChangedEnvelope
    (A : DividedPowerRing.{u}) {B B' : Type u}
    [CommRing B] [CommRing B'] (f : (A : Type u) →+* B)
    (g : B →+* B') (J : Ideal B)
    (hIJ : envelopeBaseIdeal A f ≤ J) :
    DividedPowerEnvelope A (g.comp f) (Ideal.map g J)
      (baseChanged_base_ideal_le A f g J hIJ) :=
  dividedPowerEnvelope A (g.comp f) (Ideal.map g J)
    (baseChanged_base_ideal_le A f g J hIJ)

def envelopeTorOneVanishing
    {B B' : Type u} [CommRing B] [CommRing B']
    (g : B →+* B') (I : Ideal B) : Prop :=
  IsZero
    (Formalization.Books.Algebra.Unit75.Tor
      ((ModuleCat.restrictScalars g).obj (ModuleCat.of B' B'))
      (ModuleCat.of B (B ⧸ I)) 1)

def EnvelopeFlatBaseChangeHypotheses
    (A : DividedPowerRing.{u}) {B B' : Type u}
    [CommRing B] [CommRing B'] (f : (A : Type u) →+* B)
    (g : B →+* B') : Prop :=
  RingHom.Flat
      (quotientBaseChangeMap g (envelopeBaseIdeal A f)
        (envelopeBaseIdeal A (g.comp f))
        (envelopeBaseIdeal_map_le A f g)) ∧
    envelopeTorOneVanishing g (envelopeBaseIdeal A f)

/-- Flatness of an algebra map at every prime in the closed subset defined by
an ideal of the target. -/
def FlatAtBaseIdealLocus {B B' : Type u} [CommRing B] [CommRing B']
    (g : B →+* B') (I' : Ideal B') : Prop :=
  ∀ (p : Ideal B') [p.IsPrime], I' ≤ p →
    RingHom.Flat (Localization.localRingHom (p.comap g) p g rfl)

/-- The local-flatness condition mentioned in the source implies the two
hypotheses used for envelope base change. -/
theorem envelopeFlatBaseChangeHypotheses_of_flatAtBaseIdealLocus
    (A : DividedPowerRing.{u}) {B B' : Type u}
    [CommRing B] [CommRing B'] (f : (A : Type u) →+* B)
    (g : B →+* B')
    (hflat : FlatAtBaseIdealLocus g
      (envelopeBaseIdeal A (g.comp f))) :
    EnvelopeFlatBaseChangeHypotheses A f g := by
  sorry

theorem flat_base_change_dividedPowerEnvelope
    (A : DividedPowerRing.{u}) {B B' : Type u}
    [CommRing B] [CommRing B'] (f : (A : Type u) →+* B)
    (g : B →+* B') (J : Ideal B)
    (hIJ : envelopeBaseIdeal A f ≤ J)
    (hbase : EnvelopeFlatBaseChangeHypotheses A f g) :
    Nonempty (RingEquiv
      ((envelopeTensorBaseChangeRing
        (dividedPowerEnvelope A f J hIJ) g) : Type u)
      ((baseChangedEnvelope A f g J hIJ).D : Type u)) := by
  sorry

/-- The localization instance of flat base change. -/
theorem dividedPowerEnvelope_localization
    (A : DividedPowerRing.{u}) {B : Type u} [CommRing B]
    (f : (A : Type u) →+* B) (J : Ideal B)
    (hIJ : envelopeBaseIdeal A f ≤ J) (S : Submonoid B)
    (hbase : EnvelopeFlatBaseChangeHypotheses A f
      (algebraMap B (Localization S))) :
    Nonempty (RingEquiv
      ((envelopeTensorBaseChangeRing
        (dividedPowerEnvelope A f J hIJ)
        (algebraMap B (Localization S))) : Type u)
      ((baseChangedEnvelope A f (algebraMap B (Localization S)) J hIJ).D :
        Type u)) := by
  sorry

def dividedPowerRingQuotientMap
    (A B : DividedPowerRing.{u}) (p : DividedPowerRing.Hom A B) :
    (A : Type u) ⧸ A.ideal →+* (B : Type u) ⧸ B.ideal :=
  quotientBaseChangeMap p.hom A.ideal B.ideal (by
    rw [Ideal.map_le_iff_le_comap]
    intro x hx
    exact p.ideal_map hx)

def FlatDividedPowerEnvelopeExtension
    (A B : DividedPowerRing.{u}) (p : DividedPowerRing.Hom A B)
    (J : Ideal (A : Type u)) (J' : Ideal (B : Type u)) : Prop :=
  A.ideal ≤ J ∧ B.ideal ≤ J' ∧
    RingHom.Flat (dividedPowerRingQuotientMap A B p) ∧
    J' = Ideal.map p.hom J ⊔ B.ideal

theorem flat_extension_dividedPowerEnvelope
    (A B : DividedPowerRing.{u}) (p : DividedPowerRing.Hom A B)
    (J : Ideal (A : Type u)) (J' : Ideal (B : Type u))
    (h : FlatDividedPowerEnvelopeExtension A B p J J') :
    Nonempty (RingEquiv
      ((envelopeTensorBaseChangeRing
        (identityEnvelope A J h.1) p.hom) : Type u)
      ((identityEnvelope B J' h.2.1).D : Type u)) := by
  sorry

end
end Formalization.Books.Crystalline.Unit02
