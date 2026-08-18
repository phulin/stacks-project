import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.RingHom.Flat
import Formalization.Books.Algebra.Unit14.BaseChange
import Formalization.Books.Algebra.Unit75.TorGroups
import Formalization.Books.MoreAlgebra.Unit59.DerivedTensorProduct

/-!
# More on Algebra, Chapter 61: Tor independence

This file records the comparison-map, flat base-change, derived-cohomology,
and localization interfaces used in the source section.  The preceding
formalization provides the canonical resolution-based `Tor` construction and
the derived tensor product over a fixed ring.  Cross-ring derived base change
and the canonical `A ⊗ R B`-action on `Tor` are kept as explicit interfaces:
those constructions are the subject of the intervening change-of-rings
material, which is not yet present in the earlier chapter files.
-/

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open Formalization.Books.Algebra.Unit75
open Formalization.Books.MoreAlgebra.Unit56
open scoped TensorProduct

universe u w

namespace Formalization.Books.MoreAlgebra.Unit61

abbrev Derived (R : Type u) [CommRing R]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)] :=
  Formalization.Books.MoreAlgebra.Unit56.D R

/-! ## Ring squares and the comparison map -/

/-- A commutative square of commutative rings.

The two maps from `R` to `A'` are recorded explicitly because the source
uses a square, rather than silently identifying one of them with an
`algebraMap`. -/
structure RingSquare (R A R' A' : Type u)
    [CommRing R] [CommRing A] [CommRing R'] [CommRing A'] where
  rToA : R →+* A
  rToR' : R →+* R'
  aToA' : A →+* A'
  r'ToA' : R' →+* A'
  commutes : aToA'.comp rToA = r'ToA'.comp rToR'

/-- The canonical ring maps in the base-change square
`R → A`, `R → R'`, `A → A ⊗[R] R'`, `R' → A ⊗[R] R'`. -/
noncomputable def baseChangeRingSquare
    {R A R' : Type u} [CommRing R] [CommRing A] [CommRing R']
    (f : R →+* A) (g : R →+* R') :
    letI : Algebra R A := f.toAlgebra
    letI : Algebra R R' := g.toAlgebra
    RingSquare R A R' (A ⊗[R] R') := by
  letI : Algebra R A := f.toAlgebra
  letI : Algebra R R' := g.toAlgebra
  exact
    { rToA := f
      rToR' := g
      aToA' := Formalization.Books.Algebra.Unit14.baseChangeAlgebraMap f g
      r'ToA' := Formalization.Books.Algebra.Unit14.baseChangeRingMap f g
      commutes := by
        ext x
        rw [← RingHom.algebraMap_toAlgebra f, ← RingHom.algebraMap_toAlgebra g]
        exact Algebra.TensorProduct.tmul_one_eq_one_tmul x }

/-- The derived base-change data attached to a ring square.

The natural transformation is the source's functorial comparison map
`K ⊗ᴸ_R R' ⟶ K ⊗ᴸ_A A'`, with both sides regarded as objects of `D(R')`.
This is an explicit interface because the earlier files do not yet expose
the cross-ring derived scalar-change functors. -/
structure DerivedRingSquare
    {R A R' A' : Type u} [CommRing R] [CommRing A] [CommRing R'] [CommRing A']
    [HasDerivedCategory.{w} (ModuleCat.{u} R)]
    [HasDerivedCategory.{w} (ModuleCat.{u} A)]
    [HasDerivedCategory.{w} (ModuleCat.{u} R')]
    [HasDerivedCategory.{w} (ModuleCat.{u} A')] (S : RingSquare R A R' A') where
  restrictToR : Derived A ⥤ Derived R
  changeR : Derived R ⥤ Derived R'
  changeA : Derived A ⥤ Derived A'
  restrictToR' : Derived A' ⥤ Derived R'
  comparison : (restrictToR ⋙ changeR) ⟶ (changeA ⋙ restrictToR')

/-- The comparison morphism at a derived object. -/
noncomputable def comparisonMap
    {R A R' A' : Type u} [CommRing R] [CommRing A] [CommRing R'] [CommRing A']
    [HasDerivedCategory.{w} (ModuleCat.{u} R)]
    [HasDerivedCategory.{w} (ModuleCat.{u} A)]
    [HasDerivedCategory.{w} (ModuleCat.{u} R')]
    [HasDerivedCategory.{w} (ModuleCat.{u} A')]
    {S : RingSquare R A R' A'} (D : DerivedRingSquare S) (K : Derived A) :
    ((D.restrictToR ⋙ D.changeR).obj K ⟶
      (D.changeA ⋙ D.restrictToR').obj K) :=
  D.comparison.app K

/-- In the base-change case, ordinary tensoring over `R` and over `A` are
the same extension-of-scalars functor, up to the canonical isomorphism. -/
theorem ordinaryTensor_baseChange
    {R A R' : Type u} [CommRing R] [CommRing A] [CommRing R']
    (f : R →+* A) (g : R →+* R') (M : ModuleCat A) :
    letI : Algebra R A := f.toAlgebra
    letI : Algebra R R' := g.toAlgebra
    Nonempty
      (((ModuleCat.extendScalars
          (Formalization.Books.Algebra.Unit14.baseChangeAlgebraMap f g)).obj M) ≅
        (ModuleCat.extendScalars
          (Formalization.Books.Algebra.Unit14.baseChangeRingMap f g)).obj
          ((ModuleCat.extendScalars g).obj
            ((ModuleCat.restrictScalars f).obj M))) := by
  sorry

/-! ## Tor independence -/

/-- `A` and `B` are Tor independent over the `R`-algebra structures. -/
def TorIndependent (R A B : Type u)
    [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] : Prop :=
  ∀ p : ℕ, 0 < p → IsZero (Tor (ModuleCat.of R A) (ModuleCat.of R B) p)

/-- Tor independence with the two structure maps supplied explicitly. -/
def TorIndependentVia {R A B : Type u}
    [CommRing R] [CommRing A] [CommRing B]
    (f : R →+* A) (g : R →+* B) : Prop :=
  letI : Algebra R A := f.toAlgebra
  letI : Algebra R B := g.toAlgebra
  TorIndependent R A B

/-- The vanishing condition in the definition, exposed for clients that
want to work directly with the canonical resolution-based Tor objects. -/
theorem torIndependent_iff
    (R A B : Type u) [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] :
    TorIndependent R A B ↔
      ∀ p : ℕ, 0 < p → IsZero (Tor (ModuleCat.of R A) (ModuleCat.of R B) p) := by
  rfl

/-- The polynomial quotient example from the source. -/
noncomputable abbrev polynomialAtZero (k : Type u) [Field k] : Type u :=
  Polynomial k ⧸ Ideal.span ({Polynomial.X} : Set (Polynomial k))

/-- The quotient map `k[x] → k[x]/(x)`. -/
noncomputable def polynomialAtZeroMap (k : Type u) [Field k] :
    Polynomial k →+* polynomialAtZero k :=
  Ideal.Quotient.mk _

/-- The source's example has nonzero positive Tor, so its comparison map is
not an isomorphism in general. -/
theorem polynomialAtZero_not_torIndependent
    (k : Type u) [Field k] :
    letI : Algebra (Polynomial k) (polynomialAtZero k) :=
      (polynomialAtZeroMap k).toAlgebra
    ¬ TorIndependent (Polynomial k) (polynomialAtZero k) (polynomialAtZero k) := by
  sorry

/-- Under the base-change identification `A' = A ⊗[R] R'`, Tor independence
of `A` and `R'` makes the derived comparison map an isomorphism. -/
theorem comparisonMap_isIso_of_torIndependent
    {R A R' A' : Type u} [CommRing R] [CommRing A] [CommRing R'] [CommRing A']
    [Algebra R A] [Algebra R R']
    [HasDerivedCategory.{w} (ModuleCat.{u} R)]
    [HasDerivedCategory.{w} (ModuleCat.{u} A)]
    [HasDerivedCategory.{w} (ModuleCat.{u} R')]
    [HasDerivedCategory.{w} (ModuleCat.{u} A')]
    {S : RingSquare R A R' A'} (d : DerivedRingSquare S)
    (hbase : A' = A ⊗[R] R') (hTor : TorIndependent R A R')
    (K : Derived A) :
    IsIso (comparisonMap d K) := by
  sorry

/-! ## Flat base change for Tor -/

/-- The canonical `A ⊗[R] B`-module model of a Tor group, together with
its underlying `R`-module identification.  Mathlib's resolution-based Tor
object currently exposes only the latter, so the action is an explicit
interface here. -/
structure TorTensorModule
    (R A B : Type u) [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B]
    (rToTensor : R →+* (A ⊗[R] B)) where
  object : ℕ → ModuleCat (A ⊗[R] B)
  underlyingTor : ∀ i,
    Nonempty ((ModuleCat.restrictScalars rToTensor).obj (object i) ≅
      Tor (ModuleCat.of R A) (ModuleCat.of R B) i)

/-- The flat base-change formula, stated using the canonical tensor-module
models of the two Tor systems. -/
theorem tor_flat_baseChange
    {R A B R' A' B' : Type u}
    [CommRing R] [CommRing A] [CommRing B] [CommRing R'] [CommRing A'] [CommRing B']
    [Algebra R A] [Algebra R B] [Algebra R R']
    [Algebra R' A'] [Algebra R' B']
    (g : R →+* R')
    (aBase : A ⊗[R] R' →+* A') (bBase : R' ⊗[R] B →+* B')
    (baseMap : (A ⊗[R] B) →+* (A' ⊗[R'] B'))
    (hR : RingHom.Flat g) (hA : RingHom.Flat aBase) (hB : RingHom.Flat bBase)
    (rToTensor : R →+* (A ⊗[R] B))
    (rPrimeToTensor : R' →+* (A' ⊗[R'] B'))
    (T : TorTensorModule R A B rToTensor)
    (T' : TorTensorModule R' A' B' rPrimeToTensor)
    (i : ℕ) :
    Nonempty ((ModuleCat.extendScalars baseMap).obj (T.object i) ≅ T'.object i) := by
  sorry

/-- Flat base change preserves Tor independence. -/
theorem torIndependent_flat_baseChange
    {R A B R' : Type u} [CommRing R] [CommRing A] [CommRing B] [CommRing R']
    (f : R →+* A) (h : R →+* B) (g : R →+* R')
    (hflat : RingHom.Flat g)
    (hTor : TorIndependentVia f h) :
    TorIndependentVia
      (Formalization.Books.Algebra.Unit14.baseChangeRingMap f g)
      (Formalization.Books.Algebra.Unit14.baseChangeRingMap h g) := by
  sorry

/-! ## Derived cohomology after flat base change -/

/-- Cross-ring derived tensor products and their natural module structures,
packaged at the cohomology level used by the source's comparison lemma. -/
structure DerivedCohomologyBaseChange
    {R A B R' A' B' : Type u}
    [CommRing R] [CommRing A] [CommRing B] [CommRing R'] [CommRing A'] [CommRing B']
    [Algebra R A] [Algebra R B] [Algebra R R']
    [Algebra R' A'] [Algebra R' B']
    [HasDerivedCategory.{w} (ModuleCat.{u} A)]
    [HasDerivedCategory.{w} (ModuleCat.{u} B)]
    [HasDerivedCategory.{w} (ModuleCat.{u} B')] where
  left : ℤ → Derived A ⥤ ModuleCat.{u} (A' ⊗[R'] B')
  right : ℤ → Derived A ⥤ ModuleCat.{u} (A' ⊗[R'] B')

/-- The source's canonical cohomology isomorphism after flat base change. -/
theorem derivedCohomology_flat_baseChange
    {R A B R' A' B' : Type u}
    [CommRing R] [CommRing A] [CommRing B] [CommRing R'] [CommRing A'] [CommRing B']
    [Algebra R A] [Algebra R B] [Algebra R R']
    [Algebra R' A'] [Algebra R' B']
    [HasDerivedCategory.{w} (ModuleCat.{u} A)]
    [HasDerivedCategory.{w} (ModuleCat.{u} B)]
    [HasDerivedCategory.{w} (ModuleCat.{u} B')]
    (g : R →+* R')
    (aBase : A ⊗[R] R' →+* A') (bBase : R' ⊗[R] B →+* B')
    (hR : RingHom.Flat g) (hA : RingHom.Flat aBase) (hB : RingHom.Flat bBase)
    (C : DerivedCohomologyBaseChange (R := R) (A := A) (B := B)
      (R' := R') (A' := A') (B' := B'))
    (i : ℤ) (M : Derived A) :
    Nonempty ((C.left i).obj M ≅ (C.right i).obj M) := by
  sorry

/-! ## Localization criterion -/

/-- A pair of primes of `A` and `B` lying over the same prime of `R`, with
the induced maps between the corresponding local rings made explicit. -/
structure LocalPrimePair
    (R A B : Type u) [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] where
  p : PrimeSpectrum A
  q : PrimeSpectrum B
  r : PrimeSpectrum R
  pOver : PrimeSpectrum.comap (algebraMap R A) p = r
  qOver : PrimeSpectrum.comap (algebraMap R B) q = r
  rToAp : Localization.AtPrime r.asIdeal →+* Localization.AtPrime p.asIdeal
  rToBq : Localization.AtPrime r.asIdeal →+* Localization.AtPrime q.asIdeal

/-- The localized Tor-independence predicate for a local prime pair. -/
def LocalPrimePair.TorIndependent
    {R A B : Type u} [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] (P : LocalPrimePair R A B) : Prop :=
  TorIndependentVia P.rToAp P.rToBq

/-- The localized form of the source's comparison identity, with the two
localization maps and the equality of the resulting Tor objects exposed as
a named interface. -/
structure LocalizedTorIdentity
    {R A B : Type u} [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] (P : LocalPrimePair R A B) where
  localized : ℕ → ModuleCat (Localization.AtPrime P.r.asIdeal)
  globalToLocalized : ∀ i,
    letI : Algebra (Localization.AtPrime P.r.asIdeal)
        (Localization.AtPrime P.p.asIdeal) := P.rToAp.toAlgebra
    letI : Algebra (Localization.AtPrime P.r.asIdeal)
        (Localization.AtPrime P.q.asIdeal) := P.rToBq.toAlgebra
    Nonempty (localized i ≅
      Tor (ModuleCat.of (Localization.AtPrime P.r.asIdeal)
          (Localization.AtPrime P.p.asIdeal))
        (ModuleCat.of (Localization.AtPrime P.r.asIdeal)
          (Localization.AtPrime P.q.asIdeal)) i)

/-- Tor independence is equivalent to Tor independence after localization at
corresponding primes. -/
theorem torIndependent_iff_localPrimePairs
    {R A B : Type u} [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] :
    TorIndependent R A B ↔
      ∀ P : LocalPrimePair R A B, P.TorIndependent := by
  sorry

/-- The prime-localized Tor identity used in the third formulation of the
source lemma. -/
theorem tor_localization_identity
    {R A B : Type u} [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] (P : LocalPrimePair R A B) :
    Nonempty (LocalizedTorIdentity P) := by
  sorry

/-- A chosen localized Tor object supplied by the localization identity. -/
noncomputable def localizedTor
    {R A B : Type u} [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] (P : LocalPrimePair R A B) (i : ℕ) :
    ModuleCat (Localization.AtPrime P.r.asIdeal) :=
  (Classical.choice (tor_localization_identity P)).localized i

/-- Vanishing of all prime-localized Tor modules is equivalent to Tor
independence. -/
theorem torIndependent_iff_localizedTor_vanishing
    {R A B : Type u} [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] :
    TorIndependent R A B ↔
      ∀ P : LocalPrimePair R A B, ∀ i : ℕ,
        IsZero (localizedTor P i) := by
  sorry

end Formalization.Books.MoreAlgebra.Unit61
